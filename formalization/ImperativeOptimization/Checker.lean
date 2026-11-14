/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic
import ImperativeOptimization.Language

namespace ImperativeOptimization.Checker

/-!
# A verified checker for linear cost certificates

`Language` gives a cost logic over arbitrary states and predicates. This module fixes a
concrete, executable instance and a *checker*:

* states are valuations `ℕ → ℤ` of integer variables; expressions, guards, assertions
  and potentials are affine with integer coefficients (`PExp`, `Lin`);
* a certificate is a program annotated with assertions, bounds, loop invariants,
  potentials and Farkas multipliers (`ACmd`);
* `check P c B Q : Bool` decides, by structural recursion and integer arithmetic only,
  whether the annotations justify the triple `{P} c {Q}` with bound `B`;
* `check_sound`: if `check P c B Q = true` then the triple is valid in the sense of
  `Language.Valid`; `certified_cost_le` restates it: every execution of the program from
  a state satisfying `P`, terminated or not, costs at most `B`.

The checker does not search: every implication it needs is given with its Farkas
multipliers and verified by comparing coefficients (`entails1`). An analyser, however
complex and unverified, only has to *emit* such a certificate.

Assertions may mention *logical variables* (a second valuation `ρ`), which programs
cannot modify; the loop rule uses one to state that the potential decreases.
-/

/-- Valuations of variables. -/
abbrev Env := ℕ → ℤ

/-! ### Dense integer vectors -/

/-- `dot l f = Σᵢ l[i] * f i`. -/
def dot : List ℤ → Env → ℤ
  | [], _ => 0
  | a :: l, f => a * f 0 + dot l (fun i => f (i + 1))

/-- Componentwise sum, the shorter vector being padded with zeros. -/
def vadd : List ℤ → List ℤ → List ℤ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: vadd l m

/-- Multiplication by a scalar. -/
def vsmul (k : ℤ) (l : List ℤ) : List ℤ := l.map (k * ·)

/-- The `i`-th unit vector. -/
def unit : ℕ → List ℤ
  | 0 => [1]
  | i + 1 => 0 :: unit i

/-- The `i`-th coefficient (zero beyond the end). -/
def coeff (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

/-- All coefficients are zero. -/
def isZero (l : List ℤ) : Bool := l.all (fun a => decide (a = 0))

theorem dot_vadd (l m : List ℤ) (f : Env) : dot (vadd l m) f = dot l f + dot m f := by
  induction l generalizing m f with
  | nil => simp [vadd, dot]
  | cons a l ih =>
    cases m with
    | nil => simp [vadd, dot]
    | cons b m => simp only [vadd, dot, ih]; ring

theorem dot_vsmul (k : ℤ) (l : List ℤ) (f : Env) : dot (vsmul k l) f = k * dot l f := by
  induction l generalizing f with
  | nil => simp [vsmul, dot]
  | cons a l ih =>
    have := ih (fun i => f (i + 1))
    simp only [vsmul, List.map_cons, dot] at this ⊢
    rw [this]; ring

theorem dot_unit (i : ℕ) (f : Env) : dot (unit i) f = f i := by
  induction i generalizing f with
  | zero => simp [unit, dot]
  | succ i ih => simp [unit, dot, ih]

theorem dot_isZero {l : List ℤ} (h : isZero l = true) (f : Env) : dot l f = 0 := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [isZero, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [dot, h.1, ih (by simpa [isZero] using h.2)]

theorem dot_update (l : List ℤ) (f : Env) (i : ℕ) (v : ℤ) :
    dot l (Function.update f i v) = dot l f + coeff l i * (v - f i) := by
  induction l generalizing f i with
  | nil => simp [dot, coeff]
  | cons a l ih =>
    cases i with
    | zero =>
      have h : (fun j => Function.update f 0 v (j + 1)) = fun j => f (j + 1) := by
        funext j; simp [Function.update]
      simp only [dot, h, coeff, List.getD_cons_zero]
      simp; ring
    | succ i =>
      have h : (fun j => Function.update f (i + 1) v (j + 1)) =
          Function.update (fun j => f (j + 1)) i v := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update, hj]
      have h0 : Function.update f (i + 1) v 0 = f 0 := by simp [Function.update]
      simp only [dot, h, h0, ih, coeff, List.getD_cons_succ]; ring

/-! ### Affine expressions and assertions -/

/-- A program expression `Σ sv[i] * xᵢ + c` over the program variables. -/
structure PExp where
  sv : List ℤ
  c : ℤ
  deriving DecidableEq, Repr

/-- An affine form over program variables (`sv`) and logical variables (`lv`). As a
    constraint it means `eval ≤ 0`. -/
structure Lin where
  sv : List ℤ
  lv : List ℤ
  c : ℤ
  deriving DecidableEq, Repr

def PExp.eval (a : PExp) (s : Env) : ℤ := dot a.sv s + a.c

def Lin.eval (e : Lin) (ρ s : Env) : ℤ := dot e.sv s + dot e.lv ρ + e.c

/-- The guard `a ≤ 0` as a constraint. -/
def PExp.toLin (a : PExp) : Lin := ⟨a.sv, [], a.c⟩

/-- The negation of the guard `a ≤ 0` over the integers: `1 - a ≤ 0`. -/
def PExp.negLin (a : PExp) : Lin := ⟨vsmul (-1) a.sv, [], 1 - a.c⟩

def Lin.add (e f : Lin) : Lin := ⟨vadd e.sv f.sv, vadd e.lv f.lv, e.c + f.c⟩

def Lin.smul (k : ℤ) (e : Lin) : Lin := ⟨vsmul k e.sv, vsmul k e.lv, k * e.c⟩

/-- Substitution of the expression `a` for the program variable `x`. -/
def Lin.subst (e : Lin) (x : ℕ) (a : PExp) : Lin :=
  let k := coeff e.sv x
  ⟨vadd e.sv (vsmul k (vadd a.sv (vsmul (-1) (unit x)))), e.lv, e.c + k * a.c⟩

/-- An assertion is a conjunction of constraints. -/
def holds (A : List Lin) (ρ s : Env) : Prop := ∀ e ∈ A, e.eval ρ s ≤ 0

@[simp] theorem holds_cons (e : Lin) (A : List Lin) (ρ s : Env) :
    holds (e :: A) ρ s ↔ e.eval ρ s ≤ 0 ∧ holds A ρ s := by
  simp [holds]

theorem PExp.toLin_eval (a : PExp) (ρ s : Env) : a.toLin.eval ρ s = a.eval s := by
  simp [PExp.toLin, Lin.eval, PExp.eval, dot]

theorem PExp.negLin_eval (a : PExp) (ρ s : Env) : a.negLin.eval ρ s = 1 - a.eval s := by
  simp [PExp.negLin, Lin.eval, PExp.eval, dot, dot_vsmul]; ring

theorem Lin.add_eval (e f : Lin) (ρ s : Env) : (e.add f).eval ρ s = e.eval ρ s + f.eval ρ s := by
  simp [Lin.add, Lin.eval, dot_vadd]; ring

theorem Lin.smul_eval (k : ℤ) (e : Lin) (ρ s : Env) : (e.smul k).eval ρ s = k * e.eval ρ s := by
  simp [Lin.smul, Lin.eval, dot_vsmul]; ring

theorem Lin.subst_eval (e : Lin) (x : ℕ) (a : PExp) (ρ s : Env) :
    (e.subst x a).eval ρ s = e.eval ρ (Function.update s x (a.eval s)) := by
  simp only [Lin.subst, Lin.eval, PExp.eval, dot_vadd, dot_vsmul, dot_unit, dot_update]
  ring

/-- Changing a program variable changes the value by its coefficient. -/
theorem Lin.eval_update (e : Lin) (ρ s : Env) (x : ℕ) (v : ℤ) :
    e.eval ρ (Function.update s x v) = e.eval ρ s + coeff e.sv x * (v - s x) := by
  simp only [Lin.eval, dot_update]; ring

/-- Changing a logical variable changes the value by its coefficient. -/
theorem Lin.eval_update_logical (e : Lin) (ρ s : Env) (j : ℕ) (v : ℤ) :
    e.eval (Function.update ρ j v) s = e.eval ρ s + coeff e.lv j * (v - ρ j) := by
  simp only [Lin.eval, dot_update]; ring

/-! ### Farkas certificates -/

/-- `Σᵢ lam[i] • ps[i]` (the shorter list decides the length). -/
def comb : List ℕ → List Lin → Lin
  | [], _ => ⟨[], [], 0⟩
  | _ :: _, [] => ⟨[], [], 0⟩
  | k :: lam, p :: ps => (p.smul k).add (comb lam ps)

theorem comb_nonpos (lam : List ℕ) (ps : List Lin) (ρ s : Env) (h : holds ps ρ s) :
    (comb lam ps).eval ρ s ≤ 0 := by
  induction lam generalizing ps with
  | nil => simp [comb, Lin.eval, dot]
  | cons k lam ih =>
    cases ps with
    | nil => simp [comb, Lin.eval, dot]
    | cons p ps =>
      rw [holds_cons] at h
      have h1 := ih ps h.2
      have h2 : (k : ℤ) * p.eval ρ s ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg k) h.1
      simp only [comb, Lin.add_eval, Lin.smul_eval]
      linarith

/-- A Farkas certificate `(mu, lam)` for `ps ⊢ g`: `mu > 0` and
    `mu • g - Σ lam[i] • ps[i]` is a non-positive constant. -/
def entails1 (ps : List Lin) (g : Lin) (cert : ℕ × List ℕ) : Bool :=
  let r := (g.smul cert.1).add ((comb cert.2 ps).smul (-1))
  decide (0 < cert.1) && isZero r.sv && isZero r.lv && decide (r.c ≤ 0)

theorem entails1_sound {ps : List Lin} {g : Lin} {cert : ℕ × List ℕ}
    (h : entails1 ps g cert = true) {ρ s : Env} (hps : holds ps ρ s) : g.eval ρ s ≤ 0 := by
  simp only [entails1, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hmu, hsv⟩, hlv⟩, hc⟩ := h
  have hr : ((g.smul cert.1).add ((comb cert.2 ps).smul (-1))).eval ρ s ≤ 0 := by
    simp only [Lin.eval, dot_isZero hsv, dot_isZero hlv]
    linarith
  rw [Lin.add_eval, Lin.smul_eval, Lin.smul_eval] at hr
  have hcomb := comb_nonpos cert.2 ps ρ s hps
  have hmu' : (0 : ℤ) < cert.1 := by exact_mod_cast hmu
  by_contra hg
  push_neg at hg
  have := mul_pos hmu' hg
  linarith

/-- One certificate per goal. -/
def entailsAll (ps : List Lin) : List Lin → List (ℕ × List ℕ) → Bool
  | [], [] => true
  | g :: gs, cert :: certs => entails1 ps g cert && entailsAll ps gs certs
  | _, _ => false

theorem entailsAll_sound {ps gs : List Lin} {certs : List (ℕ × List ℕ)}
    (h : entailsAll ps gs certs = true) {ρ s : Env} (hps : holds ps ρ s) : holds gs ρ s := by
  induction gs generalizing certs with
  | nil => intro e he; cases he
  | cons g gs ih =>
    cases certs with
    | nil => simp [entailsAll] at h
    | cons cert certs =>
      simp only [entailsAll, Bool.and_eq_true] at h
      rw [holds_cons]
      exact ⟨entails1_sound h.1 hps, ih h.2⟩

/-! ### Certificates -/

/-- An annotated program: the program together with everything the checker needs. -/
inductive ACmd where
  | skip : ACmd
  /-- `x := a`, at cost `w`. -/
  | assign (w : ℕ) (x : ℕ) (a : PExp) : ACmd
  /-- `x := ?` (an unknown value), at cost `w`. -/
  | havoc (w : ℕ) (x : ℕ) : ACmd
  /-- `c₁ ; c₂` with the intermediate assertion and the two bounds. -/
  | seq (c₁ : ACmd) (mid : List Lin) (B₁ B₂ : ℕ) (c₂ : ACmd) : ACmd
  /-- `if (g ≤ 0) c₁ else c₂`, the test costing `w`, with the bounds of the branches. -/
  | ite (w : ℕ) (g : PExp) (B₁ B₂ : ℕ) (c₁ c₂ : ACmd) : ACmd
  /-- `while (g ≤ 0) body`, the test costing `w`, with: the invariant `inv`; the
      potential `pot / d`; an upper bound `k` of `pot` on entry; a logical variable `j`
      not used by `inv`; the Farkas certificate of `inv ∧ g ⊢ pot ≥ d`; the bound `Wb` of
      the body. -/
  | while (w : ℕ) (g : PExp) (inv : List Lin) (pot : PExp) (d : ℕ) (k : ℤ) (j : ℕ)
      (posCert : ℕ × List ℕ) (Wb : ℕ) (body : ACmd) : ACmd
  /-- Consequence: `c` is checked against `P'`, `B'`, `Q'`, and the surrounding triple
      follows by the given Farkas certificates. -/
  | weaken (P' : List Lin) (preCerts : List (ℕ × List ℕ)) (B' : ℕ) (Q' : List Lin)
      (postCerts : List (ℕ × List ℕ)) (c : ACmd) : ACmd
  /-- Dead code: the precondition is contradictory, by the given certificate. -/
  | dead (cert : ℕ × List ℕ) (c : ACmd) : ACmd

/-- The program of a certificate, as a command of `Language` over valuations. -/
def ACmd.toCmd : ACmd → Cmd Empty Env
  | .skip => Cmd.skip
  | .assign w x a => Cmd.atom w (fun s t => t = Function.update s x (a.eval s))
  | .havoc w x => Cmd.atom w (fun s t => ∃ v, t = Function.update s x v)
  | .seq c₁ _ _ _ c₂ => Cmd.seq c₁.toCmd c₂.toCmd
  | .ite w g _ _ c₁ c₂ => Cmd.ite w (fun s => decide (g.eval s ≤ 0)) c₁.toCmd c₂.toCmd
  | .while w g _ _ _ _ _ _ _ body => Cmd.while w (fun s => decide (g.eval s ≤ 0)) body.toCmd
  | .weaken _ _ _ _ _ c => c.toCmd
  | .dead _ c => c.toCmd

/-- `pot - γⱼ + extra ≤ 0`, where `γⱼ` is the logical variable `j`. -/
def ghost (pot : PExp) (j : ℕ) (extra : ℤ) : Lin :=
  ⟨pot.sv, vsmul (-1) (unit j), pot.c + extra⟩

/-- **The checker.** -/
def check (P : List Lin) : ACmd → ℕ → List Lin → Bool
  | .skip, B, Q => decide (P = Q) && decide (B = 0)
  | .assign w x a, B, Q => decide (P = Q.map (fun e => e.subst x a)) && decide (B = w)
  | .havoc w x, B, Q =>
      decide (P = Q) && Q.all (fun e => decide (coeff e.sv x = 0)) && decide (B = w)
  | .seq c₁ mid B₁ B₂ c₂, B, Q =>
      check P c₁ B₁ mid && check mid c₂ B₂ Q && decide (B = B₁ + B₂)
  | .ite w g B₁ B₂ c₁ c₂, B, Q =>
      check (g.toLin :: P) c₁ B₁ Q && check (g.negLin :: P) c₂ B₂ Q &&
        decide (B = w + max B₁ B₂)
  | .while w g inv pot d k j posCert Wb body, B, Q =>
      decide (0 < d) &&
      decide (P = ⟨pot.sv, [], pot.c - k⟩ :: inv) &&
      decide (Q = g.negLin :: inv) &&
      inv.all (fun e => decide (coeff e.lv j = 0)) &&
      entails1 (g.toLin :: inv) ⟨vsmul (-1) pot.sv, [], d - pot.c⟩ posCert &&
      check (ghost pot j 0 :: g.toLin :: inv) body Wb (ghost pot j d :: inv) &&
      decide (B = (k / d).toNat * (w + Wb) + w)
  | .weaken P' preCerts B' Q' postCerts c, B, Q =>
      entailsAll P P' preCerts && check P' c B' Q' && decide (B' ≤ B) &&
        entailsAll Q' Q postCerts
  | .dead cert _, _, _ => entails1 P ⟨[], [], 1⟩ cert

/-- The environment of a program without procedures. -/
abbrev Φ₀ : Empty → Cmd Empty Env := noProcs

theorem ghost_eval (pot : PExp) (j : ℕ) (extra : ℤ) (ρ s : Env) :
    (ghost pot j extra).eval ρ s = pot.eval s - ρ j + extra := by
  simp only [ghost, Lin.eval, PExp.eval, dot_vsmul, dot_unit]; ring

theorem holds_update_logical {A : List Lin} {j : ℕ}
    (h : A.all (fun e => decide (coeff e.lv j = 0)) = true) (ρ s : Env) (v : ℤ) :
    holds A (Function.update ρ j v) s ↔ holds A ρ s := by
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  constructor
  · intro H e he
    have := H e he
    rwa [Lin.eval_update_logical, h e he, zero_mul, add_zero] at this
  · intro H e he
    rw [Lin.eval_update_logical, h e he, zero_mul, add_zero]
    exact H e he

theorem floor_div (k : ℤ) (d : ℕ) : ⌊(k : ℚ) / (d : ℚ)⌋₊ = (k / (d : ℤ)).toNat := by
  rw [← Int.floor_toNat, Rat.floor_intCast_div_natCast]

/-- **Soundness of the checker.** A certificate accepted by `check` proves its triple:
    for every valuation `ρ` of the logical variables, from every state satisfying `P`,
    every execution prefix of the program costs at most `B` and every terminating
    execution ends in `Q`. -/
theorem check_sound (c : ACmd) : ∀ (P Q : List Lin) (B : ℕ), check P c B Q = true →
    ∀ ρ, Valid Φ₀ (holds P ρ) c.toCmd B (holds Q ρ) := by
  induction c with
  | skip =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact valid_skip _
  | assign w x a =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine valid_atom _ _ _ _ ?_
    rintro s t hP rfl e he
    have := hP (e.subst x a) (List.mem_map_of_mem _ he)
    rwa [Lin.subst_eval] at this
  | havoc w x =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨rfl, hx⟩, rfl⟩ := h
    refine valid_atom _ _ _ _ ?_
    rintro s t hP ⟨v, rfl⟩ e he
    rw [Lin.eval_update, hx e he, zero_mul, add_zero]
    exact hP e he
  | seq c₁ mid B₁ B₂ c₂ ih₁ ih₂ =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h₁, h₂⟩, rfl⟩ := h
    exact valid_seq (ih₁ _ _ _ h₁ ρ) (ih₂ _ _ _ h₂ ρ)
  | ite w g B₁ B₂ c₁ c₂ ih₁ ih₂ =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h₁, h₂⟩, rfl⟩ := h
    refine valid_ite ?_ ?_
    · refine valid_conseq ?_ (ih₁ _ _ _ h₁ ρ) (le_refl _) (fun _ hq => hq)
      rintro s ⟨hP, hb⟩
      rw [holds_cons, PExp.toLin_eval]
      exact ⟨by simpa using hb, hP⟩
    · refine valid_conseq ?_ (ih₂ _ _ _ h₂ ρ) (le_refl _) (fun _ hq => hq)
      rintro s ⟨hP, hb⟩
      rw [holds_cons, PExp.negLin_eval]
      have : 0 < g.eval s := by simpa using hb
      exact ⟨by omega, hP⟩
  | «while» w g inv pot d k j posCert Wb body ih =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hd, rfl⟩, rfl⟩, hinv⟩, hpos⟩, hbody⟩, rfl⟩ := h
    have hd' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
    have key := valid_while (Φ := Φ₀) (I := holds inv ρ) (C := fun s => pot.eval s ≤ k)
      (w := w) (b := fun s => decide (g.eval s ≤ 0)) (c := body.toCmd) (Wb := Wb)
      (fun s => (pot.eval s : ℚ) / d) ((k : ℚ) / d) ?_ ?_ ?_
    · refine valid_conseq ?_ key (le_of_eq ?_) ?_
      · intro s hP
        rw [holds_cons] at hP
        refine ⟨hP.2, ?_⟩
        have := hP.1
        simp only [Lin.eval, dot] at this
        simp only [PExp.eval]
        linarith
      · rw [floor_div]
      · rintro t ⟨hI, hb⟩
        rw [holds_cons, PExp.negLin_eval]
        have : 0 < g.eval t := by simpa using hb
        exact ⟨by omega, hI⟩
    · -- the body decreases the potential by `d` and preserves the invariant
      intro v s hs
      obtain ⟨hI, hb, hv⟩ := hs
      have hg : g.eval s ≤ 0 := by simpa using hb
      have H := ih _ _ _ hbody (Function.update ρ j (pot.eval s)) s (by
        rw [holds_cons, holds_cons, ghost_eval, PExp.toLin_eval, holds_update_logical hinv]
        exact ⟨by simp, hg, hI⟩)
      refine ⟨H.1, fun t n he => ?_⟩
      have ht := H.2 t n he
      rw [holds_cons, ghost_eval, holds_update_logical hinv] at ht
      refine ⟨ht.2, ?_⟩
      have h1 : pot.eval t + d ≤ pot.eval s := by
        have := ht.1
        simp at this
        linarith
      have h2 : ((pot.eval t : ℚ) + d) ≤ (pot.eval s : ℚ) := by exact_mod_cast h1
      rw [← hv, div_le_iff₀ hd', sub_mul, div_mul_cancel₀ _ (ne_of_gt hd')]
      linarith
    · -- the potential is at least `d` when the guard holds
      intro s hI hb
      have hg : g.eval s ≤ 0 := by simpa using hb
      have := entails1_sound hpos (ρ := ρ) (s := s) (by
        rw [holds_cons, PExp.toLin_eval]; exact ⟨hg, hI⟩)
      simp only [Lin.eval, dot, dot_vsmul] at this
      have h1 : (d : ℤ) ≤ pot.eval s := by simp only [PExp.eval]; linarith
      have h2 : (d : ℚ) ≤ (pot.eval s : ℚ) := by exact_mod_cast h1
      rw [le_div_iff₀ hd']
      linarith
    · intro s hs
      have h2 : (pot.eval s : ℚ) ≤ (k : ℚ) := by exact_mod_cast hs
      exact div_le_div_of_nonneg_right h2 (le_of_lt hd')
  | weaken P' preCerts B' Q' postCerts c ih =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hpre, hc⟩, hB⟩, hpost⟩ := h
    exact valid_conseq (fun s hs => entailsAll_sound hpre hs) (ih _ _ _ hc ρ) hB
      (fun t ht => entailsAll_sound hpost ht)
  | dead cert c _ =>
    intro P Q B h ρ
    simp only [check] at h
    refine valid_conseq (P := fun _ => False) ?_ (valid_unreachable _ B _) (le_refl _)
      (fun _ hq => hq)
    intro s hs
    have := entails1_sound h hs
    simp [Lin.eval, dot] at this

/-- **What an accepted certificate guarantees.** Every execution of the program from a
    state satisfying the precondition, terminated or not, costs at most `B`. -/
theorem certified_cost_le {P Q : List Lin} {c : ACmd} {B : ℕ} (h : check P c B Q = true)
    {ρ s : Env} (hP : holds P ρ s) {n : ℕ} (hp : Pre Φ₀ c.toCmd s n) : n ≤ B :=
  ((check_sound c P Q B h ρ) s hP).1 n hp

/-! ### An example certificate -/

/-- Variables: `x₀ = i`, `x₁ = n`. The program is `while (i < n) i := i + 1`, with unit
    weights; the guard `i < n` is `i - n + 1 ≤ 0`. Certificate: no invariant, potential
    `n - i` decreasing by `1`, at most `10` on entry. -/
def countCert : ACmd :=
  .weaken [⟨[-1, 1], [], -10⟩] [(1, [0, 1, 1])] 21 [⟨[-1, 1], [], 0⟩] [(1, [1])]
    (.while 1 ⟨[1, -1], 1⟩ [] ⟨[-1, 1], 0⟩ 1 10 0 (1, [1]) 1
      (.weaken [⟨[-1, 1], [-1], 0⟩] [(1, [1, 0])] 1 [⟨[-1, 1], [-1], 1⟩] [(1, [1])]
        (.assign 1 0 ⟨[1], 1⟩)))

/-- Precondition `i ≤ 0`, `-i ≤ 0`, `n - 10 ≤ 0`; postcondition `n - i ≤ 0`. -/
theorem countCert_checks :
    check [⟨[1], [], 0⟩, ⟨[-1], [], 0⟩, ⟨[0, 1], [], -10⟩] countCert 21 [⟨[-1, 1], [], 0⟩]
      = true := by
  decide

/-- Hence the loop costs at most `21` from `i = 0`, `n ≤ 10`, by the checker alone. -/
theorem countCert_cost (s : Env) (h0 : s 0 = 0) (h1 : s 1 ≤ 10) (n : ℕ)
    (hp : Pre Φ₀ countCert.toCmd s n) : n ≤ 21 := by
  refine certified_cost_le countCert_checks (ρ := fun _ => 0) ?_ hp
  intro e he
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp [Lin.eval, dot] <;> omega

end ImperativeOptimization.Checker
