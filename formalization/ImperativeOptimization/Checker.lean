/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic
import ImperativeOptimization.Language
import ImperativeOptimization.CheckerCore

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

The definitions (everything the checker program runs) are in `CheckerCore`, which does
not depend on mathlib; this file proves their properties.

The checker does not search: every implication it needs is given with its Farkas
multipliers and verified by comparing coefficients (`entails1`). An analyser, however
complex and unverified, only has to *emit* such a certificate.

Assertions may mention *logical variables* (a second valuation `ρ`), which programs
cannot modify; the loop rule uses one to state that the potential decreases.
-/

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
