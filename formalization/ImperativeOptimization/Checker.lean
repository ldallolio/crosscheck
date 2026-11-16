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

/-! ### Symbolic bounds -/

theorem dotN_nadd (l m : List ℕ) (f : Env) : dotN (nadd l m) f = dotN l f + dotN m f := by
  induction l generalizing m f with
  | nil => simp [nadd, dotN]
  | cons a l ih =>
    cases m with
    | nil => simp [nadd, dotN]
    | cons b m => simp only [nadd, dotN, ih]; ring

theorem dotN_nsmul (k : ℕ) (l : List ℕ) (f : Env) : dotN (nsmul k l) f = k * dotN l f := by
  induction l generalizing f with
  | nil => simp [nsmul, dotN]
  | cons a l ih =>
    have := ih (fun i => f (i + 1))
    simp only [nsmul, List.map_cons, dotN] at this ⊢
    rw [this]; ring

theorem dotN_nil_le (l : List ℕ) (h : nle l [] = true) (f : Env) : dotN l f = 0 := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [nle, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [dotN, h.1, ih h.2]

theorem nle_dotN {l m : List ℕ} (h : nle l m = true) (f : Env) : dotN l f ≤ dotN m f := by
  induction l generalizing m f with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    cases m with
    | nil =>
      have := dotN_nil_le (a :: l) h f
      simp [this]
    | cons b m =>
      simp only [nle, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [dotN]
      have := ih h.2 (fun i => f (i + 1))
      have : a * (f 0).toNat ≤ b * (f 0).toNat := Nat.mul_le_mul_right _ h.1
      omega

theorem dotN_zero {l : List ℕ} (h : l.all (· = 0) = true) (f : Env) : dotN l f = 0 := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [dotN, h.1, ih (by simpa using h.2)]

theorem dot_ofNat_zero {l : List ℕ} (h : l.all (· = 0) = true) (f : Env) :
    dot (l.map Int.ofNat) f = 0 := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [dot, h.1, ih (by simpa using h.2)]

/-- A natural-coefficient combination of values is at most the same combination of their
    positive parts. -/
theorem dot_ofNat_le (l : List ℕ) (f : Env) : dot (l.map Int.ofNat) f ≤ (dotN l f : ℤ) := by
  induction l generalizing f with
  | nil => simp [dot, dotN]
  | cons a l ih =>
    have := ih (fun i => f (i + 1))
    simp only [List.map_cons, dot, dotN]
    push_cast
    have h1 : (a : ℤ) * f 0 ≤ (a : ℤ) * ((f 0).toNat : ℤ) :=
      mul_le_mul_of_nonneg_left (Int.self_le_toNat (f 0)) (Int.natCast_nonneg a)
    have h2 : ((a : ℕ) : ℤ) = Int.ofNat a := rfl
    rw [← h2]
    linarith

theorem dotN_update {l : List ℕ} {j : ℕ} (h : ncoeff l j = 0) (f : Env) (v : ℤ) :
    dotN l (Function.update f j v) = dotN l f := by
  induction l generalizing f j with
  | nil => rfl
  | cons a l ih =>
    cases j with
    | zero =>
      have e : (fun i => Function.update f 0 v (i + 1)) = fun i => f (i + 1) := by
        funext i; simp [Function.update]
      simp only [ncoeff, List.getD_cons_zero] at h
      simp [dotN, e, h]
    | succ j =>
      have e : (fun i => Function.update f (j + 1) v (i + 1)) =
          Function.update (fun i => f (i + 1)) j v := by
        funext i
        by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update, hi]
      have h0 : Function.update f (j + 1) v 0 = f 0 := by simp [Function.update]
      simp only [ncoeff, List.getD_cons_succ] at h
      simp only [dotN, e, h0, ih h]

@[simp] theorem SB.eval_const (w : ℕ) (ρ : Env) : (SB.const w).eval ρ = w := by
  simp [SB.eval, SB.const, dotN]

@[simp] theorem SB.eval_add (a b : SB) (ρ : Env) : (a.add b).eval ρ = a.eval ρ + b.eval ρ := by
  simp only [SB.eval, SB.add, dotN_nadd]; ring

@[simp] theorem SB.eval_smul (k : ℕ) (a : SB) (ρ : Env) : (a.smul k).eval ρ = k * a.eval ρ := by
  simp only [SB.eval, SB.smul, dotN_nsmul]; ring

theorem SB.le_eval {a b : SB} (h : SB.le a b = true) (ρ : Env) : a.eval ρ ≤ b.eval ρ := by
  simp only [SB.le, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [SB.eval]
  have := nle_dotN h.2 ρ
  omega

/-- A combination of bounds bounds the same combination of values bounded by them. -/
theorem SB.comb_ge (ks : List ℕ) (bs : List SB) (ρ ρ' : Env) (hlen : ks.length ≤ bs.length)
    (hb : ∀ i, i < ks.length → (ρ' i).toNat ≤ (bs.getD i (SB.const 0)).eval ρ) :
    dotN ks ρ' ≤ (SB.comb ks bs).eval ρ := by
  induction ks generalizing bs ρ' with
  | nil => simp [dotN, SB.comb]
  | cons k ks ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons] at hlen
      have h0 := hb 0 (by simp)
      have hr := ih bs (fun i => ρ' (i + 1)) (by omega) (fun i hi => by
        have := hb (i + 1) (by simp; omega)
        simpa using this)
      simp only [dotN, SB.comb, SB.eval_add, SB.eval_smul]
      simp only [List.getD_cons_zero] at h0
      have : k * (ρ' 0).toNat ≤ k * b.eval ρ := Nat.mul_le_mul_left _ h0
      omega

/-- The loop bound required by `loopBoundOk` dominates the bound of the loop rule. -/
theorem loopBoundOk_sound {w d : ℕ} {k : ℤ} {kl : List ℕ} {Wb B : SB}
    (h : loopBoundOk w d k kl Wb B = true) (hd : 0 < d) (ρ : Env) :
    ((k + dot (kl.map Int.ofNat) ρ) / (d : ℤ)).toNat * (w + Wb.eval ρ) + w ≤ B.eval ρ := by
  simp only [loopBoundOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hkl, hle⟩ | ⟨⟨⟨hW, hw⟩, hk⟩, hco⟩
  · have := SB.le_eval hle ρ
    simp only [SB.eval_add, SB.eval_smul, SB.eval_const] at this
    rw [dot_ofNat_zero hkl, add_zero]
    exact this
  · have hWb : Wb.eval ρ = Wb.c := by simp [SB.eval, dotN_zero hW]
    rw [hWb]
    have hco' := nle_dotN hco ρ
    rw [dotN_nsmul, dotN_nsmul] at hco'
    have hD := dot_ofNat_le kl ρ
    set D := dot (kl.map Int.ofNat) ρ
    set N := ((k + D) / (d : ℤ)).toNat
    set W := w + Wb.c
    simp only [SB.eval]
    have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
    by_cases hK : k + D < 0
    · have : N = 0 := by
        simp only [N]
        have : (k + D) / (d : ℤ) < 0 := Int.ediv_neg' hK hdZ
        omega
      rw [this]; omega
    · push_neg at hK
      have hq : 0 ≤ (k + D) / (d : ℤ) := Int.ediv_nonneg hK (le_of_lt hdZ)
      have hN : (N : ℤ) = (k + D) / (d : ℤ) := Int.toNat_of_nonneg hq
      have hmul : (k + D) / (d : ℤ) * d ≤ k + D := Int.ediv_mul_le _ (ne_of_gt hdZ)
      have hcoZ : ((W * dotN kl ρ : ℕ) : ℤ) ≤ ((d * dotN B.co ρ : ℕ) : ℤ) := by exact_mod_cast hco'
      push_cast at hcoZ hk
      have hWnn : (0 : ℤ) ≤ (W : ℤ) := Int.natCast_nonneg _
      -- d * (N * W) ≤ d * (B.c - w + dotN B.co ρ)
      have key : (d : ℤ) * ((N : ℤ) * W) ≤ (d : ℤ) * ((B.c : ℤ) - w + dotN B.co ρ) := by
        have e1 : (d : ℤ) * ((N : ℤ) * W) = ((N : ℤ) * d) * W := by ring
        rw [e1, hN]
        have e2 : (k + D) / (d : ℤ) * d * W ≤ (k + D) * W := mul_le_mul_of_nonneg_right hmul hWnn
        have e3 : (k + D) * (W : ℤ) ≤ (W : ℤ) * k + (W : ℤ) * dotN kl ρ := by nlinarith
        nlinarith
      have key' : (N : ℤ) * W ≤ (B.c : ℤ) - w + dotN B.co ρ := le_of_mul_le_mul_left key hdZ
      have : ((N * W : ℕ) : ℤ) + w ≤ ((B.c + dotN B.co ρ : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this

/-! ### Instantiation of a callee's logical variables -/

/-- The valuation of a callee's logical variables given by the expressions `inst`. -/
def instEnv (inst : List PExp) (s : Env) : Env := fun j => (inst.getD j ⟨[], 0⟩).eval s

theorem dot_zero_env (l : List ℤ) : dot l (fun _ => 0) = 0 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [dot, ih]

theorem instEnv_nil (s : Env) : instEnv [] s = fun _ => 0 := by
  funext j; simp [instEnv, PExp.eval, dot]

theorem instEnv_cons (p : PExp) (ps : List PExp) (s : Env) :
    instEnv (p :: ps) s 0 = p.eval s ∧ (fun i => instEnv (p :: ps) s (i + 1)) = instEnv ps s := by
  refine ⟨by simp [instEnv], ?_⟩
  funext i; simp [instEnv]

theorem instLv_eval (lv : List ℤ) (inst : List PExp) (s : Env) :
    (instLv lv inst).eval s = dot lv (instEnv inst s) := by
  induction lv generalizing inst with
  | nil => simp [instLv, PExp.eval, dot]
  | cons a l ih =>
    cases inst with
    | nil =>
      rw [instEnv_nil]
      simp only [instLv, PExp.eval, dot, dot_zero_env]
      simp
    | cons p ps =>
      obtain ⟨h0, e⟩ := instEnv_cons p ps s
      have ih' := ih ps
      simp only [instLv, PExp.eval] at ih' ⊢
      simp only [dot, h0, e, dot_vadd, dot_vsmul, PExp.eval]
      rw [← ih']
      ring

theorem Lin.inst_eval (e : Lin) (inst : List PExp) (ρ s : Env) :
    (e.inst inst).eval ρ s = e.eval (instEnv inst s) s := by
  have := instLv_eval e.lv inst s
  simp only [Lin.inst, Lin.eval, dot_vadd, PExp.eval] at this ⊢
  simp [dot]
  linarith

theorem ubGoals_sound {inst : List PExp} {ubs : List SB} {ρ s : Env}
    (h : holds (ubGoals inst ubs) ρ s) (j : ℕ) (hj : j < ubs.length) (hji : j < inst.length) :
    (instEnv inst s j).toNat ≤ (ubs.getD j (SB.const 0)).eval ρ := by
  induction inst generalizing ubs j with
  | nil => simp at hji
  | cons a as ih =>
    cases ubs with
    | nil => simp at hj
    | cons u us =>
      simp only [ubGoals, holds_cons] at h
      cases j with
      | zero =>
        have h1 := h.1
        simp only [ubLin, Lin.eval, dot_vsmul] at h1
        have h2 := dot_ofNat_le u.co ρ
        have : instEnv (a :: as) s 0 = a.eval s := by simp [instEnv]
        rw [this]
        simp only [List.getD_cons_zero, SB.eval]
        simp only [PExp.eval]
        omega
      | succ j =>
        have := ih h.2 j (by simpa using hj) (by simpa using hji)
        simpa [instEnv] using this

/-! ### Frames -/

theorem dot_congr (l : List ℤ) (f g : Env) (h : ∀ i, coeff l i = 0 ∨ f i = g i) :
    dot l f = dot l g := by
  induction l generalizing f g with
  | nil => rfl
  | cons a l ih =>
    have h0 := h 0
    have hr := ih (fun i => f (i + 1)) (fun i => g (i + 1)) (fun i => by
      have := h (i + 1); simpa [coeff] using this)
    simp only [coeff, List.getD_cons_zero] at h0
    simp only [dot, hr]
    rcases h0 with h0 | h0 <;> simp [h0]

theorem holds_frameOf {M : List ℕ} {P : List Lin} {ρ s t : Env} (hP : holds P ρ s)
    (ht : ∀ x, x ∉ M → t x = s x) : holds (frameOf M P) ρ t := by
  intro e he
  simp only [frameOf, List.mem_filter, List.all_eq_true, decide_eq_true_eq] at he
  have := hP e he.1
  have hd : dot e.sv t = dot e.sv s := dot_congr _ _ _ (fun i => by
    by_cases hi : i ∈ M
    · exact Or.inl (he.2 i hi)
    · exact Or.inr (ht i hi))
  simp only [Lin.eval, hd] at this ⊢
  exact this

/-- Executions of a loop whose body preserves `I` and modifies only `M` modify only `M`. -/
theorem while_frame {Φ : ℕ → Cmd ℕ Env} {I : Env → Prop} {w : ℕ} {b : Env → Bool}
    {c : Cmd ℕ Env} {M : List ℕ}
    (hbody : ∀ s, I s → b s = true → ∀ t n, Exec Φ c s t n → I t ∧ ∀ x, x ∉ M → t x = s x) :
    ∀ {s t : Env} {n : ℕ}, I s → Exec Φ (Cmd.while w b c) s t n → ∀ x, x ∉ M → t x = s x := by
  intro s t n hI he
  revert hI
  generalize hW : Cmd.while w b c = W at he
  induction he with
  | skip => cases hW
  | atom => cases hW
  | seq => cases hW
  | iteTrue => cases hW
  | iteFalse => cases hW
  | call => cases hW
  | whileFalse => intro _ x _; rfl
  | whileTrue hb e₁ _ _ ih =>
    cases hW
    intro hI
    obtain ⟨hIu, hfr⟩ := hbody _ hI hb _ _ e₁
    intro x hx
    rw [ih rfl hIu x hx, hfr x hx]

/-! ### Certificates -/

/-- The program of a certificate, as a command of `Language` over valuations, the
    procedures being the functions of the program certificate (by index). -/
def ACmd.toCmd : ACmd → Cmd ℕ Env
  | .skip => Cmd.skip
  | .assign w x a => Cmd.atom w (fun s t => t = Function.update s x (a.eval s))
  | .havoc w x => Cmd.atom w (fun s t => ∃ v, t = Function.update s x v)
  | .havocC w x cs => Cmd.atom w (fun s t =>
      ∃ v, t = Function.update s x v ∧ cs.all (fun g => decide (g.eval t ≤ 0)))
  | .seq c₁ _ _ _ c₂ => Cmd.seq c₁.toCmd c₂.toCmd
  | .ite w g _ _ c₁ c₂ => Cmd.ite w (fun s => decide (g.eval s ≤ 0)) c₁.toCmd c₂.toCmd
  | .while w g _ _ _ _ _ _ _ _ body => Cmd.while w (fun s => decide (g.eval s ≤ 0)) body.toCmd
  | .whileAnd w gs _ _ _ _ _ _ _ _ body =>
      Cmd.while w (fun s => gs.all (fun e => decide (e.eval s ≤ 0))) body.toCmd
  | .whileLog w gs _ _ _ _ _ _ _ body =>
      Cmd.while w (fun s => gs.all (fun e => decide (e.eval s ≤ 0))) body.toCmd
  | .whileGrow w gs _ _ _ _ _ _ _ body =>
      Cmd.while w (fun s => gs.all (fun e => decide (e.eval s ≤ 0))) body.toCmd
  | .weaken _ _ _ _ _ c => c.toCmd
  | .dead _ c => c.toCmd
  | .call w f _ _ _ _ => Cmd.call w f

/-- What is required of the function `f` with the certificate `F` in the environment `Φ`
    (proved for checked bodies, assumed for contracts): its triple for every valuation of
    its logical variables, and that its executions from the precondition modify only its
    declared variables. -/
def FunSpec (Φ : ℕ → Cmd ℕ Env) (f : ℕ) (F : FunCert) : Prop :=
  (∀ ρ, Valid Φ (holds F.pre ρ) (Φ f) (F.bound.eval ρ) (holds F.post ρ)) ∧
  (∀ ρ s t n, holds F.pre ρ s → Exec Φ (Φ f) s t n → ∀ x, x ∉ F.mods → t x = s x)

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

theorem entryLin_eval (pot : PExp) (k : ℤ) (kl : List ℕ) (ρ s : Env) :
    (entryLin pot k kl).eval ρ s = pot.eval s - (k + dot (kl.map Int.ofNat) ρ) := by
  simp only [entryLin, Lin.eval, PExp.eval, dot_vsmul]; ring

/-- The loop case, shared by `while` and `whileAnd`: `test` is the loop test, `G` the
    constraints it yields, `Qe` the postcondition. -/
theorem loop_sound {Φ : ℕ → Cmd ℕ Env} {w : ℕ} {test : Env → Bool} {G inv Qe : List Lin}
    {pot : PExp} {d : ℕ} {k : ℤ} {kl : List ℕ} {j : ℕ} {posCert : ℕ × List ℕ} {Wb B : SB}
    {body : Cmd ℕ Env} {M : List ℕ} (ρ : Env)
    (hd : 0 < d) (hinv : inv.all (fun e => decide (coeff e.lv j = 0)) = true)
    (hWj : ncoeff Wb.co j = 0)
    (hG : ∀ s, test s = true → holds G ρ s)
    (hGj : G.all (fun e => decide (coeff e.lv j = 0)) = true)
    (hpos : entails1 (G ++ inv) ⟨vsmul (-1) pot.sv, [], d - pot.c⟩ posCert = true)
    (hbody : ∀ ρ', Valid Φ (holds (ghost pot j 0 :: (G ++ inv)) ρ') body (Wb.eval ρ')
        (holds (ghost pot j d :: inv) ρ') ∧
      ∀ s t n, holds (ghost pot j 0 :: (G ++ inv)) ρ' s → Exec Φ body s t n →
        ∀ x, x ∉ M → t x = s x)
    (hB : loopBoundOk w d k kl Wb B = true)
    (hQ : ∀ t, holds inv ρ t → test t = false → holds Qe ρ t) :
    Valid Φ (holds (entryLin pot k kl :: inv) ρ) (Cmd.while w test body) (B.eval ρ)
        (holds Qe ρ) ∧
      ∀ s t n, holds (entryLin pot k kl :: inv) ρ s → Exec Φ (Cmd.while w test body) s t n →
        ∀ x, x ∉ M → t x = s x := by
  have hd' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have happ : ∀ s, holds G ρ s → holds inv ρ s → holds (G ++ inv) ρ s := by
    intro s hA hB e he
    rcases List.mem_append.mp he with h | h
    · exact hA e h
    · exact hB e h
  have hGinv : (G ++ inv).all (fun e => decide (coeff e.lv j = 0)) = true := by
    simp only [List.all_append, Bool.and_eq_true]; exact ⟨hGj, hinv⟩
  -- the body, read at the outer valuation with `γⱼ` set to the potential
  have body_at : ∀ s, holds inv ρ s → test s = true →
      Valid Φ (holds (ghost pot j 0 :: (G ++ inv)) (Function.update ρ j (pot.eval s))) body
        (Wb.eval ρ) (holds (ghost pot j d :: inv) (Function.update ρ j (pot.eval s))) ∧
      holds (ghost pot j 0 :: (G ++ inv)) (Function.update ρ j (pot.eval s)) s := by
    intro s hI hb
    refine ⟨?_, ?_⟩
    · have := (hbody (Function.update ρ j (pot.eval s))).1
      rwa [SB.eval, dotN_update hWj, ← SB.eval] at this
    · rw [holds_cons, ghost_eval, holds_update_logical hGinv]
      exact ⟨by simp, happ s (hG s hb) hI⟩
  have key := valid_while (Φ := Φ) (I := holds inv ρ)
    (C := fun s => pot.eval s ≤ k + dot (kl.map Int.ofNat) ρ)
    (w := w) (b := test) (c := body) (Wb := Wb.eval ρ)
    (fun s => (pot.eval s : ℚ) / d) (((k + dot (kl.map Int.ofNat) ρ : ℤ) : ℚ) / d) ?_ ?_ ?_
  · refine ⟨?_, ?_⟩
    · refine valid_conseq ?_ key ?_ ?_
      · intro s hP
        rw [holds_cons, entryLin_eval] at hP
        exact ⟨hP.2, by linarith [hP.1]⟩
      · rw [floor_div]; exact loopBoundOk_sound hB hd ρ
      · rintro t ⟨hI, hb⟩; exact hQ t hI hb
    · intro s t n hP he
      rw [holds_cons] at hP
      refine while_frame (I := holds inv ρ) (fun s' hI hb t' n' e => ?_) hP.2 he
      obtain ⟨hv, hpre⟩ := body_at s' hI hb
      have ht := (hv s' hpre).2 t' n' e
      rw [holds_cons, holds_update_logical hinv] at ht
      exact ⟨ht.2, (hbody _).2 s' t' n' hpre e⟩
  · intro v s hs
    obtain ⟨hI, hb, hv⟩ := hs
    obtain ⟨H, hpre⟩ := body_at s hI hb
    refine ⟨(H s hpre).1, fun t n he => ?_⟩
    have ht := (H s hpre).2 t n he
    rw [holds_cons, ghost_eval, holds_update_logical hinv] at ht
    refine ⟨ht.2, ?_⟩
    have h1 : pot.eval t + d ≤ pot.eval s := by
      have := ht.1
      simp at this
      linarith
    have h2 : ((pot.eval t : ℚ) + d) ≤ (pot.eval s : ℚ) := by exact_mod_cast h1
    rw [← hv, div_le_iff₀ hd', sub_mul, div_mul_cancel₀ _ (ne_of_gt hd')]
    linarith
  · intro s hI hb
    have := entails1_sound hpos (ρ := ρ) (s := s) (happ s (hG s hb) hI)
    simp only [Lin.eval, dot, dot_vsmul] at this
    have h1 : (d : ℤ) ≤ pot.eval s := by simp only [PExp.eval]; linarith
    have h2 : (d : ℚ) ≤ (pot.eval s : ℚ) := by exact_mod_cast h1
    rw [le_div_iff₀ hd']
    linarith
  · intro s hs
    have h2 : (pot.eval s : ℚ) ≤ ((k + dot (kl.map Int.ofNat) ρ : ℤ) : ℚ) := by exact_mod_cast hs
    exact div_le_div_of_nonneg_right h2 (le_of_lt hd')

/-! ### Amortised (triangular) loops -/

theorem dotN_set (l : List ℕ) (j : ℕ) (f : Env) :
    dotN l f = dotN (l.set j 0) f + ncoeff l j * (f j).toNat := by
  induction l generalizing j f with
  | nil => simp [dotN, ncoeff]
  | cons a l ih =>
    cases j with
    | zero => simp [dotN, ncoeff, List.set]; ring
    | succ j =>
      have := ih j (fun i => f (i + 1))
      simp only [dotN, ncoeff, List.set, List.getD_cons_succ] at this ⊢
      rw [this]; ring

/-- A body bound mentioning only `γⱼ`, read at `γⱼ = v`. -/
theorem SB.eval_only {Wb : SB} {j : ℕ} (h : (Wb.co.set j 0).all (· = 0) = true) (ρ : Env) :
    Wb.eval ρ = Wb.c + ncoeff Wb.co j * (ρ j).toNat := by
  simp only [SB.eval]
  rw [dotN_set Wb.co j ρ, dotN_zero h, zero_add]

/-- One iteration of the doubled amortised bound: for `k ≥ d`,
    `triBound2 k = 2 (w + a) + 2 c k + triBound2 (k - d)`. -/
theorem triBound2_step {w d a c : ℕ} (hd : 0 < d) {X : ℤ} (hX : (d : ℤ) ≤ X) :
    triBound2 w d a c X = 2 * ((w : ℤ) + a) + 2 * c * X + triBound2 w d a c (X - d) := by
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hd)
  have hq : X / (d : ℤ) = (X - d) / (d : ℤ) + 1 := by
    have : X = (X - d) + 1 * (d : ℤ) := by ring
    conv_lhs => rw [this]
    rw [Int.add_mul_ediv_right _ _ hdZ]
  have hM : 0 ≤ (X - d) / (d : ℤ) :=
    Int.ediv_nonneg (by linarith) (by exact_mod_cast Nat.zero_le d)
  have h1 : (((X / (d : ℤ)).toNat : ℕ) : ℤ) = (X - d) / (d : ℤ) + 1 := by
    rw [hq]; exact Int.toNat_of_nonneg (by linarith)
  have h2 : ((((X - d) / (d : ℤ)).toNat : ℕ) : ℤ) = (X - d) / (d : ℤ) :=
    Int.toNat_of_nonneg hM
  simp only [triBound2]
  rw [h1, h2]
  ring

/-- The doubled amortised bound is at least `2 w`. -/
theorem triBound2_ge {w d a c : ℕ} (hd : 0 < d) (X : ℤ) : 2 * (w : ℤ) ≤ triBound2 w d a c X := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  simp only [triBound2]
  set N : ℤ := (((X / (d : ℤ)).toNat : ℕ) : ℤ) with hN
  have hN0 : 0 ≤ N := Int.natCast_nonneg _
  have hNd : N * d ≤ X ∨ N = 0 := by
    by_cases hq : 0 ≤ X / (d : ℤ)
    · left
      rw [hN, Int.toNat_of_nonneg hq]
      exact Int.ediv_mul_le _ (ne_of_gt hdZ)
    · right
      rw [hN]; omega
  have hc : (0 : ℤ) ≤ c := Int.natCast_nonneg _
  have ha : (0 : ℤ) ≤ a := Int.natCast_nonneg _
  have hw : (0 : ℤ) ≤ w := Int.natCast_nonneg _
  have hS : 0 ≤ 2 * N * X - d * N * (N - 1) := by
    rcases hNd with h | h
    · have e : N * (N * d) ≤ N * X := mul_le_mul_of_nonneg_left h hN0
      nlinarith [e, mul_nonneg (mul_nonneg hdZ.le hN0) hN0, mul_nonneg hdZ.le hN0]
    · rw [h]; ring_nf; exact le_refl _
  nlinarith

/-- The loop case with a body bound `a + c·γⱼ` (amortised), from `valid_whileSum`. -/
theorem triloop_sound {Φ : ℕ → Cmd ℕ Env} {w : ℕ} {test : Env → Bool} {G inv Qe : List Lin}
    {pot : PExp} {d : ℕ} {k : ℤ} {kl : List ℕ} {j : ℕ} {posCert : ℕ × List ℕ} {Wb B : SB}
    {body : Cmd ℕ Env} {M : List ℕ} (ρ : Env)
    (hd : 0 < d) (hinv : inv.all (fun e => decide (coeff e.lv j = 0)) = true)
    (hG : ∀ s, test s = true → holds G ρ s)
    (hGj : G.all (fun e => decide (coeff e.lv j = 0)) = true)
    (hpos : entails1 (G ++ inv) ⟨vsmul (-1) pot.sv, [], d - pot.c⟩ posCert = true)
    (hbody : ∀ ρ', Valid Φ (holds (ghost pot j 0 :: (G ++ inv)) ρ') body (Wb.eval ρ')
        (holds (ghost pot j d :: inv) ρ') ∧
      ∀ s t n, holds (ghost pot j 0 :: (G ++ inv)) ρ' s → Exec Φ body s t n →
        ∀ x, x ∉ M → t x = s x)
    (hB : triOk w d k kl j Wb B = true)
    (hQ : ∀ t, holds inv ρ t → test t = false → holds Qe ρ t) :
    Valid Φ (holds (entryLin pot k kl :: inv) ρ) (Cmd.while w test body) (B.eval ρ)
        (holds Qe ρ) ∧
      ∀ s t n, holds (entryLin pot k kl :: inv) ρ s → Exec Φ (Cmd.while w test body) s t n →
        ∀ x, x ∉ M → t x = s x := by
  simp only [triOk, Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨hkl, hWo⟩, hT⟩ := hB
  set a := Wb.c
  set c := ncoeff Wb.co j
  have happ : ∀ s, holds G ρ s → holds inv ρ s → holds (G ++ inv) ρ s := by
    intro s hA hB e he
    rcases List.mem_append.mp he with h | h
    · exact hA e h
    · exact hB e h
  have hGinv : (G ++ inv).all (fun e => decide (coeff e.lv j = 0)) = true := by
    simp only [List.all_append, Bool.and_eq_true]; exact ⟨hGj, hinv⟩
  have body_at : ∀ s, holds inv ρ s → test s = true →
      Valid Φ (holds (ghost pot j 0 :: (G ++ inv)) (Function.update ρ j (pot.eval s))) body
        (a + c * (pot.eval s).toNat)
        (holds (ghost pot j d :: inv) (Function.update ρ j (pot.eval s))) ∧
      holds (ghost pot j 0 :: (G ++ inv)) (Function.update ρ j (pot.eval s)) s := by
    intro s hI hb
    refine ⟨?_, ?_⟩
    · have := (hbody (Function.update ρ j (pot.eval s))).1
      rwa [SB.eval_only hWo, Function.update_self] at this
    · rw [holds_cons, ghost_eval, holds_update_logical hGinv]
      exact ⟨by simp, happ s (hG s hb) hI⟩
  -- the bound, halved
  let T : ℤ → ℤ := fun X => triBound2 w d a c X / 2
  have hT2 : ∀ X, triBound2 w d a c X = 2 * T X := by
    intro X
    have hev : (2 : ℤ) ∣ triBound2 w d a c X := by
      simp only [triBound2]
      set N : ℤ := (((X / (d : ℤ)).toNat : ℕ) : ℤ)
      have : (2 : ℤ) ∣ N * (N - 1) := by
        rcases Int.even_or_odd N with ⟨m, hm⟩ | ⟨m, hm⟩
        · exact ⟨m * (N - 1), by rw [hm]; ring⟩
        · exact ⟨N * m, by rw [hm]; ring⟩
      obtain ⟨m, hm⟩ := this
      exact ⟨(((X / (d : ℤ)).toNat : ℕ) + 1) * w + N * a + c * (N * X - d * m),
        by rw [show (d : ℤ) * N * (N - 1) = d * (N * (N - 1)) by ring, hm]; ring⟩
    simp only [T]
    exact (Int.mul_ediv_cancel' hev).symm
  have hTge : ∀ X, (w : ℤ) ≤ T X := by
    intro X
    have := triBound2_ge (w := w) (a := a) (c := c) hd X
    rw [hT2] at this; linarith
  have hTstep : ∀ X, (d : ℤ) ≤ X → T X = w + a + c * X + T (X - d) := by
    intro X hX
    have := triBound2_step (a := a) (c := c) (w := w) hd hX
    rw [hT2, hT2] at this; linarith
  have key := valid_whileSum (Φ := Φ) (I := holds inv ρ) (w := w) (b := test) (c := body)
    (fun s => pot.eval s) d (fun v => a + c * v.toNat) (fun X => (T X).toNat) k ?_ ?_ ?_ ?_
  · refine ⟨?_, ?_⟩
    · refine valid_conseq ?_ key ?_ ?_
      · intro s hP
        rw [holds_cons, entryLin_eval, dot_ofNat_zero hkl] at hP
        exact ⟨hP.2, by linarith [hP.1]⟩
      · have h1 : T k ≤ B.c := by rw [hT2] at hT; linarith
        have h2 : B.c ≤ B.eval ρ := by simp [SB.eval]
        omega
      · rintro t ⟨hI, hb⟩; exact hQ t hI hb
    · intro s t n hP he
      rw [holds_cons] at hP
      refine while_frame (I := holds inv ρ) (fun s' hI hb t' n' e => ?_) hP.2 he
      obtain ⟨hv, hpre⟩ := body_at s' hI hb
      have ht := (hv s' hpre).2 t' n' e
      rw [holds_cons, holds_update_logical hinv] at ht
      exact ⟨ht.2, (hbody _).2 s' t' n' hpre e⟩
  · intro s hI hb
    obtain ⟨H, hpre⟩ := body_at s hI hb
    refine ⟨fun n hn => (H s hpre).1 n hn, fun t n he => ?_⟩
    have ht := (H s hpre).2 t n he
    rw [holds_cons, ghost_eval, holds_update_logical hinv] at ht
    refine ⟨ht.2, ?_⟩
    have := ht.1
    rw [Function.update_self] at this
    linarith
  · intro s hI hb
    have := entails1_sound hpos (ρ := ρ) (s := s) (happ s (hG s hb) hI)
    simp only [Lin.eval, dot, dot_vsmul] at this
    simp only [PExp.eval]; linarith
  · intro X
    have := hTge X
    show w ≤ (T X).toNat
    omega
  · intro X v hv hvX
    have hs := hTstep X (le_trans hv hvX)
    have h0 := hTge (X - d)
    have hcv : (c : ℤ) * v ≤ c * X := mul_le_mul_of_nonneg_left hvX (Int.natCast_nonneg _)
    have h1 := hTge X
    have hvn : ((v.toNat : ℕ) : ℤ) = v := Int.toNat_of_nonneg (by omega)
    have e1 : ((T (X - d)).toNat : ℤ) = T (X - d) := Int.toNat_of_nonneg (by omega)
    have e2 : ((T X).toNat : ℤ) = T X := Int.toNat_of_nonneg (by omega)
    have : ((w + (a + c * v.toNat) + (T (X - d)).toNat : ℕ) : ℤ) ≤ ((T X).toNat : ℤ) := by
      push_cast
      rw [hvn, e1, e2]
      linarith
    exact_mod_cast this

/-! ### Logarithmic loops -/

theorem ilogF_eq (b : ℕ) : ∀ fuel n, n ≤ fuel → ilogF fuel b n = Nat.log b n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this; simp [ilogF]
  | succ f ih =>
    intro n hn
    simp only [ilogF]
    split
    · next h =>
      have hlt : n / b < n := Nat.div_lt_self (by omega) h.1
      rw [ih (n / b) (by omega), Nat.log_div_base]
      have := Nat.log_pos h.1 h.2
      omega
    · next h =>
      symm
      rw [Nat.log_eq_zero_iff]
      omega

theorem ilog_eq (b n : ℕ) : ilog b n = Nat.log b n := ilogF_eq b n n (le_refl _)

/-- The potential that a logarithmic loop decreases by one per iteration: `0` if
    `pot ≤ 0`, else `⌊log_b pot⌋ + 1`. -/
def logPot (b : ℕ) (x : ℤ) : ℕ := if x ≤ 0 then 0 else Nat.log b x.toNat + 1

theorem logPot_step {b : ℕ} (hb : 1 < b) {x y : ℤ} (hx : 1 ≤ x) (hy : (b : ℤ) * y ≤ x) :
    logPot b y + 1 ≤ logPot b x := by
  have hx0 : ¬ x ≤ 0 := by omega
  simp only [logPot, hx0, if_false]
  split_ifs with hy0
  · omega
  · have hy1 : 1 ≤ y := by omega
    have hby : (b : ℤ) ≤ x := by
      have : (b : ℤ) * 1 ≤ (b : ℤ) * y := mul_le_mul_of_nonneg_left hy1 (by positivity)
      linarith
    have hle : y.toNat ≤ x.toNat / b := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      have e1 : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg (by omega)
      have e2 : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg (by omega)
      have : ((y.toNat * b : ℕ) : ℤ) ≤ ((x.toNat : ℕ) : ℤ) := by
        push_cast; rw [e1, e2]; linarith
      exact_mod_cast this
    have h1 := Nat.log_mono_right (b := b) hle
    rw [Nat.log_div_base] at h1
    have hbx : b ≤ x.toNat := by omega
    have := Nat.log_pos hb hbx
    omega

theorem logPot_le {b : ℕ} {x k : ℤ} (h : x ≤ k) : logPot b x ≤ logIters b k := by
  unfold logPot logIters
  split
  · exact Nat.zero_le _
  · rw [if_neg (by omega), ilog_eq]
    have := Nat.log_mono_right (b := b) (show x.toNat ≤ k.toNat by omega)
    omega

theorem ghostMul_eval (pot : PExp) (j b : ℕ) (ρ s : Env) :
    (ghostMul pot j b).eval ρ s = b * pot.eval s - ρ j := by
  simp only [ghostMul, Lin.eval, PExp.eval, dot_vsmul, dot_unit]; ring

/-- The loop rule of `whileLog`, from `valid_while` with the potential `logPot b pot`. -/
theorem logloop_sound {Φ : ℕ → Cmd ℕ Env} {w : ℕ} {test : Env → Bool} {G inv Qe : List Lin}
    {pot : PExp} {b : ℕ} {k : ℤ} {j : ℕ} {posCert : ℕ × List ℕ} {Wb : SB}
    {body : Cmd ℕ Env} {M : List ℕ} (ρ : Env)
    (hb : 1 < b) (hinv : inv.all (fun e => decide (coeff e.lv j = 0)) = true)
    (hWc : Wb.co.all (· = 0) = true)
    (hG : ∀ s, test s = true → holds G ρ s)
    (hGj : G.all (fun e => decide (coeff e.lv j = 0)) = true)
    (hpos : entails1 (G ++ inv) ⟨vsmul (-1) pot.sv, [], 1 - pot.c⟩ posCert = true)
    (hbody : ∀ ρ', Valid Φ (holds (ghost pot j 0 :: (G ++ inv)) ρ') body (Wb.eval ρ')
        (holds (ghostMul pot j b :: inv) ρ') ∧
      ∀ s t n, holds (ghost pot j 0 :: (G ++ inv)) ρ' s → Exec Φ body s t n →
        ∀ x, x ∉ M → t x = s x)
    (hQ : ∀ t, holds inv ρ t → test t = false → holds Qe ρ t) :
    Valid Φ (holds (entryLin pot k [] :: inv) ρ) (Cmd.while w test body)
        (logIters b k * (w + Wb.c) + w) (holds Qe ρ) ∧
      ∀ s t n, holds (entryLin pot k [] :: inv) ρ s → Exec Φ (Cmd.while w test body) s t n →
        ∀ x, x ∉ M → t x = s x := by
  have hWeval : ∀ ρ', Wb.eval ρ' = Wb.c := by
    intro ρ'
    simp only [SB.eval, dotN_zero hWc, add_zero]
  have happ : ∀ s, holds G ρ s → holds inv ρ s → holds (G ++ inv) ρ s := by
    intro s hA hB e he
    rcases List.mem_append.mp he with h | h
    · exact hA e h
    · exact hB e h
  have hGinv : (G ++ inv).all (fun e => decide (coeff e.lv j = 0)) = true := by
    simp only [List.all_append, Bool.and_eq_true]; exact ⟨hGj, hinv⟩
  have body_at : ∀ s, holds inv ρ s → test s = true →
      Valid Φ (holds (ghost pot j 0 :: (G ++ inv)) (Function.update ρ j (pot.eval s))) body
        Wb.c (holds (ghostMul pot j b :: inv) (Function.update ρ j (pot.eval s))) ∧
      holds (ghost pot j 0 :: (G ++ inv)) (Function.update ρ j (pot.eval s)) s := by
    intro s hI hbt
    refine ⟨?_, ?_⟩
    · have := (hbody (Function.update ρ j (pot.eval s))).1
      rwa [hWeval] at this
    · rw [holds_cons, ghost_eval, holds_update_logical hGinv]
      exact ⟨by simp, happ s (hG s hbt) hI⟩
  have pos : ∀ s, holds inv ρ s → test s = true → 1 ≤ pot.eval s := by
    intro s hI hbt
    have := entails1_sound hpos (ρ := ρ) (s := s) (happ s (hG s hbt) hI)
    simp only [Lin.eval, dot, dot_vsmul] at this
    simp only [PExp.eval]; linarith
  have key := valid_while (Φ := Φ) (I := holds inv ρ) (C := fun s => pot.eval s ≤ k)
    (w := w) (b := test) (c := body) (Wb := Wb.c)
    (fun s => ((logPot b (pot.eval s) : ℕ) : ℚ)) ((logIters b k : ℕ) : ℚ) ?_ ?_ ?_
  · rw [Nat.floor_natCast] at key
    refine ⟨?_, ?_⟩
    · refine valid_conseq ?_ key (le_refl _) ?_
      · intro s hP
        rw [holds_cons, entryLin_eval] at hP
        have h1 := hP.1
        simp only [List.map_nil, dot, add_zero] at h1
        exact ⟨hP.2, by linarith⟩
      · rintro t ⟨hI, hbt⟩; exact hQ t hI hbt
    · intro s t n hP he
      rw [holds_cons] at hP
      refine while_frame (I := holds inv ρ) (fun s' hI hbt t' n' e => ?_) hP.2 he
      obtain ⟨hv, hpre⟩ := body_at s' hI hbt
      have ht := (hv s' hpre).2 t' n' e
      rw [holds_cons, holds_update_logical hinv] at ht
      exact ⟨ht.2, (hbody _).2 s' t' n' hpre e⟩
  · intro v s hs
    obtain ⟨hI, hbt, hv⟩ := hs
    obtain ⟨H, hpre⟩ := body_at s hI hbt
    refine ⟨(H s hpre).1, fun t n he => ?_⟩
    have ht := (H s hpre).2 t n he
    rw [holds_cons, ghostMul_eval, holds_update_logical hinv] at ht
    refine ⟨ht.2, ?_⟩
    have h1 : (b : ℤ) * pot.eval t ≤ pot.eval s := by
      have := ht.1; rw [Function.update_self] at this; linarith
    have h2 := logPot_step hb (pos s hI hbt) h1
    rw [← hv]
    have : ((logPot b (pot.eval t) : ℕ) : ℚ) + 1 ≤ ((logPot b (pot.eval s) : ℕ) : ℚ) := by
      exact_mod_cast h2
    linarith
  · intro s hI hbt
    have h1 := pos s hI hbt
    have : 1 ≤ logPot b (pot.eval s) := by
      unfold logPot; rw [if_neg (by omega)]; omega
    show (1 : ℚ) ≤ ((logPot b (pot.eval s) : ℕ) : ℚ)
    exact_mod_cast this
  · intro s hs
    show ((logPot b (pot.eval s) : ℕ) : ℚ) ≤ ((logIters b k : ℕ) : ℚ)
    exact_mod_cast logPot_le (b := b) hs

/-! ### Growing logarithmic loops -/

theorem growEntry_eval (pot : PExp) (ρ s : Env) : (growEntry pot).eval ρ s = 1 - pot.eval s := by
  simp only [growEntry, Lin.eval, PExp.eval, dot_vsmul, dot]; ring

theorem ghostLow_eval (pot : PExp) (j : ℕ) (ρ s : Env) :
    (ghostLow pot j).eval ρ s = ρ j - pot.eval s := by
  simp only [ghostLow, Lin.eval, PExp.eval, dot_vsmul, dot_unit]; ring

theorem ghostGrow_eval (pot : PExp) (j b : ℕ) (ρ s : Env) :
    (ghostGrow pot j b).eval ρ s = b * ρ j - pot.eval s := by
  simp only [ghostGrow, Lin.eval, PExp.eval, dot_vsmul, dot_unit]; ring

/-- One growth step increases `⌊log_b⌋` by at least one. -/
theorem log_grow {b : ℕ} (hb : 1 < b) {x y : ℤ} (hx : 1 ≤ x) (hy : (b : ℤ) * x ≤ y) :
    Nat.log b x.toNat + 1 ≤ Nat.log b y.toNat := by
  have hle : x.toNat ≤ y.toNat / b := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have e1 : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg (by omega)
    have hy0 : 0 ≤ y := by
      have : (0 : ℤ) ≤ (b : ℤ) * x := by positivity
      linarith
    have e2 : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy0
    have : ((x.toNat * b : ℕ) : ℤ) ≤ ((y.toNat : ℕ) : ℤ) := by
      push_cast; rw [e1, e2]; linarith
    exact_mod_cast this
  have h1 := Nat.log_mono_right (b := b) hle
  rw [Nat.log_div_base] at h1
  have hby : b ≤ y.toNat := by
    have : (b : ℤ) * 1 ≤ (b : ℤ) * x := mul_le_mul_of_nonneg_left hx (by positivity)
    omega
  have := Nat.log_pos hb hby
  omega

/-- The loop rule of `whileGrow`, from `valid_while` with the potential
    `logIters b K - ⌊log_b pot⌋`. -/
theorem growloop_sound {Φ : ℕ → Cmd ℕ Env} {w : ℕ} {test : Env → Bool} {G inv Qe : List Lin}
    {pot : PExp} {b : ℕ} {K : ℤ} {j : ℕ} {capCert : ℕ × List ℕ} {Wb : SB}
    {body : Cmd ℕ Env} {M : List ℕ} (ρ : Env)
    (hb : 1 < b) (hinv : inv.all (fun e => decide (coeff e.lv j = 0)) = true)
    (hWc : Wb.co.all (· = 0) = true)
    (hG : ∀ s, test s = true → holds G ρ s)
    (hGj : G.all (fun e => decide (coeff e.lv j = 0)) = true)
    (hcap : entails1 (G ++ inv) ⟨pot.sv, [], pot.c - K⟩ capCert = true)
    (hbody : ∀ ρ', Valid Φ (holds (ghostLow pot j :: growEntry pot :: (G ++ inv)) ρ') body
        (Wb.eval ρ') (holds (ghostGrow pot j b :: inv) ρ') ∧
      ∀ s t n, holds (ghostLow pot j :: growEntry pot :: (G ++ inv)) ρ' s → Exec Φ body s t n →
        ∀ x, x ∉ M → t x = s x)
    (hQ : ∀ t, holds inv ρ t → test t = false → holds Qe ρ t) :
    Valid Φ (holds (growEntry pot :: inv) ρ) (Cmd.while w test body)
        (logIters b K * (w + Wb.c) + w) (holds Qe ρ) ∧
      ∀ s t n, holds (growEntry pot :: inv) ρ s → Exec Φ (Cmd.while w test body) s t n →
        ∀ x, x ∉ M → t x = s x := by
  have hWeval : ∀ ρ', Wb.eval ρ' = Wb.c := by
    intro ρ'
    simp only [SB.eval, dotN_zero hWc, add_zero]
  have happ : ∀ s, holds G ρ s → holds inv ρ s → holds (G ++ inv) ρ s := by
    intro s hA hB e he
    rcases List.mem_append.mp he with h | h
    · exact hA e h
    · exact hB e h
  have hGinv : (G ++ inv).all (fun e => decide (coeff e.lv j = 0)) = true := by
    simp only [List.all_append, Bool.and_eq_true]; exact ⟨hGj, hinv⟩
  have hEj : (growEntry pot :: (G ++ inv)).all (fun e => decide (coeff e.lv j = 0)) = true := by
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨by simp [growEntry, coeff], hGinv⟩
  let I : Env → Prop := fun s => holds inv ρ s ∧ 1 ≤ pot.eval s
  have body_at : ∀ s, I s → test s = true →
      Valid Φ (holds (ghostLow pot j :: growEntry pot :: (G ++ inv)) (Function.update ρ j (pot.eval s)))
        body Wb.c (holds (ghostGrow pot j b :: inv) (Function.update ρ j (pot.eval s))) ∧
      holds (ghostLow pot j :: growEntry pot :: (G ++ inv)) (Function.update ρ j (pot.eval s)) s := by
    intro s hI hbt
    refine ⟨?_, ?_⟩
    · have := (hbody (Function.update ρ j (pot.eval s))).1
      rwa [hWeval] at this
    · rw [holds_cons, ghostLow_eval, holds_update_logical hEj, holds_cons, growEntry_eval]
      exact ⟨by simp, by linarith [hI.2], happ s (hG s hbt) hI.1⟩
  have cap : ∀ s, I s → test s = true → pot.eval s ≤ K := by
    intro s hI hbt
    have := entails1_sound hcap (ρ := ρ) (s := s) (happ s (hG s hbt) hI.1)
    simp only [Lin.eval, dot, PExp.eval] at this ⊢
    linarith
  let V : Env → ℕ := fun s => logIters b K - Nat.log b (pot.eval s).toNat
  have key := valid_while (Φ := Φ) (I := I) (C := fun _ => True)
    (w := w) (b := test) (c := body) (Wb := Wb.c)
    (fun s => ((V s : ℕ) : ℚ)) ((logIters b K : ℕ) : ℚ) ?_ ?_ ?_
  · rw [Nat.floor_natCast] at key
    refine ⟨?_, ?_⟩
    · refine valid_conseq ?_ key (le_refl _) ?_
      · intro s hP
        rw [holds_cons, growEntry_eval] at hP
        exact ⟨⟨hP.2, by linarith [hP.1]⟩, trivial⟩
      · rintro t ⟨hI, hbt⟩; exact hQ t hI.1 hbt
    · intro s t n hP he
      rw [holds_cons, growEntry_eval] at hP
      refine while_frame (I := I) (fun s' hI hbt t' n' e => ?_) ⟨hP.2, by linarith [hP.1]⟩ he
      obtain ⟨hv, hpre⟩ := body_at s' hI hbt
      have ht := (hv s' hpre).2 t' n' e
      rw [holds_cons, ghostGrow_eval, holds_update_logical hinv, Function.update_self] at ht
      have h1 := hI.2
      refine ⟨⟨ht.2, ?_⟩, (hbody _).2 s' t' n' hpre e⟩
      have : (b : ℤ) * 1 ≤ (b : ℤ) * pot.eval s' := mul_le_mul_of_nonneg_left h1 (by positivity)
      have : (1 : ℤ) ≤ b := by exact_mod_cast hb.le
      linarith [ht.1]
  · intro v s hs
    obtain ⟨hI, hbt, hv⟩ := hs
    obtain ⟨H, hpre⟩ := body_at s hI hbt
    refine ⟨(H s hpre).1, fun t n he => ?_⟩
    have ht := (H s hpre).2 t n he
    rw [holds_cons, ghostGrow_eval, holds_update_logical hinv, Function.update_self] at ht
    have hgrow : (b : ℤ) * pot.eval s ≤ pot.eval t := by linarith [ht.1]
    have h1 := hI.2
    have hpt : 1 ≤ pot.eval t := by
      have : (b : ℤ) * 1 ≤ (b : ℤ) * pot.eval s := mul_le_mul_of_nonneg_left h1 (by positivity)
      have : (1 : ℤ) ≤ b := by exact_mod_cast hb.le
      linarith
    refine ⟨⟨ht.2, hpt⟩, ?_⟩
    have hl := log_grow hb h1 hgrow
    -- V s ≥ 1 (the test holds at s)
    have hK := cap s hI hbt
    have hKpos : 1 ≤ K := le_trans h1 hK
    have hmono := Nat.log_mono_right (b := b) (show (pot.eval s).toNat ≤ K.toNat by omega)
    have hL : logIters b K = Nat.log b K.toNat + 1 := by
      simp only [logIters, ilog_eq]; rw [if_neg (by omega)]
    have : V t + 1 ≤ V s := by
      simp only [V, hL]; omega
    rw [← hv]
    have : ((V t : ℕ) : ℚ) + 1 ≤ ((V s : ℕ) : ℚ) := by exact_mod_cast this
    linarith
  · intro s hI hbt
    have hK := cap s hI hbt
    have hKpos : 1 ≤ K := le_trans hI.2 hK
    have hmono := Nat.log_mono_right (b := b) (show (pot.eval s).toNat ≤ K.toNat by omega)
    have hL : logIters b K = Nat.log b K.toNat + 1 := by
      simp only [logIters, ilog_eq]; rw [if_neg (by omega)]
    have : 1 ≤ V s := by simp only [V, hL]; omega
    show (1 : ℚ) ≤ ((V s : ℕ) : ℚ)
    exact_mod_cast this
  · intro s _
    show ((V s : ℕ) : ℚ) ≤ ((logIters b K : ℕ) : ℚ)
    exact_mod_cast Nat.sub_le _ _

/-- **Soundness of the checker.** If every function that calls may refer to meets its
    specification (`hfs`), a certificate accepted by `check` proves its triple: for
    every valuation `ρ` of the logical variables, from every state satisfying `P`, every
    execution prefix of the program costs at most `B` (evaluated at `ρ`), every
    terminating execution ends in `Q`, and modifies only the variables `writes`. -/
theorem check_sound (fs : List FunCert) (Φ : ℕ → Cmd ℕ Env)
    (hfs : ∀ f F, fs[f]? = some F → FunSpec Φ f F) (c : ACmd) :
    ∀ (P Q : List Lin) (B : SB), check fs P c B Q = true → ∀ ρ,
      Valid Φ (holds P ρ) c.toCmd (B.eval ρ) (holds Q ρ) ∧
      ∀ s t n, holds P ρ s → Exec Φ c.toCmd s t n → ∀ x, x ∉ writes fs c → t x = s x := by
  induction c with
  | skip =>
    intro P Q B h ρ
    simp only [check, decide_eq_true_eq] at h
    subst h
    refine ⟨valid_conseq (fun _ h => h) (valid_skip _) (Nat.zero_le _) (fun _ h => h), ?_⟩
    intro s t n _ he x _
    cases he; rfl
  | assign w x a =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hB⟩ := h
    refine ⟨valid_conseq (fun _ h => h) (valid_atom _ _ _ _ ?_)
      (by simpa using SB.le_eval hB ρ) (fun _ h => h), ?_⟩
    · rintro s t hP rfl e he
      have := hP (e.subst x a) (List.mem_map_of_mem _ he)
      rwa [Lin.subst_eval] at this
    · intro s t n _ he y hy
      cases he with
      | atom h =>
        rw [h]
        simp only [writes, List.mem_singleton] at hy
        simp [Function.update, hy]
  | havoc w x =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨rfl, hx⟩, hB⟩ := h
    refine ⟨valid_conseq (fun _ h => h) (valid_atom _ _ _ _ ?_)
      (by simpa using SB.le_eval hB ρ) (fun _ h => h), ?_⟩
    · rintro s t hP ⟨v, rfl⟩ e he
      rw [Lin.eval_update, hx e he, zero_mul, add_zero]
      exact hP e he
    · intro s t n _ he y hy
      cases he with
      | atom h =>
        obtain ⟨v, rfl⟩ := h
        simp only [writes, List.mem_singleton] at hy
        simp [Function.update, hy]
  | havocC w x cs =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨rfl, hx⟩, hB⟩ := h
    refine ⟨valid_conseq (fun _ h => h) (valid_atom _ _ _ _ ?_)
      (by simpa using SB.le_eval hB ρ) (fun _ h => h), ?_⟩
    · rintro s t hP ⟨v, rfl, hcs⟩ e he
      rcases List.mem_append.mp he with he | he
      · rw [Lin.eval_update, hx e he, zero_mul, add_zero]
        exact hP e he
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
        simp only [List.all_eq_true, decide_eq_true_eq] at hcs
        rw [PExp.toLin_eval]
        exact hcs g hg
    · intro s t n _ he y hy
      cases he with
      | atom h =>
        obtain ⟨v, rfl, _⟩ := h
        simp only [writes, List.mem_singleton] at hy
        simp [Function.update, hy]
  | seq c₁ mid B₁ B₂ c₂ ih₁ ih₂ =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨h₁, h₂⟩, hB⟩ := h
    have H₁ := ih₁ _ _ _ h₁ ρ
    have H₂ := ih₂ _ _ _ h₂ ρ
    refine ⟨valid_conseq (fun _ h => h) (valid_seq H₁.1 H₂.1)
      (by simpa using SB.le_eval hB ρ) (fun _ h => h), ?_⟩
    intro s t n hP he x hx
    simp only [writes, List.mem_append, not_or] at hx
    cases he with
    | seq e₁ e₂ =>
      have hm := (H₁.1 s hP).2 _ _ e₁
      rw [H₂.2 _ _ _ hm e₂ x hx.2, H₁.2 _ _ _ hP e₁ x hx.1]
  | ite w g B₁ B₂ c₁ c₂ ih₁ ih₂ =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h₁, h₂⟩, hB₁⟩, hB₂⟩ := h
    have H₁ := ih₁ _ _ _ h₁ ρ
    have H₂ := ih₂ _ _ _ h₂ ρ
    have pre₁ : ∀ s, holds P ρ s → decide (g.eval s ≤ 0) = true → holds (g.toLin :: P) ρ s := by
      intro s hP hb
      rw [holds_cons, PExp.toLin_eval]
      exact ⟨by simpa using hb, hP⟩
    have pre₂ : ∀ s, holds P ρ s → decide (g.eval s ≤ 0) = false → holds (g.negLin :: P) ρ s := by
      intro s hP hb
      rw [holds_cons, PExp.negLin_eval]
      have : 0 < g.eval s := by simpa using hb
      exact ⟨by omega, hP⟩
    refine ⟨?_, ?_⟩
    · have e₁ := SB.le_eval hB₁ ρ
      have e₂ := SB.le_eval hB₂ ρ
      simp only [SB.eval_add, SB.eval_const] at e₁ e₂
      have hm : w + max (B₁.eval ρ) (B₂.eval ρ) ≤ B.eval ρ := by
        rcases le_total (B₁.eval ρ) (B₂.eval ρ) with h | h
        · rw [max_eq_right h]; exact e₂
        · rw [max_eq_left h]; exact e₁
      refine valid_conseq (fun _ h => h) (valid_ite ?_ ?_) hm (fun _ h => h)
      · exact valid_conseq (fun s hs => pre₁ s hs.1 hs.2) H₁.1 (le_refl _) (fun _ h => h)
      · exact valid_conseq (fun s hs => pre₂ s hs.1 hs.2) H₂.1 (le_refl _) (fun _ h => h)
    · intro s t n hP he x hx
      simp only [writes, List.mem_append, not_or] at hx
      cases he with
      | iteTrue hb e => exact H₁.2 _ _ _ (pre₁ s hP hb) e x hx.1
      | iteFalse hb e => exact H₂.2 _ _ _ (pre₂ s hP hb) e x hx.2
  | «while» w g inv pot d k kl j posCert Wb body ih =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hd, rfl⟩, rfl⟩, hinv⟩, hpos⟩, hbody⟩, hB⟩ := h
    have hGj : [g.toLin].all (fun e => decide (coeff e.lv j = 0)) = true := by
      simp [PExp.toLin, coeff]
    have hG : ∀ s, decide (g.eval s ≤ 0) = true → holds [g.toLin] ρ s := fun s hb => by
      rw [holds_cons, PExp.toLin_eval]; exact ⟨by simpa using hb, fun e he => by cases he⟩
    have hQ : ∀ t, holds inv ρ t → decide (g.eval t ≤ 0) = false → holds (g.negLin :: inv) ρ t :=
      fun t hI hb => by
        rw [holds_cons, PExp.negLin_eval]
        have : 0 < g.eval t := by simpa using hb
        exact ⟨by omega, hI⟩
    simp only [loopOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hB
    rcases hB with ⟨hWj, hB⟩ | hB
    · exact loop_sound (G := [g.toLin]) (M := writes fs body) ρ hd hinv hWj hG
        hGj hpos (fun ρ' => ih _ _ _ hbody ρ') hB hQ
    · exact triloop_sound (G := [g.toLin]) (M := writes fs body) ρ hd hinv hG
        hGj hpos (fun ρ' => ih _ _ _ hbody ρ') hB hQ
  | whileAnd w gs inv pot d k kl j posCert Wb body ih =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hd, rfl⟩, rfl⟩, hinv⟩, hpos⟩, hbody⟩, hB⟩ := h
    have hGj : (gs.map PExp.toLin).all (fun e => decide (coeff e.lv j = 0)) = true := by
      simp [List.all_map, PExp.toLin, coeff]
    have hG : ∀ s, gs.all (fun e => decide (e.eval s ≤ 0)) = true →
        holds (gs.map PExp.toLin) ρ s := fun s hs e he => by
      simp only [List.all_eq_true, decide_eq_true_eq] at hs
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
      rw [PExp.toLin_eval]
      exact hs g hg
    simp only [loopOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hB
    rcases hB with ⟨hWj, hB⟩ | hB
    · exact loop_sound (G := gs.map PExp.toLin) (M := writes fs body) ρ hd hinv hWj hG
        hGj hpos (fun ρ' => ih _ _ _ hbody ρ') hB (fun t hI _ => hI)
    · exact triloop_sound (G := gs.map PExp.toLin) (M := writes fs body) ρ hd hinv hG
        hGj hpos (fun ρ' => ih _ _ _ hbody ρ') hB (fun t hI _ => hI)
  | whileLog w gs inv pot b k j posCert Wb body ih =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hb, rfl⟩, rfl⟩, hinv⟩, hWc⟩, hpos⟩, hbody⟩, hB⟩ := h
    have hGj : (gs.map PExp.toLin).all (fun e => decide (coeff e.lv j = 0)) = true := by
      simp [List.all_map, PExp.toLin, coeff]
    have H := logloop_sound (Φ := Φ) (w := w) (test := fun s => gs.all (fun e => decide (e.eval s ≤ 0)))
      (body := body.toCmd) (G := gs.map PExp.toLin) (M := writes fs body) (k := k) ρ hb hinv hWc
      (fun s hs e he => by
        simp only [List.all_eq_true, decide_eq_true_eq] at hs
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
        rw [PExp.toLin_eval]
        exact hs g hg)
      hGj hpos (fun ρ' => ih _ _ _ hbody ρ')
      (Qe := logExit gs inv)
      (fun t hI hbt => by
        unfold logExit
        split
        · next g =>
          rw [holds_cons, PExp.negLin_eval]
          simp at hbt
          exact ⟨by omega, hI⟩
        · exact hI)
    exact ⟨valid_conseq (fun s hs => hs) H.1 (by
        have := SB.le_eval hB ρ
        simpa [SB.eval, SB.const, dotN] using this) (fun _ h => h), H.2⟩
  | whileGrow w gs inv pot b K j capCert Wb body ih =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hb, rfl⟩, rfl⟩, hinv⟩, hWc⟩, hcap⟩, hbody⟩, hB⟩ := h
    have hGj : (gs.map PExp.toLin).all (fun e => decide (coeff e.lv j = 0)) = true := by
      simp [List.all_map, PExp.toLin, coeff]
    have H := growloop_sound (Φ := Φ) (w := w) (test := fun s => gs.all (fun e => decide (e.eval s ≤ 0)))
      (body := body.toCmd) (G := gs.map PExp.toLin) (M := writes fs body) (K := K) ρ hb hinv hWc
      (fun s hs e he => by
        simp only [List.all_eq_true, decide_eq_true_eq] at hs
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
        rw [PExp.toLin_eval]
        exact hs g hg)
      hGj hcap (fun ρ' => ih _ _ _ hbody ρ')
      (Qe := logExit gs inv)
      (fun t hI hbt => by
        unfold logExit
        split
        · next g =>
          rw [holds_cons, PExp.negLin_eval]
          simp at hbt
          exact ⟨by omega, hI⟩
        · exact hI)
    exact ⟨valid_conseq (fun s hs => hs) H.1 (by
        have := SB.le_eval hB ρ
        simpa [SB.eval, SB.const, dotN] using this) (fun _ h => h), H.2⟩
  | weaken P' preCerts B' Q' postCerts c ih =>
    intro P Q B h ρ
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hpre, hc⟩, hB⟩, hpost⟩ := h
    have H := ih _ _ _ hc ρ
    exact ⟨valid_conseq (fun s hs => entailsAll_sound hpre hs) H.1 (SB.le_eval hB ρ)
      (fun t ht => entailsAll_sound hpost ht),
      fun s t n hP he x hx => H.2 s t n (entailsAll_sound hpre hP) he x hx⟩
  | dead cert c _ =>
    intro P Q B h ρ
    simp only [check] at h
    have hF : ∀ s, holds P ρ s → False := by
      intro s hs
      have := entails1_sound h hs
      simp [Lin.eval, dot] at this
    exact ⟨valid_conseq (P := fun _ => False) hF (valid_unreachable _ _ _) (le_refl _)
      (fun _ hq => hq), fun s _ _ hs => (hF s hs).elim⟩
  | call w f inst preCerts ubs ubCerts =>
    intro P Q B h ρ
    simp only [check] at h
    cases hF : fs[f]? with
    | none => simp [hF] at h
    | some F =>
      simp only [hF, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨hpre, hlen⟩, hlen'⟩, hub⟩, hB⟩, rfl⟩ := h
      obtain ⟨hV, hfr⟩ := hfs f F hF
      have pre_at : ∀ s, holds P ρ s → holds F.pre (instEnv inst s) s := by
        intro s hs e he
        have := entailsAll_sound hpre hs (e.inst inst) (List.mem_map_of_mem _ he)
        rwa [Lin.inst_eval] at this
      have bound_at : ∀ s, holds P ρ s → w + F.bound.eval (instEnv inst s) ≤ B.eval ρ := by
        intro s hs
        have hu := entailsAll_sound hub hs
        have hc := SB.comb_ge F.bound.co ubs ρ (instEnv inst s) hlen (fun i hi =>
          ubGoals_sound hu i (by omega) (by omega))
        have := SB.le_eval hB ρ
        simp only [callBound, SB.eval_add, SB.eval_const] at this
        have e : F.bound.eval (instEnv inst s) = F.bound.c + dotN F.bound.co (instEnv inst s) := rfl
        omega
      refine ⟨?_, ?_⟩
      · intro s hs
        have Hc := valid_call (w := w) (hV (instEnv inst s))
        refine ⟨fun n hn => le_trans ((Hc s (pre_at s hs)).1 n hn) (bound_at s hs),
          fun t n he => ?_⟩
        cases he with
        | call e => exact holds_frameOf hs (hfr _ s t _ (pre_at s hs) e)
      · intro s t n hs he x hx
        simp only [writes, hF] at hx
        cases he with
        | call e => exact hfr _ s t _ (pre_at s hs) e x hx

/-- **What an accepted certificate guarantees.** Every execution of the program from a
    state satisfying the precondition, terminated or not, costs at most `B`. -/
theorem certified_cost_le {P Q : List Lin} {c : ACmd} {B : SB}
    (h : check [] P c B Q = true) (Φ : ℕ → Cmd ℕ Env)
    {ρ s : Env} (hP : holds P ρ s) {n : ℕ} (hp : Pre Φ c.toCmd s n) : n ≤ B.eval ρ :=
  ((check_sound [] Φ (fun f F h => by simp at h) c P Q B h ρ).1 s hP).1 n hp

/-- **Soundness of a program certificate.** Let `Φ` run each function with a body as that
    body, and let every contract (function without a body) meet its specification. If
    `checkProgram fs` holds, every function meets its specification: its cost is bounded
    by its symbolic bound, for every call that satisfies its precondition. -/
theorem program_sound (fs : List FunCert) (h : checkProgram fs = true) (Φ : ℕ → Cmd ℕ Env)
    (hbody : ∀ i F b, fs[i]? = some F → F.body = some b → Φ i = b.toCmd)
    (hcontract : ∀ i F, fs[i]? = some F → F.body = none → FunSpec Φ i F) :
    ∀ i F, fs[i]? = some F → FunSpec Φ i F := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro F hF
    cases hb : F.body with
    | none => exact hcontract i F hF hb
    | some b =>
      have hi : i < fs.length := by
        rcases Nat.lt_or_ge i fs.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at hF; cases hF
      have hc : checkFun (fs.take i) F = true := by
        simp only [checkProgram, List.all_eq_true, List.mem_range] at h
        have := h i hi
        rwa [hF] at this
      simp only [checkFun, hb, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hc
      obtain ⟨hchk, hmods⟩ := hc
      have hfs : ∀ f G, (fs.take i)[f]? = some G → FunSpec Φ f G := by
        intro f G hG
        have hf : f < i := by
          rcases Nat.lt_or_ge f i with h' | h'
          · exact h'
          · rw [List.getElem?_take, if_neg (Nat.not_lt.mpr h')] at hG; cases hG
        rw [List.getElem?_take, if_pos hf] at hG
        exact ih f hf G hG
      have H := check_sound (fs.take i) Φ hfs b F.pre F.post F.bound hchk
      unfold FunSpec
      rw [hbody i F b hF hb]
      exact ⟨fun ρ => (H ρ).1, fun ρ s t n hs he x hx =>
        (H ρ).2 s t n hs he x (fun hw => hx (by simpa using hmods x hw))⟩

/-! ### An example logarithmic loop -/

/-- `while (n >= 1) n := 0` read as a logarithmic loop: `n ≤ 1000` on entry, base 2, so
    at most `⌊log₂ 1000⌋ + 1 = 10` iterations, bound `10·(1 + 1) + 1 = 21`. The body proves
    `2·n ≤ γ₀` after it from `n ≤ γ₀`, `n ≥ 1` before it. -/
def logCert : ACmd :=
  .whileLog 1 [⟨[-1], 1⟩] [] ⟨[1], 0⟩ 2 1000 0 (1, [1]) (SB.const 1)
    (.weaken [⟨[0], [-1], 1⟩, ⟨[0], [], 0⟩] [(1, [1, 1]), (1, [0, 0])] (SB.const 1)
      [⟨[], [-1], 1⟩, ⟨[1], [], 0⟩] [(1, [1, 2])]
      (.assign 1 0 ⟨[], 0⟩))

theorem logCert_checks :
    check [] [⟨[1], [], -1000⟩] logCert (SB.const 21) [⟨[1], [], 0⟩] = true := by decide

/-- With the bound 20, one less than `10·2 + 1`, the certificate is rejected. -/
theorem logCert_rejected :
    check [] [⟨[1], [], -1000⟩] logCert (SB.const 20) [⟨[1], [], 0⟩] = false := by decide

/-- A base of 1 is rejected (no division). -/
theorem logCert_base1_rejected :
    check [] [⟨[1], [], -1000⟩]
      (.whileLog 1 [⟨[-1], 1⟩] [] ⟨[1], 0⟩ 1 1000 0 (1, [1]) (SB.const 1) (.assign 1 0 ⟨[], 0⟩))
      (SB.const 100000) [⟨[1], [], 0⟩] = false := by decide

/-- What the accepted certificate gives, for every procedure environment. -/
theorem logCert_cost (Φ : ℕ → Cmd ℕ Env) {s : Env} (hs : s 0 ≤ 1000) {n : ℕ}
    (hp : Pre Φ logCert.toCmd s n) : n ≤ 21 := by
  have := certified_cost_le logCert_checks Φ (ρ := fun _ => 0) (s := s) (by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    simp [Lin.eval, dot]
    omega) hp
  simpa [SB.eval, SB.const, dotN] using this

/-- `while (len ≤ 100) len := 2·len` from `len ≥ 1`: a growing potential, base 2, at most
    `⌊log₂ 100⌋ + 1 = 7` iterations (from `len = 1`: 1, 2, …, 64), bound `7·2 + 1 = 15`. -/
def growCert : ACmd :=
  .whileGrow 1 [⟨[1], -100⟩] [] ⟨[1], 0⟩ 2 100 0 (1, [1]) (SB.const 1)
    (.weaken [⟨[-2], [2], 0⟩] [(1, [2, 0, 0])] (SB.const 1) [⟨[-1], [2], 0⟩] [(1, [1])]
      (.assign 1 0 ⟨[2], 0⟩))

theorem growCert_checks :
    check [] [⟨[-1], [], 1⟩] growCert (SB.const 15) [⟨[-1], [], 101⟩] = true := by decide

/-- One less than the bound is rejected. -/
theorem growCert_rejected :
    check [] [⟨[-1], [], 1⟩] growCert (SB.const 14) [⟨[-1], [], 101⟩] = false := by decide

/-- Without `len ≥ 1` on entry (`len` could be 0 and never grow), it is rejected. -/
theorem growCert_needs_entry :
    check [] [] growCert (SB.const 15) [⟨[-1], [], 101⟩] = false := by decide

theorem growCert_cost (Φ : ℕ → Cmd ℕ Env) {s : Env} (hs : 1 ≤ s 0) {n : ℕ}
    (hp : Pre Φ growCert.toCmd s n) : n ≤ 15 := by
  have := certified_cost_le growCert_checks Φ (ρ := fun _ => 0) (s := s) (by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    simp [Lin.eval, dot]
    omega) hp
  simpa [SB.eval, SB.const, dotN] using this

/-! ### An example certificate -/

/-- Variables: `x₀ = i`, `x₁ = n`. The program is `while (i < n) i := i + 1`, with unit
    weights; the guard `i < n` is `i - n + 1 ≤ 0`. Certificate: no invariant, potential
    `n - i` decreasing by `1`, at most `10` on entry. -/
def countCert : ACmd :=
  .weaken [⟨[-1, 1], [], -10⟩] [(1, [0, 1, 1])] (SB.const 21) [⟨[-1, 1], [], 0⟩] [(1, [1])]
    (.while 1 ⟨[1, -1], 1⟩ [] ⟨[-1, 1], 0⟩ 1 10 [] 0 (1, [1]) (SB.const 1)
      (.weaken [⟨[-1, 1], [-1], 0⟩] [(1, [1, 0])] (SB.const 1) [⟨[-1, 1], [-1], 1⟩] [(1, [1])]
        (.assign 1 0 ⟨[1], 1⟩)))

/-- Precondition `i ≤ 0`, `-i ≤ 0`, `n - 10 ≤ 0`; postcondition `n - i ≤ 0`. -/
theorem countCert_checks :
    check [] [⟨[1], [], 0⟩, ⟨[-1], [], 0⟩, ⟨[0, 1], [], -10⟩] countCert (SB.const 21)
      [⟨[-1, 1], [], 0⟩] = true := by
  decide

/-- Hence the loop costs at most `21` from `i = 0`, `n ≤ 10`, by the checker alone. -/
theorem countCert_cost (s : Env) (h0 : s 0 = 0) (h1 : s 1 ≤ 10) (n : ℕ)
    (hp : Pre (fun _ => Cmd.skip) countCert.toCmd s n) : n ≤ 21 := by
  have := certified_cost_le countCert_checks (fun _ => Cmd.skip) (ρ := fun _ => 0) ?_ hp
  · simpa using this
  intro e he
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp [Lin.eval, dot] <;> omega

/-! ### An amortised (triangular) loop nest -/

/-- The certificate the plugin emits for
    `for (i = 0; i < 4; i++) for (j = i; j < 4; j++) {}` (variables `x₂ = i`, `x₃ = j`),
    with the bound `b` claimed for the outer loop. The inner loop's entry bound is `γ₀`
    (the outer potential `4 - i`), so the outer body costs `5 + 4·γ₀` and the outer loop
    is bounded by `triOk`: `4·(2 + 5) + 4·(4·4 - 4·3/2) + 2 = 70`, where a body bound
    that ignores `i` gives `4·(2 + 5 + 4·4) + 2 = 94`. -/
def triCertAt (b : ℕ) : ACmd :=
  (.weaken [] [] (SB.const (b + 1)) [⟨[0, 0, -1], [], 4⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [],
  -4⟩] [] (.seq (.seq (.weaken [] [] (SB.const 0) [] [] (.havoc 0 2)) [] (SB.const 0) (SB.const 0)
  (.weaken [] [] (SB.const 0) [] [] (.havoc 0 3))) [] (SB.const 0) (SB.const (b + 1)) (.seq
  (.weaken [⟨[0, 0, 0], [], 0⟩, ⟨[0, 0, 0], [], 0⟩] [(1, []), (1, [])] (SB.const 1) [⟨[0, 0, 1],
  [], 0⟩, ⟨[0, 0, -1], [], 0⟩] [(1, [1, 0]), (1, [0, 1])] (.assign 1 2 ⟨[], 0⟩)) [⟨[0, 0, 1], [],
  0⟩, ⟨[0, 0, -1], [], 0⟩] (SB.const 1) (SB.const b) (.seq .skip [⟨[0, 0, 1], [], 0⟩, ⟨[0, 0, -1],
  [], 0⟩] (SB.const 0) (SB.const b) (.weaken [⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0,
  1], [], -4⟩] [(1, [0, 1]), (1, [0, 1]), (1, [1, 0])] (SB.const b) [⟨[0, 0, -1], [], 4⟩, ⟨[0, 0,
  -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩] [(1, [1, 0, 0]), (1, [0, 1, 0]), (1, [0, 0, 1])] (.while 2
  ⟨[0, 0, 1], -3⟩ [⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩] ⟨[0, 0, -1], 4⟩ 1 (4) [] 0 (1, [1, 0,
  0]) ⟨5, [4]⟩ (.weaken [⟨[0, 0, -1], [-1], 4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0,
  1], [], -4⟩] [(1, [1, 0, 0, 0]), (1, [0, 1, 0, 0]), (1, [0, 0, 1, 0]), (1, [0, 0, 0, 1])] ⟨5,
  [4]⟩ [⟨[0, 0, 0, -1], [], 4⟩, ⟨[0, 0, -1], [-1], 5⟩, ⟨[0, 0, 1], [], -4⟩, ⟨[0, 0, -1], [], 1⟩,
  ⟨[0, 0, 1], [], -5⟩, ⟨[0, 0, 1, -1], [], -1⟩, ⟨[0, 0, 0, 1], [], -4⟩] [(1, [0, 1, 0, 0, 0, 0,
  0]), (1, [0, 0, 0, 1, 0, 0, 0]), (1, [0, 0, 1, 0, 0, 0, 0])] (.seq (.seq .skip [⟨[0, 0, -1],
  [-1], 4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩] (SB.const 0) ⟨3, [4]⟩
  (.seq (.weaken [⟨[0, 0, -1, 0], [-1], 4⟩, ⟨[0, 0, 1, 0], [], -3⟩, ⟨[0, 0, -1, 0], [], 0⟩, ⟨[0,
  0, 1, 0], [], -4⟩, ⟨[0, 0, 0, 0], [], 0⟩, ⟨[0, 0, 0, 0], [], 0⟩] [(1, [1, 0, 0, 0]), (1, [0, 1,
  0, 0]), (1, [0, 0, 1, 0]), (1, [0, 0, 0, 1]), (1, [0, 0, 0, 0]), (1, [0, 0, 0, 0])] (SB.const 1)
  [⟨[0, 0, -1], [-1], 4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩, ⟨[0, 0,
  -1, 1], [], 0⟩, ⟨[0, 0, 1, -1], [], 0⟩] [(1, [1, 0, 0, 0, 0, 0]), (1, [0, 1, 0, 0, 0, 0]), (1,
  [0, 0, 1, 0, 0, 0]), (1, [0, 0, 0, 1, 0, 0]), (1, [0, 0, 0, 0, 1, 0]), (1, [0, 0, 0, 0, 0, 1])]
  (.assign 1 3 ⟨[0, 0, 1], 0⟩)) [⟨[0, 0, -1], [-1], 4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩,
  ⟨[0, 0, 1], [], -4⟩, ⟨[0, 0, -1, 1], [], 0⟩, ⟨[0, 0, 1, -1], [], 0⟩] (SB.const 1) ⟨2, [4]⟩ (.seq
  .skip [⟨[0, 0, -1], [-1], 4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩,
  ⟨[0, 0, -1, 1], [], 0⟩, ⟨[0, 0, 1, -1], [], 0⟩] (SB.const 0) ⟨2, [4]⟩ (.weaken [⟨[0, 0, 0, -1],
  [-1], 4⟩, ⟨[0, 0, -1], [-1], 4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩,
  ⟨[0, 0, 1, -1], [], 0⟩, ⟨[0, 0, 0, 1], [], -4⟩] [(1, [1, 0, 0, 0, 0, 1]), (1, [1, 0, 0, 0, 0,
  0]), (1, [0, 1, 0, 0, 0, 0]), (1, [0, 0, 1, 0, 0, 0]), (1, [0, 0, 0, 1, 0, 0]), (1, [0, 0, 0, 0,
  0, 1]), (1, [0, 0, 0, 1, 1, 0])] ⟨2, [4]⟩ [⟨[0, 0, 0, -1], [], 4⟩, ⟨[0, 0, -1], [-1], 4⟩, ⟨[0,
  0, 1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩, ⟨[0, 0, 1, -1], [], 0⟩, ⟨[0, 0, 0, 1],
  [], -4⟩] [(1, [1, 0, 0, 0, 0, 0, 0]), (1, [0, 1, 0, 0, 0, 0, 0]), (1, [0, 0, 1, 0, 0, 0, 0]),
  (1, [0, 0, 0, 1, 0, 0, 0]), (1, [0, 0, 0, 0, 1, 0, 0]), (1, [0, 0, 0, 0, 0, 1, 0]), (1, [0, 0,
  0, 0, 0, 0, 1])] (.while 2 ⟨[0, 0, 0, 1], -3⟩ [⟨[0, 0, -1], [-1], 4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0,
  0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩, ⟨[0, 0, 1, -1], [], 0⟩, ⟨[0, 0, 0, 1], [], -4⟩] ⟨[0, 0, 0,
  -1], 4⟩ 1 (0) [1] 1 (1, [1, 0, 0, 0, 0, 0, 0]) (SB.const 2) (.weaken [⟨[0, 0, 0, -1], [0, -1],
  4⟩, ⟨[0, 0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [-1], 4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩,
  ⟨[0, 0, 1], [], -4⟩, ⟨[0, 0, 1, -1], [], 0⟩, ⟨[0, 0, 0, 1], [], -4⟩] [(1, [1, 0, 0, 0, 0, 0, 0,
  0]), (1, [0, 1, 0, 0, 0, 0, 0, 0]), (1, [0, 0, 1, 0, 0, 0, 0, 0]), (1, [0, 0, 0, 1, 0, 0, 0,
  0]), (1, [0, 0, 0, 0, 1, 0, 0, 0]), (1, [0, 0, 0, 0, 0, 1, 0, 0]), (1, [0, 0, 0, 0, 0, 0, 1,
  0]), (1, [0, 0, 0, 0, 0, 0, 0, 1])] (SB.const 2) [⟨[0, 0, 0, -1], [0, -1], 5⟩, ⟨[0, 0, 0, 1],
  [], -4⟩, ⟨[0, 0, -1], [-1], 4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩,
  ⟨[0, 0, 1, -1], [], 1⟩, ⟨[0, 0, 0, 1], [], -5⟩] [(1, [1, 0, 0, 0, 0, 0, 0, 0]), (1, [0, 0, 1, 0,
  0, 0, 0, 0]), (1, [0, 0, 0, 1, 0, 0, 0, 0]), (1, [0, 0, 0, 0, 1, 0, 0, 0]), (1, [0, 0, 0, 0, 0,
  1, 0, 0]), (1, [0, 0, 0, 0, 0, 0, 1, 0]), (1, [0, 1, 0, 0, 0, 0, 0, 0])] (.seq (.seq .skip [⟨[0,
  0, 0, -1], [0, -1], 4⟩, ⟨[0, 0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [-1], 4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0,
  0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩, ⟨[0, 0, 1, -1], [], 0⟩, ⟨[0, 0, 0, 1], [], -4⟩] (SB.const
  0) (SB.const 0) .skip) [⟨[0, 0, 0, -1], [0, -1], 4⟩, ⟨[0, 0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [-1],
  4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩, ⟨[0, 0, 1, -1], [], 0⟩, ⟨[0,
  0, 0, 1], [], -4⟩] (SB.const 0) (SB.const 2) (.weaken [⟨[0, 0, 0, -1], [0, -1], 4⟩, ⟨[0, 0, 0,
  1], [], -3⟩, ⟨[0, 0, -1, 0], [-1], 4⟩, ⟨[0, 0, 1, 0], [], -3⟩, ⟨[0, 0, -1, 0], [], 0⟩, ⟨[0, 0,
  1, 0], [], -4⟩, ⟨[0, 0, 1, -1], [], 0⟩, ⟨[0, 0, 0, 1], [], -4⟩] [(1, [1, 0, 0, 0, 0, 0, 0, 0]),
  (1, [0, 1, 0, 0, 0, 0, 0, 0]), (1, [0, 0, 1, 0, 0, 0, 0, 0]), (1, [0, 0, 0, 1, 0, 0, 0, 0]), (1,
  [0, 0, 0, 0, 1, 0, 0, 0]), (1, [0, 0, 0, 0, 0, 1, 0, 0]), (1, [0, 0, 0, 0, 0, 0, 1, 0]), (1, [0,
  0, 0, 0, 0, 0, 0, 1])] (SB.const 2) [⟨[0, 0, 0, -1], [0, -1], 5⟩, ⟨[0, 0, 0, 1], [], -4⟩, ⟨[0,
  0, -1], [-1], 4⟩, ⟨[0, 0, 1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩, ⟨[0, 0, 1, -1],
  [], 1⟩, ⟨[0, 0, 0, 1], [], -5⟩] [(1, [1, 0, 0, 0, 0, 0, 0, 0]), (1, [0, 1, 0, 0, 0, 0, 0, 0]),
  (1, [0, 0, 1, 0, 0, 0, 0, 0]), (1, [0, 0, 0, 1, 0, 0, 0, 0]), (1, [0, 0, 0, 0, 1, 0, 0, 0]), (1,
  [0, 0, 0, 0, 0, 1, 0, 0]), (1, [0, 0, 0, 0, 0, 0, 1, 0]), (1, [0, 0, 0, 0, 0, 0, 0, 1])]
  (.assign 2 3 ⟨[0, 0, 0, 1], 1⟩))))))))) [⟨[0, 0, 0, -1], [], 4⟩, ⟨[0, 0, -1], [-1], 4⟩, ⟨[0, 0,
  1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩, ⟨[0, 0, 1, -1], [], 0⟩, ⟨[0, 0, 0, 1],
  [], -4⟩] ⟨3, [4]⟩ (SB.const 2) (.weaken [⟨[0, 0, 0, -1], [], 4⟩, ⟨[0, 0, -1], [-1], 4⟩, ⟨[0, 0,
  1], [], -3⟩, ⟨[0, 0, -1], [], 0⟩, ⟨[0, 0, 1], [], -4⟩, ⟨[0, 0, 1, -1], [], 0⟩, ⟨[0, 0, 0, 1],
  [], -4⟩] [(1, [1, 0, 0, 0, 0, 0, 0]), (1, [0, 1, 0, 0, 0, 0, 0]), (1, [0, 0, 1, 0, 0, 0, 0]),
  (1, [0, 0, 0, 1, 0, 0, 0]), (1, [0, 0, 0, 0, 1, 0, 0]), (1, [0, 0, 0, 0, 0, 1, 0]), (1, [0, 0,
  0, 0, 0, 0, 1])] (SB.const 2) [⟨[0, 0, 0, -1], [], 4⟩, ⟨[0, 0, -1], [-1], 5⟩, ⟨[0, 0, 1], [],
  -4⟩, ⟨[0, 0, -1], [], 1⟩, ⟨[0, 0, 1], [], -5⟩, ⟨[0, 0, 1, -1], [], -1⟩, ⟨[0, 0, 0, 1], [], -4⟩]
  [(1, [1, 0, 0, 0, 0, 0, 0]), (1, [0, 1, 0, 0, 0, 0, 0]), (1, [0, 0, 1, 0, 0, 0, 0]), (1, [0, 0,
  0, 1, 0, 0, 0]), (1, [0, 0, 0, 0, 1, 0, 0]), (1, [0, 0, 0, 0, 0, 1, 0]), (1, [0, 0, 0, 0, 0, 0,
  1])] (.assign 2 2 ⟨[0, 0, 1], 1⟩))))))))))

set_option maxRecDepth 100000 in
theorem triCert_checks : check [] [] (triCertAt 70) (SB.const 71) [] = true := by decide

set_option maxRecDepth 100000 in
/-- The amortised bound is the least the checker accepts for this nest. -/
theorem triCert_69_rejected : check [] [] (triCertAt 69) (SB.const 70) [] = false := by decide

/-- Hence the nest costs at most `71` from any state, by the checker alone. -/
theorem triCert_cost (s : Env) (n : ℕ)
    (hp : Pre (fun _ => Cmd.skip) (triCertAt 70).toCmd s n) : n ≤ 71 := by
  have := certified_cost_le triCert_checks (fun _ => Cmd.skip) (ρ := fun _ => 0) (by simp [holds]) hp
  simpa using this

/-! ### A constrained unknown value -/

/-- `x₁ := x₀ >> 2` for `x₀ ≥ 0`, modelled as an unknown value with `4 x₁ ≤ x₀ ≤ 4 x₁ + 3`. -/
theorem shiftCert_checks :
    check [] [⟨[-1], [], 0⟩] (.havocC 1 1 [⟨[-1, 4], 0⟩, ⟨[1, -4], -3⟩]) (SB.const 1)
      [⟨[-1], [], 0⟩, ⟨[-1, 4], [], 0⟩, ⟨[1, -4], [], -3⟩] = true := by decide

/-- A precondition that mentions the assigned variable is not carried over. -/
theorem shiftCert_rejected :
    check [] [⟨[0, 1], [], 0⟩] (.havocC 1 1 [⟨[-1, 4], 0⟩]) (SB.const 1)
      [⟨[0, 1], [], 0⟩, ⟨[-1, 4], [], 0⟩] = false := by decide

/-! ### A symbolic bound and a call -/

/-- The loop `while (i < n) i := i + 1` again, with a **symbolic** bound: the precondition
    `i = 0`, `n ≤ γ₀` (γ₀ is the value of the parameter `n`), the entry bound of the
    potential `n - i` is `0 + 1·γ₀`, and the bound is `1 + 2·max 0 γ₀`. -/
def countSym : ACmd :=
  .weaken [⟨[-1, 1], [-1], 0⟩] [(1, [0, 1, 1])] ⟨1, [2]⟩ [⟨[-1, 1], [], 0⟩] []
    (.while 1 ⟨[1, -1], 1⟩ [] ⟨[-1, 1], 0⟩ 1 0 [1] 1 (1, [1]) (SB.const 1)
      (.weaken [⟨[-1, 1], [0, -1], 0⟩] [(1, [1, 0])] (SB.const 1) [⟨[-1, 1], [0, -1], 1⟩] [(1, [1])]
        (.assign 1 0 ⟨[1], 1⟩)))

def countPre : List Lin := [⟨[1], [], 0⟩, ⟨[-1], [], 0⟩, ⟨[0, 1], [-1], 0⟩]

theorem countSym_checks : check [] countPre countSym ⟨1, [2]⟩ [] = true := by decide

/-- From `i = 0`, the loop costs at most `1 + 2·max 0 n`, for every `n`. -/
theorem countSym_cost (s : Env) (h0 : s 0 = 0) (n : ℕ)
    (hp : Pre (fun _ => Cmd.skip) countSym.toCmd s n) : n ≤ 1 + 2 * (s 1).toNat := by
  have := certified_cost_le countSym_checks (fun _ => Cmd.skip) (ρ := fun _ => s 1) ?_ hp
  · simpa [SB.eval, dotN] using this
  intro e he
  simp only [countPre, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp [Lin.eval, dot] <;> omega

/-- The function `count` (variables `x₀ = i`, `x₁ = n`): it may modify `i`. -/
def countF : FunCert := ⟨countPre, ⟨1, [2]⟩, [], [0], some countSym⟩

/-- `main`: `n := 7; i := 0; count()`. The call instantiates `γ₀` by `n` and bounds it by
    `7`; the call costs `1 + (1 + 2·7) = 16` and `main` `18`, without inlining `count`. -/
def mainBody : ACmd :=
  .seq (.weaken [⟨[0, 0], [], 0⟩, ⟨[0, 0], [], 0⟩] [(1, []), (1, [])] (SB.const 1)
          [⟨[0, 1], [], -7⟩, ⟨[0, -1], [], 7⟩] [(1, [1, 0]), (1, [0, 1])]
          (.assign 1 1 ⟨[], 7⟩))
    [⟨[0, 1], [], -7⟩, ⟨[0, -1], [], 7⟩] (SB.const 1) ⟨17, []⟩
    (.seq (.weaken [⟨[0], [], 0⟩, ⟨[0], [], 0⟩, ⟨[0, 1], [], -7⟩, ⟨[0, -1], [], 7⟩]
            [(1, []), (1, []), (1, [1, 0]), (1, [0, 1])] (SB.const 1)
            [⟨[1], [], 0⟩, ⟨[-1], [], 0⟩, ⟨[0, 1], [], -7⟩, ⟨[0, -1], [], 7⟩]
            [(1, [1, 0, 0, 0]), (1, [0, 1, 0, 0]), (1, [0, 0, 1, 0]), (1, [0, 0, 0, 1])]
            (.assign 1 0 ⟨[], 0⟩))
      [⟨[1], [], 0⟩, ⟨[-1], [], 0⟩, ⟨[0, 1], [], -7⟩, ⟨[0, -1], [], 7⟩] (SB.const 1) ⟨16, []⟩
      (.weaken [⟨[1], [], 0⟩, ⟨[-1], [], 0⟩, ⟨[0, 1], [], -7⟩, ⟨[0, -1], [], 7⟩]
          [(1, [1, 0, 0, 0]), (1, [0, 1, 0, 0]), (1, [0, 0, 1, 0]), (1, [0, 0, 0, 1])]
          ⟨16, []⟩ [⟨[0, 1], [], -7⟩, ⟨[0, -1], [], 7⟩] []
        (.call 1 0 [⟨[0, 1], 0⟩] [(1, [1, 0, 0, 0]), (1, [0, 1, 0, 0]), (1, [])] [⟨7, []⟩]
          [(1, [0, 0, 1, 0])])))

def mainF : FunCert := ⟨[], ⟨18, []⟩, [], [0, 1], some mainBody⟩

theorem exProgram_checks : checkProgram [countF, mainF] = true := by decide

/-- The same program with the bound `17` for `main` is rejected. -/
theorem exProgram_17_rejected :
    checkProgram [countF, ⟨[], ⟨17, []⟩, [], [0, 1], some mainBody⟩] = false := by decide

/-- The procedures of the example: function `0` is `count`, function `1` is `main`. -/
def exΦ : ℕ → Cmd ℕ Env := fun i => if i = 0 then countSym.toCmd else mainBody.toCmd

/-- Hence, by `program_sound`, every execution of `main` costs at most `18`. -/
theorem exMain_cost (s : Env) (n : ℕ) (hp : Pre exΦ (exΦ 1) s n) : n ≤ 18 := by
  have H := program_sound [countF, mainF] exProgram_checks exΦ ?_ ?_ 1 mainF rfl
  · have := ((H.1 (fun _ => 0)) s (fun e he => by simp [mainF] at he)).1 n hp
    simpa [mainF, SB.eval, dotN] using this
  · intro i F b hF hb
    match i, hF with
    | 0, hF => simp at hF; subst hF; simp [countF] at hb; subst hb; rfl
    | 1, hF => simp at hF; subst hF; simp [mainF] at hb; subst hb; rfl
  · intro i F hF hb
    match i, hF with
    | 0, hF => simp at hF; subst hF; simp [countF] at hb
    | 1, hF => simp at hF; subst hF; simp [mainF] at hb

end ImperativeOptimization.Checker
