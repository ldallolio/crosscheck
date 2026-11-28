/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic
import ImperativeOptimization.Checker
import ImperativeOptimization.MiniCCore

/-!
# Mini-C: validation of certificates against the source program

`MiniCCore` defines the fragment `MStmt`, its semantics `lower` (into the programs of the
checker, hence into `Language`), the normal form `nf` of a certificate's program and the
test `validate`. Here:

* `nf_equiv`: a program and its normal form have the same executions and execution
  prefixes, with the same costs (annotations, `weaken`, `dead`, `skip` and the nesting of
  sequences do not change the cost semantics);
* `validated_sound`: if the program certificate is accepted (`checkProgram`) and the body
  of function `i` is validated against the mini-C statement `s`, then every execution
  prefix of `s` (from a state satisfying the precondition) costs at most the function's
  bound, and every terminating execution ends in the postcondition. The generator of
  certificates is not trusted; what remains trusted is the export of the C program as
  `MStmt` (and the cost model, which is data of `MStmt`).
-/

namespace ImperativeOptimization.MiniC
open Checker

section Equiv
variable {ι S : Type} {Φ : ι → Cmd ι S}

/-- Every execution and execution prefix of `c` is one of `d`, with the same cost. -/
def CImp (Φ : ι → Cmd ι S) (c d : Cmd ι S) : Prop :=
  (∀ s t n, Exec Φ c s t n → Exec Φ d s t n) ∧ (∀ s n, Pre Φ c s n → Pre Φ d s n)

/-- Same executions and execution prefixes, with the same costs. -/
def CEquiv (Φ : ι → Cmd ι S) (c d : Cmd ι S) : Prop := CImp Φ c d ∧ CImp Φ d c

theorem CEquiv.refl (c : Cmd ι S) : CEquiv Φ c c :=
  ⟨⟨fun _ _ _ h => h, fun _ _ h => h⟩, ⟨fun _ _ _ h => h, fun _ _ h => h⟩⟩

theorem CEquiv.symm {c d : Cmd ι S} (h : CEquiv Φ c d) : CEquiv Φ d c := ⟨h.2, h.1⟩

theorem CImp.trans {c d e : Cmd ι S} (h₁ : CImp Φ c d) (h₂ : CImp Φ d e) : CImp Φ c e :=
  ⟨fun s t n h => h₂.1 s t n (h₁.1 s t n h), fun s n h => h₂.2 s n (h₁.2 s n h)⟩

theorem CEquiv.trans {c d e : Cmd ι S} (h₁ : CEquiv Φ c d) (h₂ : CEquiv Φ d e) :
    CEquiv Φ c e := ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem pre_skip {s : S} {n : ℕ} (h : Pre Φ Cmd.skip s n) : n = 0 := by
  cases h with
  | stop => rfl
  | done h => cases h; rfl

theorem CImp.seq {a a' b b' : Cmd ι S} (ha : CImp Φ a a') (hb : CImp Φ b b') :
    CImp Φ (Cmd.seq a b) (Cmd.seq a' b') := by
  have he : ∀ s t n, Exec Φ (Cmd.seq a b) s t n → Exec Φ (Cmd.seq a' b') s t n := by
    intro s t n h
    cases h with
    | seq h₁ h₂ => exact Exec.seq (ha.1 _ _ _ h₁) (hb.1 _ _ _ h₂)
  refine ⟨he, fun s n h => ?_⟩
  cases h with
  | stop => exact Pre.stop _ _
  | done h => exact Pre.done (he _ _ _ h)
  | seqLeft h => exact Pre.seqLeft (ha.2 _ _ h)
  | seqRight h₁ h₂ => exact Pre.seqRight (ha.1 _ _ _ h₁) (hb.2 _ _ h₂)

theorem CImp.ite {w : ℕ} {b : S → Bool} {c₁ c₁' c₂ c₂' : Cmd ι S}
    (h₁ : CImp Φ c₁ c₁') (h₂ : CImp Φ c₂ c₂') :
    CImp Φ (Cmd.ite w b c₁ c₂) (Cmd.ite w b c₁' c₂') := by
  have he : ∀ s t n, Exec Φ (Cmd.ite w b c₁ c₂) s t n → Exec Φ (Cmd.ite w b c₁' c₂') s t n := by
    intro s t n h
    cases h with
    | iteTrue hb h => exact Exec.iteTrue hb (h₁.1 _ _ _ h)
    | iteFalse hb h => exact Exec.iteFalse hb (h₂.1 _ _ _ h)
  refine ⟨he, fun s n h => ?_⟩
  cases h with
  | stop => exact Pre.stop _ _
  | done h => exact Pre.done (he _ _ _ h)
  | iteTrue hb h => exact Pre.iteTrue hb (h₁.2 _ _ h)
  | iteFalse hb h => exact Pre.iteFalse hb (h₂.2 _ _ h)

theorem CImp.while {w : ℕ} {b : S → Bool} {c c' : Cmd ι S} (hc : CImp Φ c c') :
    CImp Φ (Cmd.while w b c) (Cmd.while w b c') := by
  have he : ∀ s t n, Exec Φ (Cmd.while w b c) s t n → Exec Φ (Cmd.while w b c') s t n := by
    intro s t n h
    generalize hx : Cmd.while w b c = x at h
    induction h with
    | whileFalse hb => cases hx; exact Exec.whileFalse hb
    | whileTrue hb h₁ _ _ ih₂ =>
      cases hx; exact Exec.whileTrue hb (hc.1 _ _ _ h₁) (ih₂ rfl)
    | _ => cases hx
  refine ⟨he, fun s n h => ?_⟩
  generalize hx : Cmd.while w b c = x at h
  induction h with
  | stop => exact Pre.stop _ _
  | done h => subst hx; exact Pre.done (he _ _ _ h)
  | whileBody hb h => cases hx; exact Pre.whileBody hb (hc.2 _ _ h)
  | whileNext hb h₁ _ ih₂ => cases hx; exact Pre.whileNext hb (hc.1 _ _ _ h₁) (ih₂ rfl)
  | _ => cases hx

theorem CEquiv.seq {a a' b b' : Cmd ι S} (ha : CEquiv Φ a a') (hb : CEquiv Φ b b') :
    CEquiv Φ (Cmd.seq a b) (Cmd.seq a' b') := ⟨ha.1.seq hb.1, ha.2.seq hb.2⟩

theorem CEquiv.ite {w : ℕ} {b : S → Bool} {c₁ c₁' c₂ c₂' : Cmd ι S}
    (h₁ : CEquiv Φ c₁ c₁') (h₂ : CEquiv Φ c₂ c₂') :
    CEquiv Φ (Cmd.ite w b c₁ c₂) (Cmd.ite w b c₁' c₂') := ⟨h₁.1.ite h₂.1, h₁.2.ite h₂.2⟩

theorem CEquiv.while {w : ℕ} {b : S → Bool} {c c' : Cmd ι S} (hc : CEquiv Φ c c') :
    CEquiv Φ (Cmd.while w b c) (Cmd.while w b c') := ⟨hc.1.while, hc.2.while⟩

theorem seq_skip_left (b : Cmd ι S) : CEquiv Φ (Cmd.seq Cmd.skip b) b := by
  refine ⟨⟨fun s t n h => ?_, fun s n h => ?_⟩, ⟨fun s t n h => ?_, fun s n h => ?_⟩⟩
  · cases h with
    | seq h₁ h₂ => cases h₁; simpa using h₂
  · cases h with
    | stop => exact Pre.stop _ _
    | done h => cases h with | seq h₁ h₂ => cases h₁; simpa using Pre.done h₂
    | seqLeft h => rw [pre_skip h]; exact Pre.stop _ _
    | seqRight h₁ h₂ => cases h₁; simpa using h₂
  · simpa using Exec.seq (Exec.skip s) h
  · simpa using Pre.seqRight (c₂ := b) (Exec.skip (Φ := Φ) s) h

theorem seq_skip_right (a : Cmd ι S) : CEquiv Φ (Cmd.seq a Cmd.skip) a := by
  refine ⟨⟨fun s t n h => ?_, fun s n h => ?_⟩, ⟨fun s t n h => ?_, fun s n h => ?_⟩⟩
  · cases h with
    | seq h₁ h₂ => cases h₂; simpa using h₁
  · cases h with
    | stop => exact Pre.stop _ _
    | done h => cases h with | seq h₁ h₂ => cases h₂; simpa using Pre.done h₁
    | seqLeft h => exact h
    | seqRight h₁ h₂ => rw [pre_skip h₂]; simpa using Pre.done h₁
  · simpa using Exec.seq h (Exec.skip t)
  · exact Pre.seqLeft h

theorem seq_assoc (a b c : Cmd ι S) :
    CEquiv Φ (Cmd.seq (Cmd.seq a b) c) (Cmd.seq a (Cmd.seq b c)) := by
  have e1 : ∀ s t n, Exec Φ (Cmd.seq (Cmd.seq a b) c) s t n →
      Exec Φ (Cmd.seq a (Cmd.seq b c)) s t n := by
    intro s t n h
    cases h with
    | seq h h₃ => cases h with
      | seq h₁ h₂ => rw [Nat.add_assoc]; exact Exec.seq h₁ (Exec.seq h₂ h₃)
  have e2 : ∀ s t n, Exec Φ (Cmd.seq a (Cmd.seq b c)) s t n →
      Exec Φ (Cmd.seq (Cmd.seq a b) c) s t n := by
    intro s t n h
    cases h with
    | seq h₁ h => cases h with
      | seq h₂ h₃ => rw [← Nat.add_assoc]; exact Exec.seq (Exec.seq h₁ h₂) h₃
  refine ⟨⟨e1, fun s n h => ?_⟩, ⟨e2, fun s n h => ?_⟩⟩
  · cases h with
    | stop => exact Pre.stop _ _
    | done h => exact Pre.done (e1 _ _ _ h)
    | seqLeft h =>
      cases h with
      | stop => exact Pre.stop _ _
      | done h => cases h with
        | seq h₁ h₂ => exact Pre.seqRight h₁ (Pre.seqLeft (Pre.done h₂))
      | seqLeft h => exact Pre.seqLeft h
      | seqRight h₁ h₂ => exact Pre.seqRight h₁ (Pre.seqLeft h₂)
    | seqRight h h₃ => cases h with
      | seq h₁ h₂ => rw [Nat.add_assoc]; exact Pre.seqRight h₁ (Pre.seqRight h₂ h₃)
  · cases h with
    | stop => exact Pre.stop _ _
    | done h => exact Pre.done (e2 _ _ _ h)
    | seqLeft h => exact Pre.seqLeft (Pre.seqLeft h)
    | seqRight h₁ h =>
      cases h with
      | stop => exact Pre.seqLeft (Pre.seqRight h₁ (Pre.stop _ _))
      | done h => exact Pre.done (e2 _ _ _ (Exec.seq h₁ h))
      | seqLeft h => exact Pre.seqLeft (Pre.seqRight h₁ h)
      | seqRight h₂ h₃ => rw [← Nat.add_assoc]; exact Pre.seqRight (Exec.seq h₁ h₂) h₃

end Equiv

/-! ### The normal form keeps the cost semantics -/

theorem dot_trim (l : List ℤ) (f : Env) : dot (trim l) f = dot l f := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    have h := ih (fun i => f (i + 1))
    simp only [trim]
    split
    · next hr =>
      rw [hr] at h
      simp only [dot] at h
      split_ifs with ha
      · simp [dot, ha, ← h]
      · simp [dot, ← h]
    · next r hr =>
      simp only [dot]
      rw [h]

theorem canon_eval (p : PExp) (s : Env) : (canon p).eval s = p.eval s := by
  simp [canon, PExp.eval, dot_trim]

theorem all_canon (cs : List PExp) (s : Env) :
    (cs.map canon).all (fun g => decide (g.eval s ≤ 0)) = cs.all (fun g => decide (g.eval s ≤ 0)) := by
  induction cs with
  | nil => rfl
  | cons g cs ih => simp only [List.map_cons, List.all_cons, canon_eval, ih]

variable {Φ : ℕ → Cmd ℕ Env}

theorem app_equiv (a b : ACmd) : CEquiv Φ (app a b).toCmd (Cmd.seq a.toCmd b.toCmd) := by
  induction a with
  | skip => simp only [app, ACmd.toCmd]; exact (seq_skip_left _).symm
  | seq x _ _ _ rest _ ih =>
    simp only [app, ACmd.toCmd]
    exact ((CEquiv.refl x.toCmd).seq ih).trans (seq_assoc _ _ _).symm
  | _ =>
    cases b <;> first
      | exact CEquiv.refl _
      | exact (seq_skip_right _).symm

theorem nf_equiv (c : ACmd) : CEquiv Φ (nf c).toCmd c.toCmd := by
  induction c with
  | skip => exact CEquiv.refl _
  | assign w x a =>
    simp only [nf, ACmd.toCmd, canon_eval]; exact CEquiv.refl _
  | havoc w x => exact CEquiv.refl _
  | havocC w x cs =>
    simp only [nf, ACmd.toCmd, all_canon]; exact CEquiv.refl _
  | assume w cs =>
    simp only [nf, ACmd.toCmd, all_canon]; exact CEquiv.refl _
  | seq a _ _ _ b iha ihb => exact (app_equiv _ _).trans (iha.seq ihb)
  | ite w g _ _ a b iha ihb =>
    simp only [nf, ACmd.toCmd, canon_eval]; exact iha.ite ihb
  | «while» w g _ _ _ _ _ _ _ _ b ih =>
    simp only [nf, ACmd.toCmd, canon_eval]; exact ih.while
  | whileAnd w gs _ _ _ _ _ _ _ _ b ih =>
    simp only [nf, ACmd.toCmd, all_canon]; exact ih.while
  | whileLog w gs _ _ _ _ _ _ _ b ih =>
    cases gs with
    | nil => simp only [nf, ACmd.toCmd, List.map_nil]; exact ih.while
    | cons g gs =>
      cases gs with
      | nil =>
        simp only [nf, ACmd.toCmd, canon_eval, List.all_cons, List.all_nil, Bool.and_true]
        exact ih.while
      | cons g' gs => simp only [nf, ACmd.toCmd, all_canon]; exact ih.while
  | whileGrow w gs _ _ _ _ _ _ _ b ih =>
    cases gs with
    | nil => simp only [nf, ACmd.toCmd, List.map_nil]; exact ih.while
    | cons g gs =>
      cases gs with
      | nil =>
        simp only [nf, ACmd.toCmd, canon_eval, List.all_cons, List.all_nil, Bool.and_true]
        exact ih.while
      | cons g' gs => simp only [nf, ACmd.toCmd, all_canon]; exact ih.while
  | whileUp w gs _ _ _ _ _ _ _ b ih =>
    cases gs with
    | nil => simp only [nf, ACmd.toCmd, List.map_nil]; exact ih.while
    | cons g gs =>
      cases gs with
      | nil =>
        simp only [nf, ACmd.toCmd, canon_eval, List.all_cons, List.all_nil, Bool.and_true]
        exact ih.while
      | cons g' gs => simp only [nf, ACmd.toCmd, all_canon]; exact ih.while
  | whileSz w gs _ _ _ _ _ _ _ _ b ih =>
    cases gs with
    | nil => simp only [nf, ACmd.toCmd, List.map_nil]; exact ih.while
    | cons g gs =>
      cases gs with
      | nil =>
        simp only [nf, ACmd.toCmd, canon_eval, List.all_cons, List.all_nil, Bool.and_true]
        exact ih.while
      | cons g' gs => simp only [nf, ACmd.toCmd, all_canon]; exact ih.while
  | weaken _ _ _ _ _ c ih => exact ih
  | dead _ c ih => exact ih
  | call w f inst _ _ _ => exact CEquiv.refl _

/-- Two programs with the same normal form have the same cost semantics. -/
theorem equiv_of_nf_eq {c d : ACmd} (h : nf c = nf d) : CEquiv Φ c.toCmd d.toCmd :=
  (nf_equiv c).symm.trans (h ▸ nf_equiv d)

theorem validate_lower {c : ACmd} {s : MStmt} (h : validate c s = true) :
    ∃ d, lower s = some d ∧ CEquiv Φ c.toCmd d.toCmd := by
  unfold validate at h
  split at h
  · next d hd => exact ⟨d, hd, equiv_of_nf_eq (of_decide_eq_true h)⟩
  · cases h

/-- **Validated certificates.** If the program certificate `fs` is accepted, the bodies of
    its functions are the procedures of `Φ` and its contracts hold, and the body of function
    `i` is validated against the mini-C statement `s`, then `s` lowers to a program `d`
    such that, from every state satisfying the function's precondition, every execution
    prefix of `d` costs at most the function's bound and every terminating execution
    satisfies its postcondition. -/
theorem validated_sound (fs : List FunCert) (h : checkProgram fs = true)
    (hbody : ∀ i F b, fs[i]? = some F → F.body = some b → Φ i = b.toCmd)
    (hcontract : ∀ i F, fs[i]? = some F → F.body = none → FunSpec Φ i F)
    {i : ℕ} {F : FunCert} {b : ACmd} (hF : fs[i]? = some F) (hb : F.body = some b)
    {s : MStmt} (hv : validate b s = true) :
    ∃ d, lower s = some d ∧ ∀ ρ σ, holds F.pre ρ σ →
      (∀ n, Pre Φ d.toCmd σ n → n ≤ F.bound.eval ρ) ∧
      (∀ t n, Exec Φ d.toCmd σ t n → holds F.post ρ t) := by
  obtain ⟨d, hd, heq⟩ := validate_lower (Φ := Φ) hv
  refine ⟨d, hd, fun ρ σ hσ => ?_⟩
  have hspec := (program_sound fs h Φ hbody hcontract i F hF).1 ρ
  rw [hbody i F b hF hb] at hspec
  obtain ⟨hpre, hexec⟩ := hspec σ hσ
  exact ⟨fun n hn => hpre n (heq.2.2 σ n hn),
    fun t n hn => hexec t n (heq.2.1 σ t n hn)⟩

/-! ### Example: the loop of `countCert` -/

/-- `while (i < n) i = i + 1;` with `i = x₀`, `n = x₁`, unit weights. -/
def countSrc : MStmt :=
  .while 1 [.cmp .lt (.var 0) (.var 1)] (.assign 1 0 (.add (.var 0) (.lit 1)))

theorem countCert_validated : validate countCert countSrc = true := by decide

/-- `i = i + 2` is not the program of the certificate. -/
def countSrcWrong : MStmt :=
  .while 1 [.cmp .lt (.var 0) (.var 1)] (.assign 1 0 (.add (.var 0) (.lit 2)))

theorem countCert_not_validated : validate countCert countSrcWrong = false := by decide

end ImperativeOptimization.MiniC
