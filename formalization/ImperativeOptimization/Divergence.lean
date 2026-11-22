/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import ImperativeOptimization.Language

namespace ImperativeOptimization

/-!
# Infinite executions of the small language, and why a cost bound excludes them

`Language` bounds the cost of every execution *prefix* (`Pre`). This module defines the
infinite executions of a command and proves the remark of Paper I (Section "A cost logic
for a small language"): if every loop test and every call has a positive weight, a command
with a valid cost bound has no infinite execution from its precondition.

* `DivStep Φ R`: one unfolding of the rules of coinductive big-step divergence (Leroy and
  Grall): a sequence diverges in its first part, or terminates it and diverges in the
  second; a conditional diverges in the branch it takes; a loop whose test holds diverges
  in its body, or completes the body and diverges in the rest of the loop; a call diverges
  in the body of the procedure. `skip` and atoms never diverge.
* `Div Φ c s`: the greatest fixed point of `DivStep`, as the union of all post-fixed
  points (`R ⊆ DivStep Φ R`). Lean 4 has no coinductive types; this is the standard
  encoding.
* `PosWeights c`: every loop test and every call in `c` has a positive weight.
* `div_prefixes_unbounded`: an infinite execution has prefixes of every cost.
* `valid_no_div`, `derivable_no_div`: a valid (or derivable) bound excludes infinite
  executions from the precondition.
* `spin_div`, `spin_prefixes`: the hypotheses are satisfiable (`while true skip`).
-/

variable {ι S : Type}

/-- One unfolding of the divergence rules, relative to a relation `R` that stands for
    "diverges". -/
def DivStep (Φ : ι → Cmd ι S) (R : Cmd ι S → S → Prop) : Cmd ι S → S → Prop
  | Cmd.skip, _ => False
  | Cmd.atom _ _, _ => False
  | Cmd.seq c₁ c₂, s => R c₁ s ∨ ∃ u n, Exec Φ c₁ s u n ∧ R c₂ u
  | Cmd.ite _ b c₁ c₂, s => (b s = true ∧ R c₁ s) ∨ (b s = false ∧ R c₂ s)
  | Cmd.while w b c, s => b s = true ∧ (R c s ∨ ∃ u n, Exec Φ c s u n ∧ R (Cmd.while w b c) u)
  | Cmd.call _ p, s => R (Φ p) s

/-- **Infinite execution.** `Div Φ c s`: `c` started in `s` has an infinite execution
    (the greatest fixed point of `DivStep`). -/
def Div (Φ : ι → Cmd ι S) (c : Cmd ι S) (s : S) : Prop :=
  ∃ R : Cmd ι S → S → Prop, (∀ c s, R c s → DivStep Φ R c s) ∧ R c s

/-- `Div` is itself a post-fixed point: an infinite execution unfolds by one rule. -/
theorem Div.unfold {Φ : ι → Cmd ι S} {c : Cmd ι S} {s : S} (h : Div Φ c s) :
    DivStep Φ (Div Φ) c s := by
  obtain ⟨R, hR, hc⟩ := h
  have lift : ∀ c s, R c s → Div Φ c s := fun c s h => ⟨R, hR, h⟩
  have := hR c s hc
  cases c with
  | skip => exact this.elim
  | atom => exact this.elim
  | seq c₁ c₂ =>
    rcases this with h | ⟨u, n, he, h⟩
    · exact Or.inl (lift _ _ h)
    · exact Or.inr ⟨u, n, he, lift _ _ h⟩
  | ite w b c₁ c₂ =>
    rcases this with ⟨hb, h⟩ | ⟨hb, h⟩
    · exact Or.inl ⟨hb, lift _ _ h⟩
    · exact Or.inr ⟨hb, lift _ _ h⟩
  | «while» w b c =>
    obtain ⟨hb, h | ⟨u, n, he, h⟩⟩ := this
    · exact ⟨hb, Or.inl (lift _ _ h)⟩
    · exact ⟨hb, Or.inr ⟨u, n, he, lift _ _ h⟩⟩
  | call w p => exact lift _ _ this

/-- Every loop test and every call has a positive weight (conditionals and atoms may
    cost nothing). -/
def PosWeights : Cmd ι S → Prop
  | Cmd.skip => True
  | Cmd.atom _ _ => True
  | Cmd.seq c₁ c₂ => PosWeights c₁ ∧ PosWeights c₂
  | Cmd.ite _ _ c₁ c₂ => PosWeights c₁ ∧ PosWeights c₂
  | Cmd.while w _ c => 0 < w ∧ PosWeights c
  | Cmd.call w _ => 0 < w

/-- **An infinite execution has prefixes of every cost**, when loop tests and calls
    have positive weights. By induction on the cost `N`, and inside it on the command:
    a loop iteration or a call pays at least one unit (outer induction), a sequence or a
    conditional moves to a smaller command (inner induction). -/
theorem div_prefixes_unbounded {Φ : ι → Cmd ι S} (hΦ : ∀ p, PosWeights (Φ p))
    {c : Cmd ι S} (hc : PosWeights c) {s : S} (hd : Div Φ c s) (N : ℕ) :
    ∃ n, N ≤ n ∧ Pre Φ c s n := by
  obtain ⟨R, hR, hcs⟩ := hd
  -- the claim for every command and state in `R`, by induction on `N`
  suffices key : ∀ N c, PosWeights c → ∀ s, R c s → ∃ n, N ≤ n ∧ Pre Φ c s n from
    key N c hc s hcs
  intro N
  induction N with
  | zero => exact fun c _ s _ => ⟨0, le_refl _, Pre.stop c s⟩
  | succ N ihN =>
    intro c
    induction c with
    | skip => intro _ s h; exact (hR _ s h).elim
    | atom w r => intro _ s h; exact (hR _ s h).elim
    | seq c₁ c₂ ih₁ ih₂ =>
      intro hc s h
      rcases hR _ s h with h₁ | ⟨u, m, he, h₂⟩
      · obtain ⟨n, hn, hp⟩ := ih₁ hc.1 s h₁
        exact ⟨n, hn, Pre.seqLeft hp⟩
      · obtain ⟨n, hn, hp⟩ := ih₂ hc.2 u h₂
        exact ⟨m + n, by omega, Pre.seqRight he hp⟩
    | ite w b c₁ c₂ ih₁ ih₂ =>
      intro hc s h
      rcases hR _ s h with ⟨hb, h₁⟩ | ⟨hb, h₂⟩
      · obtain ⟨n, hn, hp⟩ := ih₁ hc.1 s h₁
        exact ⟨w + n, by omega, Pre.iteTrue hb hp⟩
      · obtain ⟨n, hn, hp⟩ := ih₂ hc.2 s h₂
        exact ⟨w + n, by omega, Pre.iteFalse hb hp⟩
    | «while» w b c ihc =>
      intro hc s h
      obtain ⟨hb, h₁ | ⟨u, m, he, h₂⟩⟩ := hR _ s h
      · obtain ⟨n, hn, hp⟩ := ihc hc.2 s h₁
        exact ⟨w + n, by omega, Pre.whileBody hb hp⟩
      · obtain ⟨n, hn, hp⟩ := ihN _ hc u h₂
        have := hc.1
        exact ⟨w + m + n, by omega, Pre.whileNext hb he hp⟩
    | call w p =>
      intro hc s h
      obtain ⟨n, hn, hp⟩ := ihN _ (hΦ p) s (hR _ s h)
      have : 0 < w := hc
      exact ⟨w + n, by omega, Pre.call hp⟩

/-- **A valid cost bound excludes infinite executions** from the precondition, when loop
    tests and calls have positive weights. -/
theorem valid_no_div {Φ : ι → Cmd ι S} (hΦ : ∀ p, PosWeights (Φ p)) {P Q : S → Prop}
    {c : Cmd ι S} {B : ℕ} (hc : PosWeights c) (hv : Valid Φ P c B Q) {s : S} (hP : P s) :
    ¬ Div Φ c s := by
  intro hd
  obtain ⟨n, hn, hp⟩ := div_prefixes_unbounded hΦ hc hd (B + 1)
  have := (hv s hP).1 n hp
  omega

/-- The same for a bound derivable in the cost logic from no assumption (Paper I, the
    remark after `prop:amortised-loop`). -/
theorem derivable_no_div {Φ : ι → Cmd ι S} (hΦ : ∀ p, PosWeights (Φ p)) {P Q : S → Prop}
    {c : Cmd ι S} {B : ℕ} (hc : PosWeights c) (h : Derivable Φ noSpecs P c B Q) {s : S}
    (hP : P s) : ¬ Div Φ c s :=
  valid_no_div hΦ hc (soundness h (fun _ _ _ _ hf => hf.elim)) hP

/-! ### The hypotheses are satisfiable -/

/-- `while true skip`, with test weight 1. -/
def spin : Cmd Unit Unit := Cmd.while 1 (fun _ => true) Cmd.skip

/-- `spin` has an infinite execution. -/
theorem spin_div : Div (fun _ => Cmd.skip) spin () := by
  refine ⟨fun c _ => c = spin, ?_, rfl⟩
  rintro c s rfl
  exact ⟨rfl, Or.inr ⟨(), 0, Exec.skip (), rfl⟩⟩

/-- Hence its prefixes have every cost, and no bound is valid for it. -/
theorem spin_prefixes (N : ℕ) : ∃ n, N ≤ n ∧ Pre (fun _ => Cmd.skip) spin () n :=
  div_prefixes_unbounded (Φ := fun _ => Cmd.skip) (c := spin) (fun _ => trivial)
    ⟨Nat.one_pos, trivial⟩ spin_div N

theorem spin_no_bound (B : ℕ) :
    ¬ Valid (fun _ => Cmd.skip) (fun _ => True) spin B (fun _ => True) :=
  fun hv => valid_no_div (Φ := fun _ => Cmd.skip) (c := spin) (fun _ => trivial)
    ⟨Nat.one_pos, trivial⟩ hv trivial spin_div

end ImperativeOptimization
