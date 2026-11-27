/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic

namespace ImperativeOptimization

/-!
# A small imperative language with costs, and a sound cost logic

The other modules prove bounds for one loop or one recursion scheme at a time. This
module defines a *language* and proves that the rules by which a cost analysis composes
bounds are sound for every program of it.

* `Cmd ι S`: commands over a state type `S`: `skip`, atomic actions with a weight and a
  (possibly nondeterministic or partial) transition relation, sequence, conditional,
  `while` (the tests having a weight too) and calls of procedures named by `ι`, whose
  bodies are given by an environment `Φ : ι → Cmd ι S`. Procedures may be recursive.
* `Exec Φ c s t n`: `c` started in `s` terminates in `t` with cost `n` (big-step).
* `Pre Φ c s n`: some execution of `c` from `s`, **not necessarily terminated**, has
  accumulated cost `n`. Bounding `Pre` bounds diverging executions as well.
* `Valid Φ P c B Q`: from every state satisfying `P`, every execution prefix of `c` costs
  at most `B`, and every terminating execution ends in a state satisfying `Q`.
* `valid_skip`, `valid_atom`, `valid_seq`, `valid_ite`, `valid_while`, `valid_call`,
  `valid_conseq`: the rules. `valid_while` is the ranking certificate under an invariant
  and a context (`Certificate.ranking_bound_of_context`) combined with the loop cost
  formula.
* `Derivable Φ Γ`: the same rules as an inductive proof system, relative to a set `Γ` of
  *assumed* triples (contracts of code that is not analysed, such as library functions),
  with a rule for calls of possibly recursive procedures. `soundness` shows that
  everything derivable is valid provided the assumed triples are.
* `ValidSym`: bounds that are functions of the initial state (*symbolic* bounds), with
  the rule `validSym_call` that instantiates such a summary at a call site.
-/

/-- Commands. `atom w r` performs a step of the relation `r` at cost `w`; the tests of
    `ite` and `while` cost `w`; `call w p` runs the body of procedure `p` after paying
    `w`. -/
inductive Cmd (ι S : Type) where
  | skip : Cmd ι S
  | atom (w : ℕ) (r : S → S → Prop) : Cmd ι S
  | seq (c₁ c₂ : Cmd ι S) : Cmd ι S
  | ite (w : ℕ) (b : S → Bool) (c₁ c₂ : Cmd ι S) : Cmd ι S
  | while (w : ℕ) (b : S → Bool) (c : Cmd ι S) : Cmd ι S
  | call (w : ℕ) (p : ι) : Cmd ι S

variable {ι S : Type}

/-- Big-step semantics with cost: `Exec Φ c s t n` means that `c`, started in `s`, can
    terminate in `t` after spending `n`, the procedure bodies being given by `Φ`. -/
inductive Exec (Φ : ι → Cmd ι S) : Cmd ι S → S → S → ℕ → Prop where
  | skip (s : S) : Exec Φ Cmd.skip s s 0
  | atom {w : ℕ} {r : S → S → Prop} {s t : S} (h : r s t) : Exec Φ (Cmd.atom w r) s t w
  | seq {c₁ c₂ : Cmd ι S} {s u t : S} {n₁ n₂ : ℕ}
      (h₁ : Exec Φ c₁ s u n₁) (h₂ : Exec Φ c₂ u t n₂) : Exec Φ (Cmd.seq c₁ c₂) s t (n₁ + n₂)
  | iteTrue {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd ι S} {s t : S} {n : ℕ}
      (hb : b s = true) (h : Exec Φ c₁ s t n) : Exec Φ (Cmd.ite w b c₁ c₂) s t (w + n)
  | iteFalse {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd ι S} {s t : S} {n : ℕ}
      (hb : b s = false) (h : Exec Φ c₂ s t n) : Exec Φ (Cmd.ite w b c₁ c₂) s t (w + n)
  | whileFalse {w : ℕ} {b : S → Bool} {c : Cmd ι S} {s : S} (hb : b s = false) :
      Exec Φ (Cmd.while w b c) s s w
  | whileTrue {w : ℕ} {b : S → Bool} {c : Cmd ι S} {s u t : S} {n₁ n₂ : ℕ}
      (hb : b s = true) (h₁ : Exec Φ c s u n₁) (h₂ : Exec Φ (Cmd.while w b c) u t n₂) :
      Exec Φ (Cmd.while w b c) s t (w + n₁ + n₂)
  | call {w : ℕ} {p : ι} {s t : S} {n : ℕ} (h : Exec Φ (Φ p) s t n) :
      Exec Φ (Cmd.call w p) s t (w + n)

/-- Cost of execution prefixes: `Pre Φ c s n` means that an execution of `c` from `s`,
    possibly interrupted or still running, has spent `n`. -/
inductive Pre (Φ : ι → Cmd ι S) : Cmd ι S → S → ℕ → Prop where
  | stop (c : Cmd ι S) (s : S) : Pre Φ c s 0
  | done {c : Cmd ι S} {s t : S} {n : ℕ} (h : Exec Φ c s t n) : Pre Φ c s n
  | seqLeft {c₁ c₂ : Cmd ι S} {s : S} {n : ℕ} (h : Pre Φ c₁ s n) : Pre Φ (Cmd.seq c₁ c₂) s n
  | seqRight {c₁ c₂ : Cmd ι S} {s u : S} {n₁ n₂ : ℕ}
      (h₁ : Exec Φ c₁ s u n₁) (h₂ : Pre Φ c₂ u n₂) : Pre Φ (Cmd.seq c₁ c₂) s (n₁ + n₂)
  | iteTrue {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd ι S} {s : S} {n : ℕ}
      (hb : b s = true) (h : Pre Φ c₁ s n) : Pre Φ (Cmd.ite w b c₁ c₂) s (w + n)
  | iteFalse {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd ι S} {s : S} {n : ℕ}
      (hb : b s = false) (h : Pre Φ c₂ s n) : Pre Φ (Cmd.ite w b c₁ c₂) s (w + n)
  | whileBody {w : ℕ} {b : S → Bool} {c : Cmd ι S} {s : S} {n : ℕ}
      (hb : b s = true) (h : Pre Φ c s n) : Pre Φ (Cmd.while w b c) s (w + n)
  | whileNext {w : ℕ} {b : S → Bool} {c : Cmd ι S} {s u : S} {n₁ n₂ : ℕ}
      (hb : b s = true) (h₁ : Exec Φ c s u n₁) (h₂ : Pre Φ (Cmd.while w b c) u n₂) :
      Pre Φ (Cmd.while w b c) s (w + n₁ + n₂)
  | call {w : ℕ} {p : ι} {s : S} {n : ℕ} (h : Pre Φ (Φ p) s n) : Pre Φ (Cmd.call w p) s (w + n)

/-- **Validity of a cost triple.** From every state satisfying `P`: every execution
    prefix of `c` costs at most `B`, and every terminating execution ends in `Q`. -/
def Valid (Φ : ι → Cmd ι S) (P : S → Prop) (c : Cmd ι S) (B : ℕ) (Q : S → Prop) : Prop :=
  ∀ s, P s → (∀ n, Pre Φ c s n → n ≤ B) ∧ (∀ t n, Exec Φ c s t n → Q t)

variable {Φ : ι → Cmd ι S}

/-- Under a valid triple, terminating executions cost at most `B` too. -/
theorem Valid.exec_le {P Q : S → Prop} {c : Cmd ι S} {B : ℕ} (h : Valid Φ P c B Q)
    {s t : S} {n : ℕ} (hP : P s) (he : Exec Φ c s t n) : n ≤ B :=
  (h s hP).1 n (Pre.done he)

theorem valid_skip (P : S → Prop) : Valid Φ P Cmd.skip 0 P := by
  intro s hP
  refine ⟨fun n h => ?_, fun t n h => ?_⟩
  · cases h with
    | stop => exact le_refl _
    | done h => cases h; exact le_refl _
  · cases h; exact hP

theorem valid_atom (P Q : S → Prop) (w : ℕ) (r : S → S → Prop)
    (h : ∀ s t, P s → r s t → Q t) : Valid Φ P (Cmd.atom w r) w Q := by
  intro s hP
  refine ⟨fun n hn => ?_, fun t n he => ?_⟩
  · cases hn with
    | stop => exact Nat.zero_le _
    | done he => cases he; exact le_refl _
  · cases he with
    | atom hr => exact h s t hP hr

/-- A triple whose precondition is unsatisfiable is valid (dead code). -/
theorem valid_unreachable (c : Cmd ι S) (B : ℕ) (Q : S → Prop) :
    Valid Φ (fun _ => False) c B Q :=
  fun _ h => h.elim

/-- **Sequence: costs add.** -/
theorem valid_seq {P R Q : S → Prop} {c₁ c₂ : Cmd ι S} {B₁ B₂ : ℕ}
    (h₁ : Valid Φ P c₁ B₁ R) (h₂ : Valid Φ R c₂ B₂ Q) :
    Valid Φ P (Cmd.seq c₁ c₂) (B₁ + B₂) Q := by
  intro s hP
  have exec_bound : ∀ t n, Exec Φ (Cmd.seq c₁ c₂) s t n → n ≤ B₁ + B₂ ∧ Q t := by
    intro t n he
    cases he with
    | seq e₁ e₂ =>
      have hR := (h₁ s hP).2 _ _ e₁
      have a := h₁.exec_le hP e₁
      have b := h₂.exec_le hR e₂
      exact ⟨by omega, (h₂ _ hR).2 _ _ e₂⟩
  refine ⟨fun n hn => ?_, fun t n he => (exec_bound t n he).2⟩
  cases hn with
  | stop => exact Nat.zero_le _
  | done he => exact (exec_bound _ _ he).1
  | seqLeft hp =>
    have := (h₁ s hP).1 _ hp
    omega
  | seqRight e₁ p₂ =>
    have hR := (h₁ s hP).2 _ _ e₁
    have a := h₁.exec_le hP e₁
    have b := (h₂ _ hR).1 _ p₂
    omega

/-- **Conditional: the test, then the maximum of the branches.** -/
theorem valid_ite {P Q : S → Prop} {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd ι S} {B₁ B₂ : ℕ}
    (h₁ : Valid Φ (fun s => P s ∧ b s = true) c₁ B₁ Q)
    (h₂ : Valid Φ (fun s => P s ∧ b s = false) c₂ B₂ Q) :
    Valid Φ P (Cmd.ite w b c₁ c₂) (w + max B₁ B₂) Q := by
  intro s hP
  have exec_bound : ∀ t n, Exec Φ (Cmd.ite w b c₁ c₂) s t n → n ≤ w + max B₁ B₂ ∧ Q t := by
    intro t n he
    cases he with
    | iteTrue hb e =>
      have a := h₁.exec_le (P := fun s => P s ∧ b s = true) ⟨hP, hb⟩ e
      exact ⟨by have := le_max_left B₁ B₂; omega, (h₁ s ⟨hP, hb⟩).2 _ _ e⟩
    | iteFalse hb e =>
      have a := h₂.exec_le (P := fun s => P s ∧ b s = false) ⟨hP, hb⟩ e
      exact ⟨by have := le_max_right B₁ B₂; omega, (h₂ s ⟨hP, hb⟩).2 _ _ e⟩
  refine ⟨fun n hn => ?_, fun t n he => (exec_bound t n he).2⟩
  cases hn with
  | stop => exact Nat.zero_le _
  | done he => exact (exec_bound _ _ he).1
  | iteTrue hb p =>
    have a := (h₁ s ⟨hP, hb⟩).1 _ p
    have := le_max_left B₁ B₂
    omega
  | iteFalse hb p =>
    have a := (h₂ s ⟨hP, hb⟩).1 _ p
    have := le_max_right B₁ B₂
    omega

/-- **Call: the call weight, then the body.** -/
theorem valid_call {P Q : S → Prop} {w : ℕ} {p : ι} {B : ℕ}
    (h : Valid Φ P (Φ p) B Q) : Valid Φ P (Cmd.call w p) (w + B) Q := by
  intro s hP
  have exec_bound : ∀ t n, Exec Φ (Cmd.call w p) s t n → n ≤ w + B ∧ Q t := by
    intro t n he
    cases he with
    | call e =>
      have a := h.exec_le hP e
      exact ⟨by omega, (h s hP).2 _ _ e⟩
  refine ⟨fun n hn => ?_, fun t n he => (exec_bound t n he).2⟩
  cases hn with
  | stop => exact Nat.zero_le _
  | done he => exact (exec_bound _ _ he).1
  | call hp =>
    have := (h s hP).1 _ hp
    omega

/-- **Consequence (context rule).** A triple can be used under a stronger precondition,
    with a larger bound and a weaker postcondition. In particular a bound derived for a
    command under a context `P` holds wherever the state satisfies `P`. -/
theorem valid_conseq {P P' Q Q' : S → Prop} {c : Cmd ι S} {B B' : ℕ}
    (hP : ∀ s, P' s → P s) (h : Valid Φ P c B Q) (hB : B ≤ B') (hQ : ∀ t, Q t → Q' t) :
    Valid Φ P' c B' Q' := by
  intro s hs
  exact ⟨fun n hn => le_trans ((h s (hP s hs)).1 n hn) hB,
    fun t n he => hQ t ((h s (hP s hs)).2 t n he)⟩

section While

variable {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Terminating executions of a loop under a ranking certificate: with invariant `I`
    and potential `V < m + 1`, at most `m` iterations are performed. -/
theorem while_exec_bound {I : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd ι S} {Wb : ℕ}
    (V : S → α)
    (h_body : ∀ v, Valid Φ (fun s => I s ∧ b s = true ∧ V s = v) c Wb
      (fun t => I t ∧ V t ≤ v - 1))
    (h_pos : ∀ s, I s → b s = true → 1 ≤ V s)
    {s t : S} {n : ℕ} (he : Exec Φ (Cmd.while w b c) s t n) :
    ∀ m : ℕ, I s → V s < m + 1 → n ≤ m * (w + Wb) + w ∧ I t ∧ b t = false := by
  generalize hW : Cmd.while w b c = W at he
  induction he with
  | skip => cases hW
  | atom => cases hW
  | seq => cases hW
  | iteTrue => cases hW
  | iteFalse => cases hW
  | call => cases hW
  | whileFalse hb =>
    cases hW
    intro m hI _
    exact ⟨Nat.le_add_left _ _, hI, hb⟩
  | @whileTrue _ _ _ s' u' _ _ _ hb e₁ _ _ ih =>
    cases hW
    intro m hI hV
    have hbody := h_body (V s') s' ⟨hI, hb, rfl⟩
    have hpost := hbody.2 _ _ e₁
    have hcost := hbody.1 _ (Pre.done e₁)
    have h1 := h_pos _ hI hb
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
      cases m with
      | zero => simp at hV; linarith
      | succ k => exact ⟨k, rfl⟩
    have hVu : V u' < (k : α) + 1 := by push_cast at hV; linarith [hpost.2]
    obtain ⟨hn, hIt, hbt⟩ := ih rfl k hpost.1 hVu
    refine ⟨?_, hIt, hbt⟩
    have : (k + 1) * (w + Wb) = k * (w + Wb) + (w + Wb) := by ring
    omega

/-- The same for execution prefixes. -/
theorem while_pre_bound {I : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd ι S} {Wb : ℕ}
    (V : S → α)
    (h_body : ∀ v, Valid Φ (fun s => I s ∧ b s = true ∧ V s = v) c Wb
      (fun t => I t ∧ V t ≤ v - 1))
    (h_pos : ∀ s, I s → b s = true → 1 ≤ V s)
    {s : S} {n : ℕ} (hp : Pre Φ (Cmd.while w b c) s n) :
    ∀ m : ℕ, I s → V s < m + 1 → n ≤ m * (w + Wb) + w := by
  generalize hW : Cmd.while w b c = W at hp
  induction hp with
  | stop => intro m _ _; exact Nat.zero_le _
  | done he =>
    cases hW
    intro m hI hV
    exact (while_exec_bound V h_body h_pos he m hI hV).1
  | seqLeft => cases hW
  | seqRight => cases hW
  | iteTrue => cases hW
  | iteFalse => cases hW
  | call => cases hW
  | @whileBody _ _ _ s' _ hb p =>
    cases hW
    intro m hI hV
    have hcost := (h_body (V s') s' ⟨hI, hb, rfl⟩).1 _ p
    have h1 := h_pos _ hI hb
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
      cases m with
      | zero => simp at hV; linarith
      | succ k => exact ⟨k, rfl⟩
    have : (k + 1) * (w + Wb) = k * (w + Wb) + (w + Wb) := by ring
    omega
  | @whileNext _ _ _ s' u' _ _ hb e₁ _ ih =>
    cases hW
    intro m hI hV
    have hbody := h_body (V s') s' ⟨hI, hb, rfl⟩
    have hpost := hbody.2 _ _ e₁
    have hcost := hbody.1 _ (Pre.done e₁)
    have h1 := h_pos _ hI hb
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
      cases m with
      | zero => simp at hV; linarith
      | succ k => exact ⟨k, rfl⟩
    have hVu : V u' < (k : α) + 1 := by push_cast at hV; linarith [hpost.2]
    have hn := ih rfl k hpost.1 hVu
    have : (k + 1) * (w + Wb) = k * (w + Wb) + (w + Wb) := by ring
    omega

variable [FloorSemiring α]

/-- **Loop rule.** Let `I` be an invariant of the body, `V` a potential that the body
    decreases by at least `1` and that is at least `1` when the guard holds, and `K` a
    bound of `V` under the context `C`. Then, from `I ∧ C`, the loop costs at most
    `⌊K⌋ · (w + Wb) + w` (also if it is interrupted), and it ends in `I` with the guard
    false. -/
theorem valid_while {I C : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd ι S} {Wb : ℕ}
    (V : S → α) (K : α)
    (h_body : ∀ v, Valid Φ (fun s => I s ∧ b s = true ∧ V s = v) c Wb
      (fun t => I t ∧ V t ≤ v - 1))
    (h_pos : ∀ s, I s → b s = true → 1 ≤ V s)
    (hK : ∀ s, C s → V s ≤ K) :
    Valid Φ (fun s => I s ∧ C s) (Cmd.while w b c) (⌊K⌋₊ * (w + Wb) + w)
      (fun t => I t ∧ b t = false) := by
  intro s hs
  have hV : V s < (⌊K⌋₊ : α) + 1 := lt_of_le_of_lt (hK s hs.2) (Nat.lt_floor_add_one K)
  exact ⟨fun n hp => while_pre_bound V h_body h_pos hp _ hs.1 hV,
    fun t n he => (while_exec_bound V h_body h_pos he _ hs.1 hV).2⟩

end While

/-! ### Loops whose body cost depends on the potential (amortised loop rule) -/

section WhileSum

/-- Terminating executions of a loop whose body costs at most `W (V s)` from `s`: with
    `F X ≥ w` and `w + W v + F (X - d) ≤ F X` for `d ≤ v ≤ X`, an execution from a state
    with `V s ≤ X` costs at most `F X`. -/
theorem whileSum_exec {I : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd ι S}
    (V : S → ℤ) (d : ℕ) (W : ℤ → ℕ) (F : ℤ → ℕ)
    (h_body : ∀ s, I s → b s = true →
      (∀ n, Pre Φ c s n → n ≤ W (V s)) ∧ ∀ t n, Exec Φ c s t n → I t ∧ V t + d ≤ V s)
    (h_pos : ∀ s, I s → b s = true → (d : ℤ) ≤ V s)
    (hF0 : ∀ X, w ≤ F X)
    (hF : ∀ X v, (d : ℤ) ≤ v → v ≤ X → w + W v + F (X - d) ≤ F X)
    {s t : S} {n : ℕ} (he : Exec Φ (Cmd.while w b c) s t n) :
    ∀ X : ℤ, I s → V s ≤ X → n ≤ F X ∧ I t ∧ b t = false := by
  generalize hW : Cmd.while w b c = Wc at he
  induction he with
  | skip => cases hW
  | atom => cases hW
  | seq => cases hW
  | iteTrue => cases hW
  | iteFalse => cases hW
  | call => cases hW
  | whileFalse hb =>
    cases hW
    intro X hI _
    exact ⟨hF0 X, hI, hb⟩
  | @whileTrue _ _ _ s' u' _ _ _ hb e₁ _ _ ih =>
    cases hW
    intro X hI hV
    have hbody := h_body s' hI hb
    have hpost := hbody.2 _ _ e₁
    have hcost := hbody.1 _ (Pre.done e₁)
    have h1 := h_pos _ hI hb
    obtain ⟨hn, hIt, hbt⟩ := ih rfl (X - d) hpost.1 (by linarith [hpost.2])
    refine ⟨?_, hIt, hbt⟩
    have := hF X (V s') h1 hV
    omega

/-- The same for execution prefixes. -/
theorem whileSum_pre {I : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd ι S}
    (V : S → ℤ) (d : ℕ) (W : ℤ → ℕ) (F : ℤ → ℕ)
    (h_body : ∀ s, I s → b s = true →
      (∀ n, Pre Φ c s n → n ≤ W (V s)) ∧ ∀ t n, Exec Φ c s t n → I t ∧ V t + d ≤ V s)
    (h_pos : ∀ s, I s → b s = true → (d : ℤ) ≤ V s)
    (hF0 : ∀ X, w ≤ F X)
    (hF : ∀ X v, (d : ℤ) ≤ v → v ≤ X → w + W v + F (X - d) ≤ F X)
    {s : S} {n : ℕ} (hp : Pre Φ (Cmd.while w b c) s n) :
    ∀ X : ℤ, I s → V s ≤ X → n ≤ F X := by
  generalize hW : Cmd.while w b c = Wc at hp
  induction hp with
  | stop => intro _ _ _; exact Nat.zero_le _
  | done he =>
    cases hW
    intro X hI hV
    exact (whileSum_exec V d W F h_body h_pos hF0 hF he X hI hV).1
  | seqLeft => cases hW
  | seqRight => cases hW
  | iteTrue => cases hW
  | iteFalse => cases hW
  | call => cases hW
  | @whileBody _ _ _ s' _ hb p =>
    cases hW
    intro X hI hV
    have hcost := (h_body s' hI hb).1 _ p
    have := hF X (V s') (h_pos _ hI hb) hV
    omega
  | @whileNext _ _ _ s' u' _ _ hb e₁ _ ih =>
    cases hW
    intro X hI hV
    have hbody := h_body s' hI hb
    have hpost := hbody.2 _ _ e₁
    have hcost := hbody.1 _ (Pre.done e₁)
    have hn := ih rfl (X - d) hpost.1 (by linarith [hpost.2])
    have := hF X (V s') (h_pos _ hI hb) hV
    omega

/-- **Amortised loop rule.** As `valid_while`, but the body may cost more when the
    potential is larger: from a state where the guard holds, it costs at most `W (V s)`,
    and it decreases the integer potential `V` by at least `d`. Any `F` with `F X ≥ w` and
    `w + W v + F (X - d) ≤ F X` (for `d ≤ v ≤ X`) bounds the loop from `V ≤ K` by `F K`:
    for `W v = a + c v` the bound is the sum `Σᵢ (w + a + c (K - i d)) + w` over the
    iterations instead of their number times the largest body cost. -/
theorem valid_whileSum {I : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd ι S}
    (V : S → ℤ) (d : ℕ) (W : ℤ → ℕ) (F : ℤ → ℕ) (K : ℤ)
    (h_body : ∀ s, I s → b s = true →
      (∀ n, Pre Φ c s n → n ≤ W (V s)) ∧ ∀ t n, Exec Φ c s t n → I t ∧ V t + d ≤ V s)
    (h_pos : ∀ s, I s → b s = true → (d : ℤ) ≤ V s)
    (hF0 : ∀ X, w ≤ F X)
    (hF : ∀ X v, (d : ℤ) ≤ v → v ≤ X → w + W v + F (X - d) ≤ F X) :
    Valid Φ (fun s => I s ∧ V s ≤ K) (Cmd.while w b c) (F K)
      (fun t => I t ∧ b t = false) := by
  intro s hs
  exact ⟨fun n hp => whileSum_pre V d W F h_body h_pos hF0 hF hp K hs.1 hs.2,
    fun t n he => (whileSum_exec V d W F h_body h_pos hF0 hF he K hs.1 hs.2).2⟩

/-- Terminating executions, with a bound `F` of the potential itself: if `F` is monotone,
    `F X ≥ w` and `w + W v + F (v - d) ≤ F v` for `v ≥ d`, an execution from `s` costs at
    most `F (V s)`. -/
theorem whileMono_exec {I : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd ι S}
    (V : S → ℤ) (d : ℕ) (W : ℤ → ℕ) (F : ℤ → ℕ)
    (h_body : ∀ s, I s → b s = true →
      (∀ n, Pre Φ c s n → n ≤ W (V s)) ∧ ∀ t n, Exec Φ c s t n → I t ∧ V t + d ≤ V s)
    (h_pos : ∀ s, I s → b s = true → (d : ℤ) ≤ V s)
    (hF0 : ∀ X, w ≤ F X) (hmono : Monotone F)
    (hF : ∀ v, (d : ℤ) ≤ v → w + W v + F (v - d) ≤ F v)
    {s t : S} {n : ℕ} (he : Exec Φ (Cmd.while w b c) s t n) :
    I s → n ≤ F (V s) ∧ I t ∧ b t = false := by
  generalize hW : Cmd.while w b c = Wc at he
  induction he with
  | skip => cases hW
  | atom => cases hW
  | seq => cases hW
  | iteTrue => cases hW
  | iteFalse => cases hW
  | call => cases hW
  | whileFalse hb =>
    cases hW
    intro hI
    exact ⟨hF0 _, hI, hb⟩
  | @whileTrue _ _ _ s' u' _ _ _ hb e₁ _ _ ih =>
    cases hW
    intro hI
    have hbody := h_body s' hI hb
    have hpost := hbody.2 _ _ e₁
    have hcost := hbody.1 _ (Pre.done e₁)
    have h1 := h_pos _ hI hb
    obtain ⟨hn, hIt, hbt⟩ := ih rfl hpost.1
    refine ⟨?_, hIt, hbt⟩
    have hm := hmono (show V u' ≤ V s' - d by linarith [hpost.2])
    have := hF (V s') h1
    omega

/-- The same for execution prefixes. -/
theorem whileMono_pre {I : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd ι S}
    (V : S → ℤ) (d : ℕ) (W : ℤ → ℕ) (F : ℤ → ℕ)
    (h_body : ∀ s, I s → b s = true →
      (∀ n, Pre Φ c s n → n ≤ W (V s)) ∧ ∀ t n, Exec Φ c s t n → I t ∧ V t + d ≤ V s)
    (h_pos : ∀ s, I s → b s = true → (d : ℤ) ≤ V s)
    (hF0 : ∀ X, w ≤ F X) (hmono : Monotone F)
    (hF : ∀ v, (d : ℤ) ≤ v → w + W v + F (v - d) ≤ F v)
    {s : S} {n : ℕ} (hp : Pre Φ (Cmd.while w b c) s n) :
    I s → n ≤ F (V s) := by
  generalize hW : Cmd.while w b c = Wc at hp
  induction hp with
  | stop => intro _; exact Nat.zero_le _
  | done he =>
    cases hW
    intro hI
    exact (whileMono_exec V d W F h_body h_pos hF0 hmono hF he hI).1
  | seqLeft => cases hW
  | seqRight => cases hW
  | iteTrue => cases hW
  | iteFalse => cases hW
  | call => cases hW
  | @whileBody _ _ _ s' _ hb p =>
    cases hW
    intro hI
    have hcost := (h_body s' hI hb).1 _ p
    have := hF (V s') (h_pos _ hI hb)
    omega
  | @whileNext _ _ _ s' u' _ _ hb e₁ _ ih =>
    cases hW
    intro hI
    have hbody := h_body s' hI hb
    have hpost := hbody.2 _ _ e₁
    have hcost := hbody.1 _ (Pre.done e₁)
    have hn := ih rfl hpost.1
    have hm := hmono (show V u' ≤ V s' - d by linarith [hpost.2])
    have := hF (V s') (h_pos _ hI hb)
    omega

/-- **Amortised loop rule, general form.** The bound is a monotone function `F` of the
    potential itself: `F X ≥ w` and `w + W v + F (v - d) ≤ F v` for `v ≥ d`. Unlike
    `valid_whileSum`, the body cost `W` need not grow with the potential: for
    `W v = a + c (K - v)` (an iteration costs more when more has been spent before it)
    the bound is `Σ_{m=1}^{N} (w + a + c (K - m d)) + w` with `N = ⌊K/d⌋`. -/
theorem valid_whileMono {I : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd ι S}
    (V : S → ℤ) (d : ℕ) (W : ℤ → ℕ) (F : ℤ → ℕ) (K : ℤ)
    (h_body : ∀ s, I s → b s = true →
      (∀ n, Pre Φ c s n → n ≤ W (V s)) ∧ ∀ t n, Exec Φ c s t n → I t ∧ V t + d ≤ V s)
    (h_pos : ∀ s, I s → b s = true → (d : ℤ) ≤ V s)
    (hF0 : ∀ X, w ≤ F X) (hmono : Monotone F)
    (hF : ∀ v, (d : ℤ) ≤ v → w + W v + F (v - d) ≤ F v) :
    Valid Φ (fun s => I s ∧ V s ≤ K) (Cmd.while w b c) (F K)
      (fun t => I t ∧ b t = false) := by
  intro s hs
  exact ⟨fun n hp => le_trans (whileMono_pre V d W F h_body h_pos hF0 hmono hF hp hs.1)
      (hmono hs.2),
    fun t n he => (whileMono_exec V d W F h_body h_pos hF0 hmono hF he hs.1).2⟩

end WhileSum

/-! ### The cost logic -/

/-- A set of cost triples, as a predicate. -/
abbrev Specs (ι S : Type) := (S → Prop) → Cmd ι S → ℕ → (S → Prop) → Prop

/-- **The cost logic.** `Derivable Φ Γ P c B Q`: the triple is derivable from the assumed
    triples `Γ`, the procedure bodies being `Φ`. Potentials are rational, as in the
    analyser.

    The rule `call` covers recursive (also mutually recursive) procedures: for a family
    of triples about calls, indexed by `κ` and ranked by natural numbers, the triple of
    index `k` is proved for the *body* of its procedure, assuming the triples of smaller
    rank for the calls it performs. -/
inductive Derivable (Φ : ι → Cmd ι S) :
    Specs ι S → (S → Prop) → Cmd ι S → ℕ → (S → Prop) → Prop where
  | skip (Γ : Specs ι S) (P : S → Prop) : Derivable Φ Γ P Cmd.skip 0 P
  | atom (Γ : Specs ι S) (P Q : S → Prop) (w : ℕ) (r : S → S → Prop)
      (h : ∀ s t, P s → r s t → Q t) : Derivable Φ Γ P (Cmd.atom w r) w Q
  | unreachable (Γ : Specs ι S) (c : Cmd ι S) (Q : S → Prop) :
      Derivable Φ Γ (fun _ => False) c 0 Q
  | seq {Γ : Specs ι S} {P R Q : S → Prop} {c₁ c₂ : Cmd ι S} {B₁ B₂ : ℕ}
      (h₁ : Derivable Φ Γ P c₁ B₁ R) (h₂ : Derivable Φ Γ R c₂ B₂ Q) :
      Derivable Φ Γ P (Cmd.seq c₁ c₂) (B₁ + B₂) Q
  | ite {Γ : Specs ι S} {P Q : S → Prop} {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd ι S} {B₁ B₂ : ℕ}
      (h₁ : Derivable Φ Γ (fun s => P s ∧ b s = true) c₁ B₁ Q)
      (h₂ : Derivable Φ Γ (fun s => P s ∧ b s = false) c₂ B₂ Q) :
      Derivable Φ Γ P (Cmd.ite w b c₁ c₂) (w + max B₁ B₂) Q
  | while {Γ : Specs ι S} {I C : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd ι S} {Wb : ℕ}
      (V : S → ℚ) (K : ℚ)
      (h_body : ∀ v, Derivable Φ Γ (fun s => I s ∧ b s = true ∧ V s = v) c Wb
        (fun t => I t ∧ V t ≤ v - 1))
      (h_pos : ∀ s, I s → b s = true → 1 ≤ V s)
      (hK : ∀ s, C s → V s ≤ K) :
      Derivable Φ Γ (fun s => I s ∧ C s) (Cmd.while w b c) (⌊K⌋₊ * (w + Wb) + w)
        (fun t => I t ∧ b t = false)
  | conseq {Γ : Specs ι S} {P P' Q Q' : S → Prop} {c : Cmd ι S} {B B' : ℕ}
      (hP : ∀ s, P' s → P s) (h : Derivable Φ Γ P c B Q) (hB : B ≤ B')
      (hQ : ∀ t, Q t → Q' t) : Derivable Φ Γ P' c B' Q'
  | assume {Γ : Specs ι S} {P Q : S → Prop} {c : Cmd ι S} {B : ℕ} (h : Γ P c B Q) :
      Derivable Φ Γ P c B Q
  | call {Γ : Specs ι S} {κ : Type} (Pk Qk : κ → S → Prop) (pk : κ → ι) (Bk : κ → ℕ)
      (rank : κ → ℕ) (w : ℕ)
      (h : ∀ k, Derivable Φ
        (fun P c B Q => Γ P c B Q ∨
          ∃ j, rank j < rank k ∧ P = Pk j ∧ c = Cmd.call w (pk j) ∧ B = w + Bk j ∧ Q = Qk j)
        (Pk k) (Φ (pk k)) (Bk k) (Qk k))
      (k : κ) : Derivable Φ Γ (Pk k) (Cmd.call w (pk k)) (w + Bk k) (Qk k)

/-- **Soundness of the cost logic.** If the assumed triples are valid, every derivable
    triple is valid: the derived number bounds the cost of every execution of the program
    from the precondition, terminated or not. -/
theorem soundness {Γ : Specs ι S} {P Q : S → Prop} {c : Cmd ι S} {B : ℕ}
    (h : Derivable Φ Γ P c B Q) :
    (∀ P c B Q, Γ P c B Q → Valid Φ P c B Q) → Valid Φ P c B Q := by
  induction h with
  | skip Γ P => intro _; exact valid_skip P
  | atom Γ P Q w r h => intro _; exact valid_atom P Q w r h
  | unreachable Γ c Q => intro _; exact valid_unreachable c 0 Q
  | seq _ _ ih₁ ih₂ => intro hΓ; exact valid_seq (ih₁ hΓ) (ih₂ hΓ)
  | ite _ _ ih₁ ih₂ => intro hΓ; exact valid_ite (ih₁ hΓ) (ih₂ hΓ)
  | «while» V K _ h_pos hK ih => intro hΓ; exact valid_while V K (fun v => ih v hΓ) h_pos hK
  | conseq hP _ hB hQ ih => intro hΓ; exact valid_conseq hP (ih hΓ) hB hQ
  | assume h => intro hΓ; exact hΓ _ _ _ _ h
  | call Pk Qk pk Bk rank w _ k ih =>
    intro hΓ
    have key : ∀ n, ∀ k, rank k = n →
        Valid Φ (Pk k) (Cmd.call w (pk k)) (w + Bk k) (Qk k) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n IH =>
        intro k hk
        apply valid_call
        apply ih k
        intro P c B Q hspec
        rcases hspec with hg | ⟨j, hj, rfl, rfl, rfl, rfl⟩
        · exact hΓ _ _ _ _ hg
        · exact IH (rank j) (hk ▸ hj) j rfl
    exact key _ k rfl

/-- The triples assumed when nothing is assumed. -/
def noSpecs : Specs ι S := fun _ _ _ _ => False

/-- Without assumptions: a program with a derivable bound has no execution of unbounded
    cost; in particular, if every loop test and every call has a positive weight, it has
    no infinite execution. -/
theorem derivable_cost_le {P Q : S → Prop} {c : Cmd ι S} {B : ℕ}
    (h : Derivable Φ noSpecs P c B Q) {s : S} (hP : P s) {n : ℕ} (hp : Pre Φ c s n) : n ≤ B :=
  ((soundness h (fun _ _ _ _ hf => hf.elim)) s hP).1 n hp

/-! ### Symbolic bounds and function summaries -/

/-- A **symbolic bound**: the bound `B s` is a function of the initial state (for a
    function body: of its parameters). It is expressed with numeric triples by
    quantifying over a budget `k`. -/
def ValidSym (Φ : ι → Cmd ι S) (P : S → Prop) (c : Cmd ι S) (B : S → ℕ) (Q : S → Prop) : Prop :=
  ∀ k, Valid Φ (fun s => P s ∧ B s ≤ k) c k Q

/-- A symbolic bound bounds, state by state, the cost of every execution prefix. -/
theorem validSym_iff {P Q : S → Prop} {c : Cmd ι S} {B : S → ℕ} :
    ValidSym Φ P c B Q ↔
      ∀ s, P s → (∀ n, Pre Φ c s n → n ≤ B s) ∧ (∀ t n, Exec Φ c s t n → Q t) := by
  constructor
  · intro h s hP
    exact h (B s) s ⟨hP, le_refl _⟩
  · intro h k s hs
    exact ⟨fun n hn => le_trans ((h s hs.1).1 n hn) hs.2, (h s hs.1).2⟩

/-- **Call rule for summaries.** If the body `c` of a function has the symbolic bound
    `B` under the precondition `P`, then at a call site where the state satisfies `P`
    and `B` is at most `k`, the call costs at most `k`. With `B` constant on a context
    this is the rule used for calling contexts. -/
theorem validSym_call {P P' Q : S → Prop} {c : Cmd ι S} {B : S → ℕ} {k : ℕ}
    (h : ValidSym Φ P c B Q) (hsite : ∀ s, P' s → P s ∧ B s ≤ k) : Valid Φ P' c k Q :=
  valid_conseq hsite (h k) (le_refl _) (fun _ hq => hq)

/-- Symbolic bounds compose in sequence when the bound of the second command, read in
    the intermediate state, is dominated by an expression `B₂'` of the initial state. -/
theorem validSym_seq {P R Q : S → Prop} {c₁ c₂ : Cmd ι S} {B₁ B₂ B₂' : S → ℕ}
    (h₁ : ValidSym Φ P c₁ B₁ R) (h₂ : ValidSym Φ R c₂ B₂ Q)
    (hdom : ∀ s u n, P s → Exec Φ c₁ s u n → B₂ u ≤ B₂' s) :
    ValidSym Φ P (Cmd.seq c₁ c₂) (fun s => B₁ s + B₂' s) Q := by
  rw [validSym_iff] at h₁ h₂ ⊢
  intro s hP
  have exec_bound : ∀ t n, Exec Φ (Cmd.seq c₁ c₂) s t n → n ≤ B₁ s + B₂' s ∧ Q t := by
    intro t n he
    cases he with
    | seq e₁ e₂ =>
      have hR := (h₁ s hP).2 _ _ e₁
      have a := (h₁ s hP).1 _ (Pre.done e₁)
      have b := (h₂ _ hR).1 _ (Pre.done e₂)
      have d := hdom _ _ _ hP e₁
      exact ⟨by omega, (h₂ _ hR).2 _ _ e₂⟩
  refine ⟨fun n hn => ?_, fun t n he => (exec_bound t n he).2⟩
  cases hn with
  | stop => exact Nat.zero_le _
  | done he => exact (exec_bound _ _ he).1
  | seqLeft hp =>
    have := (h₁ s hP).1 _ hp
    omega
  | seqRight e₁ p₂ =>
    have hR := (h₁ s hP).2 _ _ e₁
    have a := (h₁ s hP).1 _ (Pre.done e₁)
    have b := (h₂ _ hR).1 _ p₂
    have d := hdom _ _ _ hP e₁
    omega

/-! ### Examples: the hypotheses of the rules can be met -/

/-- The environment of a program without procedures. -/
def noProcs : Empty → Cmd Empty S := fun e => nomatch e

/-- `while (i < n) i := i + 1` on states `(i, n)`, with unit weights. -/
def countLoop : Cmd Empty (ℤ × ℤ) :=
  Cmd.while 1 (fun s => decide (s.1 < s.2)) (Cmd.atom 1 (fun s t => t = (s.1 + 1, s.2)))

/-- From `i = 0` and `n ≤ 10` the loop has the derivable bound `21 = 10 · (1 + 1) + 1`,
    with the potential `V = n - i`. -/
theorem countLoop_derivable :
    Derivable noProcs noSpecs (fun s : ℤ × ℤ => s.1 = 0 ∧ s.2 ≤ 10) countLoop 21
      (fun t => ¬ t.1 < t.2) := by
  have h := Derivable.while (Φ := noProcs) (Γ := noSpecs) (I := fun _ : ℤ × ℤ => True)
    (C := fun s => ((s.2 - s.1 : ℤ) : ℚ) ≤ 10) (w := 1)
    (b := fun s => decide (s.1 < s.2)) (c := Cmd.atom 1 (fun s t => t = (s.1 + 1, s.2)))
    (Wb := 1) (fun s => ((s.2 - s.1 : ℤ) : ℚ)) 10
    (fun v => Derivable.atom _ _ _ 1 _ (by
      rintro s t ⟨-, -, hv⟩ rfl
      refine ⟨trivial, ?_⟩
      push_cast at hv ⊢
      linarith))
    (by
      intro s _ hb
      have hlt : s.1 < s.2 := by simpa using hb
      have : (1 : ℤ) ≤ s.2 - s.1 := by omega
      show (1 : ℚ) ≤ ((s.2 - s.1 : ℤ) : ℚ)
      exact_mod_cast this)
    (fun s hs => hs)
  refine Derivable.conseq ?_ h ?_ ?_
  · rintro s ⟨h1, h2⟩
    refine ⟨trivial, ?_⟩
    have : s.2 - s.1 ≤ 10 := by omega
    exact_mod_cast this
  · have : ⌊(10 : ℚ)⌋₊ = 10 := by
      rw [show (10 : ℚ) = ((10 : ℕ) : ℚ) by norm_num, Nat.floor_natCast]
    rw [this]
  · rintro t ⟨-, hb⟩
    simpa using hb

/-- Hence every execution of the loop from such a state, terminated or not, costs at
    most `21`. -/
theorem countLoop_cost (s : ℤ × ℤ) (h1 : s.1 = 0) (h2 : s.2 ≤ 10) (n : ℕ)
    (hp : Pre noProcs countLoop s n) : n ≤ 21 :=
  derivable_cost_le countLoop_derivable ⟨h1, h2⟩ hp

/-- A recursive procedure on an integer `x`:
    `down() { if (x > 0) { x := x - 1; down() } }`, with unit weights. -/
def downBody : Unit → Cmd Unit ℤ := fun _ =>
  Cmd.ite 1 (fun x => decide (0 < x))
    (Cmd.seq (Cmd.atom 1 (fun x y => y = x - 1)) (Cmd.call 1 ())) Cmd.skip

/-- A call of `down` from `x ≤ n` costs at most `1 + (3n + 1)`: one unit for the call and
    three per level of recursion. The family of triples is indexed by `n`, which is also
    its rank. -/
theorem down_derivable (n : ℕ) :
    Derivable downBody noSpecs (fun x : ℤ => x ≤ n) (Cmd.call 1 ()) (1 + (3 * n + 1))
      (fun _ => True) := by
  refine Derivable.call (Φ := downBody) (Γ := noSpecs) (κ := ℕ)
    (fun k (x : ℤ) => x ≤ k) (fun _ _ => True) (fun _ => ()) (fun k => 3 * k + 1) id 1 ?_ n
  intro k
  show Derivable downBody _ (fun x : ℤ => x ≤ k)
    (Cmd.ite 1 (fun x => decide (0 < x))
      (Cmd.seq (Cmd.atom 1 (fun x y => y = x - 1)) (Cmd.call 1 ())) Cmd.skip) (3 * k + 1)
    (fun _ => True)
  cases k with
  | zero =>
    -- x ≤ 0: the test fails and the recursive branch is dead code.
    refine Derivable.conseq (P := fun x : ℤ => x ≤ (0 : ℕ)) (Q := fun _ => True)
      (B := 1 + max 0 0) (fun _ h => h) ?_ (by simp) (fun _ h => h)
    refine Derivable.ite ?_ ?_
    · refine Derivable.conseq (P := fun _ : ℤ => False) (Q := fun _ => True) (B := 0)
        ?_ (Derivable.unreachable _ _ _) (le_refl _) (fun _ h => h)
      rintro x ⟨h1, h2⟩
      have : 0 < x := by simpa using h2
      push_cast at h1
      omega
    · exact Derivable.conseq (fun _ _ => trivial) (Derivable.skip _ (fun _ => True)) (le_refl _)
        (fun _ h => h)
  | succ m =>
    refine Derivable.conseq (P := fun x : ℤ => x ≤ (m + 1 : ℕ)) (Q := fun _ => True)
      (B := 1 + max (1 + (1 + (3 * m + 1))) 0) (fun _ h => h) ?_ (by simp; omega) (fun _ h => h)
    refine Derivable.ite ?_ ?_
    · refine Derivable.seq (R := fun x : ℤ => x ≤ m) ?_ ?_
      · exact Derivable.atom _ _ _ 1 _ (by
          rintro x y ⟨h, -⟩ rfl
          push_cast at h
          omega)
      · exact Derivable.assume (Or.inr ⟨m, by simp, rfl, rfl, rfl, rfl⟩)
    · exact Derivable.conseq (fun _ _ => trivial) (Derivable.skip _ (fun _ => True)) (le_refl _)
        (fun _ h => h)

/-- Hence every execution of `down` from `x ≤ n`, terminated or not, costs at most
    `3n + 2`. -/
theorem down_cost (n : ℕ) (x : ℤ) (hx : x ≤ n) (c : ℕ)
    (hp : Pre downBody (Cmd.call 1 ()) x c) : c ≤ 3 * n + 2 := by
  have := derivable_cost_le (down_derivable n) hx hp
  omega

end ImperativeOptimization
