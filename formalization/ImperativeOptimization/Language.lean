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

* `Cmd S`: commands over a state type `S`: `skip`, atomic actions with a weight and a
  (possibly nondeterministic or partial) transition relation, sequence, conditional and
  `while`, the tests having a weight too.
* `Exec c s t n`: `c` started in `s` terminates in `t` with cost `n` (big-step).
* `Pre c s n`: some execution of `c` from `s`, **not necessarily terminated**, has
  accumulated cost `n`. Bounding `Pre` bounds diverging executions as well.
* `Valid P c B Q`: from every state satisfying `P`, every execution prefix of `c` costs
  at most `B`, and every terminating execution ends in a state satisfying `Q`.
* `valid_skip`, `valid_atom`, `valid_seq`, `valid_ite`, `valid_while`, `valid_conseq`:
  the rules. `valid_while` is the ranking certificate under an invariant and a context
  (`Certificate.ranking_bound_of_context`) combined with the loop cost formula.
* `Derivable`: the same rules as an inductive proof system; `soundness` shows that
  everything derivable is valid.
* `ValidSym`: bounds that are functions of the initial state (*symbolic* bounds), with
  the rule `validSym_call` that instantiates such a summary at a call site.

Not in the language: recursive procedures (see `Recursion` and `Arity`).
-/

/-- Commands. `atom w r` performs a step of the relation `r` at cost `w`; the tests of
    `ite` and `while` cost `w`. -/
inductive Cmd (S : Type) where
  | skip : Cmd S
  | atom (w : ℕ) (r : S → S → Prop) : Cmd S
  | seq (c₁ c₂ : Cmd S) : Cmd S
  | ite (w : ℕ) (b : S → Bool) (c₁ c₂ : Cmd S) : Cmd S
  | while (w : ℕ) (b : S → Bool) (c : Cmd S) : Cmd S

variable {S : Type}

/-- Big-step semantics with cost: `Exec c s t n` means that `c`, started in `s`, can
    terminate in `t` after spending `n`. -/
inductive Exec : Cmd S → S → S → ℕ → Prop where
  | skip (s : S) : Exec Cmd.skip s s 0
  | atom {w : ℕ} {r : S → S → Prop} {s t : S} (h : r s t) : Exec (Cmd.atom w r) s t w
  | seq {c₁ c₂ : Cmd S} {s u t : S} {n₁ n₂ : ℕ} (h₁ : Exec c₁ s u n₁) (h₂ : Exec c₂ u t n₂) :
      Exec (Cmd.seq c₁ c₂) s t (n₁ + n₂)
  | iteTrue {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd S} {s t : S} {n : ℕ}
      (hb : b s = true) (h : Exec c₁ s t n) : Exec (Cmd.ite w b c₁ c₂) s t (w + n)
  | iteFalse {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd S} {s t : S} {n : ℕ}
      (hb : b s = false) (h : Exec c₂ s t n) : Exec (Cmd.ite w b c₁ c₂) s t (w + n)
  | whileFalse {w : ℕ} {b : S → Bool} {c : Cmd S} {s : S} (hb : b s = false) :
      Exec (Cmd.while w b c) s s w
  | whileTrue {w : ℕ} {b : S → Bool} {c : Cmd S} {s u t : S} {n₁ n₂ : ℕ}
      (hb : b s = true) (h₁ : Exec c s u n₁) (h₂ : Exec (Cmd.while w b c) u t n₂) :
      Exec (Cmd.while w b c) s t (w + n₁ + n₂)

/-- Cost of execution prefixes: `Pre c s n` means that an execution of `c` from `s`,
    possibly interrupted or still running, has spent `n`. -/
inductive Pre : Cmd S → S → ℕ → Prop where
  | stop (c : Cmd S) (s : S) : Pre c s 0
  | done {c : Cmd S} {s t : S} {n : ℕ} (h : Exec c s t n) : Pre c s n
  | seqLeft {c₁ c₂ : Cmd S} {s : S} {n : ℕ} (h : Pre c₁ s n) : Pre (Cmd.seq c₁ c₂) s n
  | seqRight {c₁ c₂ : Cmd S} {s u : S} {n₁ n₂ : ℕ} (h₁ : Exec c₁ s u n₁) (h₂ : Pre c₂ u n₂) :
      Pre (Cmd.seq c₁ c₂) s (n₁ + n₂)
  | iteTrue {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd S} {s : S} {n : ℕ}
      (hb : b s = true) (h : Pre c₁ s n) : Pre (Cmd.ite w b c₁ c₂) s (w + n)
  | iteFalse {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd S} {s : S} {n : ℕ}
      (hb : b s = false) (h : Pre c₂ s n) : Pre (Cmd.ite w b c₁ c₂) s (w + n)
  | whileBody {w : ℕ} {b : S → Bool} {c : Cmd S} {s : S} {n : ℕ}
      (hb : b s = true) (h : Pre c s n) : Pre (Cmd.while w b c) s (w + n)
  | whileNext {w : ℕ} {b : S → Bool} {c : Cmd S} {s u : S} {n₁ n₂ : ℕ}
      (hb : b s = true) (h₁ : Exec c s u n₁) (h₂ : Pre (Cmd.while w b c) u n₂) :
      Pre (Cmd.while w b c) s (w + n₁ + n₂)

/-- **Validity of a cost triple.** From every state satisfying `P`: every execution
    prefix of `c` costs at most `B`, and every terminating execution ends in `Q`. -/
def Valid (P : S → Prop) (c : Cmd S) (B : ℕ) (Q : S → Prop) : Prop :=
  ∀ s, P s → (∀ n, Pre c s n → n ≤ B) ∧ (∀ t n, Exec c s t n → Q t)

/-- Under a valid triple, terminating executions cost at most `B` too. -/
theorem Valid.exec_le {P Q : S → Prop} {c : Cmd S} {B : ℕ} (h : Valid P c B Q)
    {s t : S} {n : ℕ} (hP : P s) (he : Exec c s t n) : n ≤ B :=
  (h s hP).1 n (Pre.done he)

theorem valid_skip (P : S → Prop) : Valid P Cmd.skip 0 P := by
  intro s hP
  refine ⟨fun n h => ?_, fun t n h => ?_⟩
  · cases h with
    | stop => exact le_refl _
    | done h => cases h; exact le_refl _
  · cases h; exact hP

theorem valid_atom (P Q : S → Prop) (w : ℕ) (r : S → S → Prop)
    (h : ∀ s t, P s → r s t → Q t) : Valid P (Cmd.atom w r) w Q := by
  intro s hP
  refine ⟨fun n hn => ?_, fun t n he => ?_⟩
  · cases hn with
    | stop => exact Nat.zero_le _
    | done he => cases he; exact le_refl _
  · cases he with
    | atom hr => exact h s t hP hr

/-- **Sequence: costs add.** -/
theorem valid_seq {P R Q : S → Prop} {c₁ c₂ : Cmd S} {B₁ B₂ : ℕ}
    (h₁ : Valid P c₁ B₁ R) (h₂ : Valid R c₂ B₂ Q) : Valid P (Cmd.seq c₁ c₂) (B₁ + B₂) Q := by
  intro s hP
  have exec_bound : ∀ t n, Exec (Cmd.seq c₁ c₂) s t n → n ≤ B₁ + B₂ ∧ Q t := by
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
theorem valid_ite {P Q : S → Prop} {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd S} {B₁ B₂ : ℕ}
    (h₁ : Valid (fun s => P s ∧ b s = true) c₁ B₁ Q)
    (h₂ : Valid (fun s => P s ∧ b s = false) c₂ B₂ Q) :
    Valid P (Cmd.ite w b c₁ c₂) (w + max B₁ B₂) Q := by
  intro s hP
  have exec_bound : ∀ t n, Exec (Cmd.ite w b c₁ c₂) s t n → n ≤ w + max B₁ B₂ ∧ Q t := by
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

/-- **Consequence (context rule).** A triple can be used under a stronger precondition,
    with a larger bound and a weaker postcondition. In particular a bound derived for a
    command under a context `P` holds wherever the state satisfies `P`. -/
theorem valid_conseq {P P' Q Q' : S → Prop} {c : Cmd S} {B B' : ℕ}
    (hP : ∀ s, P' s → P s) (h : Valid P c B Q) (hB : B ≤ B') (hQ : ∀ t, Q t → Q' t) :
    Valid P' c B' Q' := by
  intro s hs
  exact ⟨fun n hn => le_trans ((h s (hP s hs)).1 n hn) hB,
    fun t n he => hQ t ((h s (hP s hs)).2 t n he)⟩

section While

variable {α : Type} [LinearOrderedField α]

/-- Terminating executions of a loop under a ranking certificate: with invariant `I`
    and potential `V < m + 1`, at most `m` iterations are performed. -/
theorem while_exec_bound {I : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd S} {Wb : ℕ}
    (V : S → α)
    (h_body : ∀ v, Valid (fun s => I s ∧ b s = true ∧ V s = v) c Wb
      (fun t => I t ∧ V t ≤ v - 1))
    (h_pos : ∀ s, I s → b s = true → 1 ≤ V s)
    {s t : S} {n : ℕ} (he : Exec (Cmd.while w b c) s t n) :
    ∀ m : ℕ, I s → V s < m + 1 → n ≤ m * (w + Wb) + w ∧ I t ∧ b t = false := by
  generalize hW : Cmd.while w b c = W at he
  induction he with
  | skip => cases hW
  | atom => cases hW
  | seq => cases hW
  | iteTrue => cases hW
  | iteFalse => cases hW
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
theorem while_pre_bound {I : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd S} {Wb : ℕ}
    (V : S → α)
    (h_body : ∀ v, Valid (fun s => I s ∧ b s = true ∧ V s = v) c Wb
      (fun t => I t ∧ V t ≤ v - 1))
    (h_pos : ∀ s, I s → b s = true → 1 ≤ V s)
    {s : S} {n : ℕ} (hp : Pre (Cmd.while w b c) s n) :
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
theorem valid_while {I C : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd S} {Wb : ℕ}
    (V : S → α) (K : α)
    (h_body : ∀ v, Valid (fun s => I s ∧ b s = true ∧ V s = v) c Wb
      (fun t => I t ∧ V t ≤ v - 1))
    (h_pos : ∀ s, I s → b s = true → 1 ≤ V s)
    (hK : ∀ s, C s → V s ≤ K) :
    Valid (fun s => I s ∧ C s) (Cmd.while w b c) (⌊K⌋₊ * (w + Wb) + w)
      (fun t => I t ∧ b t = false) := by
  intro s hs
  have hV : V s < (⌊K⌋₊ : α) + 1 := lt_of_le_of_lt (hK s hs.2) (Nat.lt_floor_add_one K)
  exact ⟨fun n hp => while_pre_bound V h_body h_pos hp _ hs.1 hV,
    fun t n he => (while_exec_bound V h_body h_pos he _ hs.1 hV).2⟩

end While

/-- **The cost logic.** Derivations of cost triples; potentials are rational, as in the
    analyser. -/
inductive Derivable : (S → Prop) → Cmd S → ℕ → (S → Prop) → Prop where
  | skip (P : S → Prop) : Derivable P Cmd.skip 0 P
  | atom (P Q : S → Prop) (w : ℕ) (r : S → S → Prop) (h : ∀ s t, P s → r s t → Q t) :
      Derivable P (Cmd.atom w r) w Q
  | seq {P R Q : S → Prop} {c₁ c₂ : Cmd S} {B₁ B₂ : ℕ}
      (h₁ : Derivable P c₁ B₁ R) (h₂ : Derivable R c₂ B₂ Q) :
      Derivable P (Cmd.seq c₁ c₂) (B₁ + B₂) Q
  | ite {P Q : S → Prop} {w : ℕ} {b : S → Bool} {c₁ c₂ : Cmd S} {B₁ B₂ : ℕ}
      (h₁ : Derivable (fun s => P s ∧ b s = true) c₁ B₁ Q)
      (h₂ : Derivable (fun s => P s ∧ b s = false) c₂ B₂ Q) :
      Derivable P (Cmd.ite w b c₁ c₂) (w + max B₁ B₂) Q
  | while {I C : S → Prop} {w : ℕ} {b : S → Bool} {c : Cmd S} {Wb : ℕ} (V : S → ℚ) (K : ℚ)
      (h_body : ∀ v, Derivable (fun s => I s ∧ b s = true ∧ V s = v) c Wb
        (fun t => I t ∧ V t ≤ v - 1))
      (h_pos : ∀ s, I s → b s = true → 1 ≤ V s)
      (hK : ∀ s, C s → V s ≤ K) :
      Derivable (fun s => I s ∧ C s) (Cmd.while w b c) (⌊K⌋₊ * (w + Wb) + w)
        (fun t => I t ∧ b t = false)
  | conseq {P P' Q Q' : S → Prop} {c : Cmd S} {B B' : ℕ}
      (hP : ∀ s, P' s → P s) (h : Derivable P c B Q) (hB : B ≤ B') (hQ : ∀ t, Q t → Q' t) :
      Derivable P' c B' Q'

/-- **Soundness of the cost logic.** Every derivable triple is valid: the derived number
    bounds the cost of every execution of the program from the precondition, terminated
    or not. -/
theorem soundness {P Q : S → Prop} {c : Cmd S} {B : ℕ} (h : Derivable P c B Q) :
    Valid P c B Q := by
  induction h with
  | skip P => exact valid_skip P
  | atom P Q w r h => exact valid_atom P Q w r h
  | seq _ _ ih₁ ih₂ => exact valid_seq ih₁ ih₂
  | ite _ _ ih₁ ih₂ => exact valid_ite ih₁ ih₂
  | «while» V K _ h_pos hK ih => exact valid_while V K ih h_pos hK
  | conseq hP _ hB hQ ih => exact valid_conseq hP ih hB hQ

/-- A program with a derivable bound has no execution of unbounded cost; in particular,
    if every loop test has a positive weight, it has no infinite execution. -/
theorem derivable_cost_le {P Q : S → Prop} {c : Cmd S} {B : ℕ} (h : Derivable P c B Q)
    {s : S} (hP : P s) {n : ℕ} (hp : Pre c s n) : n ≤ B :=
  ((soundness h) s hP).1 n hp

/-! ### Symbolic bounds and function summaries -/

/-- A **symbolic bound**: the bound `B s` is a function of the initial state (for a
    function body: of its parameters). It is expressed with numeric triples by
    quantifying over a budget `k`. -/
def ValidSym (P : S → Prop) (c : Cmd S) (B : S → ℕ) (Q : S → Prop) : Prop :=
  ∀ k, Valid (fun s => P s ∧ B s ≤ k) c k Q

/-- A symbolic bound bounds, state by state, the cost of every execution prefix. -/
theorem validSym_iff {P Q : S → Prop} {c : Cmd S} {B : S → ℕ} :
    ValidSym P c B Q ↔
      ∀ s, P s → (∀ n, Pre c s n → n ≤ B s) ∧ (∀ t n, Exec c s t n → Q t) := by
  constructor
  · intro h s hP
    exact h (B s) s ⟨hP, le_refl _⟩
  · intro h k s hs
    exact ⟨fun n hn => le_trans ((h s hs.1).1 n hn) hs.2, (h s hs.1).2⟩

/-- **Call rule for summaries.** If the body `c` of a function has the symbolic bound
    `B` under the precondition `P`, then at a call site where the state satisfies `P`
    and `B` is at most `k`, the call costs at most `k`. With `B` constant on a context
    this is the rule used for calling contexts. -/
theorem validSym_call {P P' Q : S → Prop} {c : Cmd S} {B : S → ℕ} {k : ℕ}
    (h : ValidSym P c B Q) (hsite : ∀ s, P' s → P s ∧ B s ≤ k) : Valid P' c k Q :=
  valid_conseq hsite (h k) (le_refl _) (fun _ hq => hq)

/-- Symbolic bounds compose in sequence when the bound of the second command, read in
    the intermediate state, is dominated by an expression `B₂'` of the initial state. -/
theorem validSym_seq {P R Q : S → Prop} {c₁ c₂ : Cmd S} {B₁ B₂ B₂' : S → ℕ}
    (h₁ : ValidSym P c₁ B₁ R) (h₂ : ValidSym R c₂ B₂ Q)
    (hdom : ∀ s u n, P s → Exec c₁ s u n → B₂ u ≤ B₂' s) :
    ValidSym P (Cmd.seq c₁ c₂) (fun s => B₁ s + B₂' s) Q := by
  rw [validSym_iff] at h₁ h₂ ⊢
  intro s hP
  have exec_bound : ∀ t n, Exec (Cmd.seq c₁ c₂) s t n → n ≤ B₁ s + B₂' s ∧ Q t := by
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

/-! ### An example: the hypotheses of the rules can be met -/

/-- `while (i < n) i := i + 1` on states `(i, n)`, with unit weights. -/
def countLoop : Cmd (ℤ × ℤ) :=
  Cmd.while 1 (fun s => decide (s.1 < s.2)) (Cmd.atom 1 (fun s t => t = (s.1 + 1, s.2)))

/-- From `i = 0` and `n ≤ 10` the loop has the derivable bound `21 = 10 · (1 + 1) + 1`,
    with the potential `V = n - i`. -/
theorem countLoop_derivable :
    Derivable (fun s : ℤ × ℤ => s.1 = 0 ∧ s.2 ≤ 10) countLoop 21 (fun t => ¬ t.1 < t.2) := by
  have h := Derivable.while (S := ℤ × ℤ) (I := fun _ => True)
    (C := fun s => ((s.2 - s.1 : ℤ) : ℚ) ≤ 10) (w := 1)
    (b := fun s => decide (s.1 < s.2)) (c := Cmd.atom 1 (fun s t => t = (s.1 + 1, s.2)))
    (Wb := 1) (fun s => ((s.2 - s.1 : ℤ) : ℚ)) 10
    (fun v => Derivable.atom _ _ 1 _ (by
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
    (hp : Pre countLoop s n) : n ≤ 21 :=
  derivable_cost_le countLoop_derivable ⟨h1, h2⟩ hp

end ImperativeOptimization
