/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic
import ImperativeOptimization.WhileLoop

namespace ImperativeOptimization

/-!
# Certificates checked by the CrossCheck analyser

The Clang plugin (`clang-plugin/`) does not trust its SMT solver: every bound it
reports follows from a small certificate. This module proves that the certificates
are sound.

* `ranking_bound_floor`: a potential `V` with values in an ordered field (the plugin
  uses `ℚ`) that decreases by at least `1` along every step of a transition
  *relation* and is at least `1` whenever a step is taken bounds the length of every
  run by `⌊V s₀⌋`. Being relational, it covers nondeterministic updates (unknown
  inputs, havocked variables) and partial, faulting updates.
* `farkas_sound`: the easy direction of Farkas' Lemma, used to reduce the universally
  quantified conditions on `V` to linear constraints on its coefficients.
* `while_cost_bound`: the cost formula `K · (guard + body) + guard` of a loop with at
  most `K` iterations.
* `run_invariant`, `ranking_bound_floor_of_invariant`: the conditions on `V` are only
  needed on the states of an inductive invariant. This is how the analyser uses the
  loop invariants it proves and the facts of a *calling context* (intervals of the
  arguments at a call site, which speak of the parameters' initial values and are
  therefore preserved by every step).
* `call_bound_of_context`: a cost bound proved for a function under a context holds
  for every call whose argument satisfies the context.
-/

variable {S : Type} {α : Type} [LinearOrderedField α]

/-- Along a run of `step`, a potential that decreases by at least `1` per step has
    decreased by at least `k` after `k` steps. -/
theorem run_descent (step : S → S → Prop) (V : S → α)
    (h_decr : ∀ s s', step s s' → V s' ≤ V s - 1)
    (σ : ℕ → S) (n : ℕ) (h_run : ∀ k < n, step (σ k) (σ (k + 1))) :
    ∀ k ≤ n, V (σ k) ≤ V (σ 0) - k := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := h_decr _ _ (h_run k (by omega))
    push_cast
    linarith

variable [FloorSemiring α]

/-- **Ranking certificate (relational, field-valued).** If `V` decreases by at least
    `1` along every step and `V s ≥ 1` whenever a step is taken from `s`, every run
    of `n` steps satisfies `n ≤ ⌊V (σ 0)⌋`. -/
theorem ranking_bound_floor (step : S → S → Prop) (V : S → α)
    (h_decr : ∀ s s', step s s' → V s' ≤ V s - 1)
    (h_pos : ∀ s s', step s s' → 1 ≤ V s)
    (σ : ℕ → S) (n : ℕ) (h_run : ∀ k < n, step (σ k) (σ (k + 1))) :
    n ≤ ⌊V (σ 0)⌋₊ := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ m =>
    have hd := run_descent step V h_decr σ (m + 1) h_run m (by omega)
    have hp := h_pos _ _ (h_run m (by omega))
    apply Nat.le_floor
    push_cast
    linarith

/-- The same bound for any upper bound `K` of the potential on entry: this is the
    number the analyser reports. -/
theorem ranking_bound_of_le (step : S → S → Prop) (V : S → α)
    (h_decr : ∀ s s', step s s' → V s' ≤ V s - 1)
    (h_pos : ∀ s s', step s s' → 1 ≤ V s)
    (σ : ℕ → S) (n : ℕ) (h_run : ∀ k < n, step (σ k) (σ (k + 1)))
    (K : α) (hK : V (σ 0) ≤ K) :
    n ≤ ⌊K⌋₊ :=
  le_trans (ranking_bound_floor step V h_decr h_pos σ n h_run) (Nat.floor_mono hK)

/-- Specialisation to a deterministic loop `while cond do s := f s`. -/
theorem while_ranking_floor (cond : S → Bool) (f : S → S) (V : S → α)
    (h_decr : ∀ s, cond s = true → V (f s) ≤ V s - 1)
    (h_pos : ∀ s, cond s = true → 1 ≤ V s)
    (s₀ : S) (n : ℕ) (h_run : ∀ k < n, cond (f^[k] s₀) = true) :
    n ≤ ⌊V s₀⌋₊ := by
  have h := ranking_bound_floor (fun s s' => cond s = true ∧ s' = f s) V
    (fun s s' hs => by rw [hs.2]; exact h_decr s hs.1)
    (fun s _ hs => h_pos s hs.1)
    (fun k => f^[k] s₀) n
    (fun k hk => ⟨h_run k hk, Function.iterate_succ_apply' f k s₀⟩)
  simpa using h

/-- Specialisation to a loop whose body may fault (`f s = none`): the bound holds
    for every run of successful iterations. -/
theorem partial_ranking_floor (cond : S → Bool) (f : S → Option S) (V : S → α)
    (h_decr : ∀ s s', cond s = true → f s = some s' → V s' ≤ V s - 1)
    (h_pos : ∀ s, cond s = true → 1 ≤ V s)
    (σ : ℕ → S) (n : ℕ) (h_run : ∀ k < n, cond (σ k) = true ∧ f (σ k) = some (σ (k + 1))) :
    n ≤ ⌊V (σ 0)⌋₊ :=
  ranking_bound_floor (fun s s' => cond s = true ∧ f s = some s') V
    (fun s s' hs => h_decr s s' hs.1 hs.2) (fun s _ hs => h_pos s hs.1) σ n h_run

/-- **Farkas certificate (soundness).** Let `a i · x ≤ b i` be premises and
    `c · x ≤ d` a target. If non-negative multipliers `lam` satisfy
    `c = Σ lam i • a i` and `Σ lam i * b i ≤ d`, the premises imply the target. -/
theorem farkas_sound {ι κ : Type} [Fintype ι] [Fintype κ]
    (a : ι → κ → ℚ) (b : ι → ℚ) (lam : ι → ℚ) (c : κ → ℚ) (d : ℚ)
    (hlam : ∀ i, 0 ≤ lam i)
    (hc : ∀ j, c j = ∑ i, lam i * a i j)
    (hd : ∑ i, lam i * b i ≤ d)
    (x : κ → ℚ) (hx : ∀ i, ∑ j, a i j * x j ≤ b i) :
    ∑ j, c j * x j ≤ d := by
  have h1 : ∑ j, c j * x j = ∑ i, lam i * ∑ j, a i j * x j := by
    simp only [hc, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  rw [h1]
  exact le_trans
    (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (hlam i))) hd

/-- The form used by the analyser: premises `p i · x + q i ≤ 0`, target
    `c · x + d ≤ 0`, certificate `c = Σ lam i • p i` and `d ≤ Σ lam i * q i`. -/
theorem farkas_sound_affine {ι κ : Type} [Fintype ι] [Fintype κ]
    (p : ι → κ → ℚ) (q : ι → ℚ) (lam : ι → ℚ) (c : κ → ℚ) (d : ℚ)
    (hlam : ∀ i, 0 ≤ lam i)
    (hc : ∀ j, c j = ∑ i, lam i * p i j)
    (hd : d ≤ ∑ i, lam i * q i)
    (x : κ → ℚ) (hx : ∀ i, ∑ j, p i j * x j + q i ≤ 0) :
    ∑ j, c j * x j + d ≤ 0 := by
  have h := farkas_sound p (fun i => -q i) lam c (-d) hlam hc
    (by simp only [mul_neg, Finset.sum_neg_distrib]; linarith) x
    (fun i => by
      show ∑ j, p i j * x j ≤ -q i
      have := hx i
      linarith)
  linarith

/-- **Loop cost formula.** A loop that performs `n ≤ K` iterations, each made of a
    guard evaluation of cost at most `Wg` and a body of cost at most `Wb`, followed
    by the final failing guard, costs at most `K * (Wg + Wb) + Wg`. -/
theorem while_cost_bound {Instr : Type} (g τ : S → Trace Instr) (f : S → S)
    (Wg Wb K n : ℕ) (hg : ∀ s, cost (g s) ≤ Wg) (hb : ∀ s, cost (τ s) ≤ Wb)
    (hn : n ≤ K) (s : S) :
    cost (runTrace (fun s => g s ++ τ s) f n s ++ g (f^[n] s)) ≤ K * (Wg + Wb) + Wg := by
  rw [cost_additive]
  have h1 := runTrace_cost_le (fun s => g s ++ τ s) f (Wg + Wb)
    (fun s => by rw [cost_additive]; have := hg s; have := hb s; omega) n s
  have h2 := hg (f^[n] s)
  have h3 : n * (Wg + Wb) ≤ K * (Wg + Wb) := Nat.mul_le_mul_right _ hn
  omega

/-- **Invariants along a run.** A predicate that holds initially and is preserved by
    every step holds at every state of a run. The analyser uses it for the facts it
    keeps at a loop exit, whether the loop is left through its guard or through a
    `break`: the loop head it leaves from satisfies the invariant. -/
theorem run_invariant (step : S → S → Prop) (I : S → Prop)
    (h_inv : ∀ s s', I s → step s s' → I s')
    (σ : ℕ → S) (n : ℕ) (h_run : ∀ k < n, step (σ k) (σ (k + 1))) (h0 : I (σ 0)) :
    ∀ k ≤ n, I (σ k) := by
  intro k hk
  induction k with
  | zero => exact h0
  | succ k ih => exact h_inv _ _ (ih (by omega)) (h_run k (by omega))

/-- **Ranking certificate under an invariant.** The descent and positivity conditions
    are required only on states that satisfy an inductive invariant `I` which holds
    initially. `I` stands for the loop invariants the analyser proves and for the
    facts of the calling context (constraints on the parameters' initial values). -/
theorem ranking_bound_floor_of_invariant (step : S → S → Prop) (V : S → α) (I : S → Prop)
    (h_inv : ∀ s s', I s → step s s' → I s')
    (h_decr : ∀ s s', I s → step s s' → V s' ≤ V s - 1)
    (h_pos : ∀ s s', I s → step s s' → 1 ≤ V s)
    (σ : ℕ → S) (n : ℕ) (h_run : ∀ k < n, step (σ k) (σ (k + 1))) (h0 : I (σ 0)) :
    n ≤ ⌊V (σ 0)⌋₊ :=
  ranking_bound_floor (fun s s' => I s ∧ step s s') V
    (fun s s' hs => h_decr s s' hs.1 hs.2) (fun s s' hs => h_pos s s' hs.1 hs.2) σ n
    (fun k hk => ⟨run_invariant step I h_inv σ n h_run h0 k (by omega), h_run k hk⟩)

/-- The same with an upper bound `K` of the potential that is valid under the
    context `C` of the initial state: the number reported for a calling context. -/
theorem ranking_bound_of_context (step : S → S → Prop) (V : S → α) (I C : S → Prop)
    (h_inv : ∀ s s', I s → step s s' → I s')
    (h_decr : ∀ s s', I s → step s s' → V s' ≤ V s - 1)
    (h_pos : ∀ s s', I s → step s s' → 1 ≤ V s)
    (K : α) (hK : ∀ s, C s → V s ≤ K)
    (σ : ℕ → S) (n : ℕ) (h_run : ∀ k < n, step (σ k) (σ (k + 1)))
    (h0 : I (σ 0)) (hC : C (σ 0)) :
    n ≤ ⌊K⌋₊ :=
  le_trans (ranking_bound_floor_of_invariant step V I h_inv h_decr h_pos σ n h_run h0)
    (Nat.floor_mono (hK _ hC))

/-- **Call rule.** If the cost of a function is at most `B` for every argument that
    satisfies a context `C`, then calls whose arguments all satisfy `C` cost at most
    `B` each. The analyser takes for `C` an interval that contains the argument in
    every state in which the call is evaluated. -/
theorem call_bound_of_context {A : Type} (callCost : A → ℕ) (C : A → Prop) (B : ℕ)
    (h : ∀ a, C a → callCost a ≤ B) (args : List A) (hC : ∀ a ∈ args, C a) :
    (args.map callCost).sum ≤ args.length * B := by
  induction args with
  | nil => simp
  | cons a t ih =>
    have h1 := h a (hC a (List.mem_cons_self a t))
    have h2 := ih (fun x hx => hC x (List.mem_cons_of_mem a hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.succ_mul]
    omega

end ImperativeOptimization
