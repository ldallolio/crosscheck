/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic
import ImperativeOptimization.WhileLoop

namespace ImperativeOptimization

/-!
# Ranking potentials (Lyapunov bounds) and WCET envelopes

Let `cond` be the continuation condition of a loop and `f` its (total) state update.
An integer-valued *ranking potential* `V` with step decrease `Δ > 0` satisfies, on
every continuing state `s` (i.e. `cond s = true`):

* descent:    `V (f s) ≤ V s - Δ`,
* positivity: `0 < V s`.

Then the loop terminates, and its minimal exiting iteration count is at most
`rankBound (V s₀) Δ = ⌈V s₀ / Δ⌉` (`ranking_terminates`). Combined with the
worst-case step bound `runTrace_cost_le` this yields the WCET envelope
`wcet_bound`.
-/

variable {S : Type}

/-- The iteration bound `⌈V₀ / Δ⌉` (clipped at `0`). -/
def rankBound (V₀ Δ : ℤ) : ℕ := Int.toNat ((V₀ + Δ - 1) / Δ)

/-- Inductive descent: while the loop keeps running, the potential has decreased
    by at least `k · Δ` after `k` iterations. -/
theorem ranking_descent (cond : S → Bool) (f : S → S) (V : S → ℤ) (Δ : ℤ)
    (h_decr : ∀ s, cond s = true → V (f s) ≤ V s - Δ)
    (s₀ : S) (k : ℕ) (h_run : ∀ j < k, cond (f^[j] s₀) = true) :
    V (f^[k] s₀) ≤ V s₀ - k * Δ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun j hj => h_run j (by omega))
    have hstep := h_decr (f^[k] s₀) (h_run k (by omega))
    rw [← Function.iterate_succ_apply' f k s₀] at hstep
    have hcast : ((k + 1 : ℕ) : ℤ) * Δ = k * Δ + Δ := by
      push_cast
      ring
    linarith

/-- **Lyapunov iteration bound.** If the loop has performed `n` iterations
    (the continuation condition held at steps `0, …, n-1`), then `n ≤ ⌈V s₀ / Δ⌉`. -/
theorem ranking_bound (cond : S → Bool) (f : S → S) (V : S → ℤ) (Δ : ℤ) (hΔ : 0 < Δ)
    (h_decr : ∀ s, cond s = true → V (f s) ≤ V s - Δ)
    (h_pos : ∀ s, cond s = true → 0 < V s)
    (s₀ : S) (n : ℕ) (h_run : ∀ k < n, cond (f^[k] s₀) = true) :
    n ≤ rankBound (V s₀) Δ := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ m =>
    have hdesc := ranking_descent cond f V Δ h_decr s₀ m (fun j hj => h_run j (by omega))
    have hpos := h_pos (f^[m] s₀) (h_run m (by omega))
    have hlt : (m : ℤ) * Δ < V s₀ := by linarith
    have hle : (m : ℤ) * Δ + 1 ≤ V s₀ := Int.add_one_le_iff.mpr hlt
    have h1 : ((m : ℤ) + 1) * Δ ≤ V s₀ + Δ - 1 := by
      have : ((m : ℤ) + 1) * Δ = m * Δ + Δ := by ring
      linarith
    have h2 : (m : ℤ) + 1 ≤ (V s₀ + Δ - 1) / Δ := Int.le_ediv_of_mul_le hΔ h1
    unfold rankBound
    omega

/-- **Termination with a certified bound.** A ranking potential guarantees that a
    minimal exiting iteration count exists and is bounded by `⌈V s₀ / Δ⌉`. -/
theorem ranking_terminates (cond : S → Bool) (f : S → S) (V : S → ℤ) (Δ : ℤ) (hΔ : 0 < Δ)
    (h_decr : ∀ s, cond s = true → V (f s) ≤ V s - Δ)
    (h_pos : ∀ s, cond s = true → 0 < V s) (s₀ : S) :
    ∃ n, MinimalIter cond f s₀ n ∧ n ≤ rankBound (V s₀) Δ := by
  have hex : ∃ n, cond (f^[n] s₀) = false := by
    by_contra hne
    have hall : ∀ k, cond (f^[k] s₀) = true := by
      intro k
      cases hk : cond (f^[k] s₀) with
      | true => rfl
      | false => exact absurd ⟨k, hk⟩ hne
    have hb := ranking_bound cond f V Δ hΔ h_decr h_pos s₀ (rankBound (V s₀) Δ + 1)
      (fun k _ => hall k)
    omega
  have hmin : ∀ k < Nat.find hex, cond (f^[k] s₀) = true := by
    intro k hk
    simpa using Nat.find_min hex hk
  exact ⟨Nat.find hex, ⟨Nat.find_spec hex, hmin⟩,
    ranking_bound cond f V Δ hΔ h_decr h_pos s₀ _ hmin⟩

/-- **WCET envelope.** If every path through the loop body costs at most `W` and `V`
    is a ranking potential, the trace executed by the loop (up to any iteration `n`
    it actually reaches) costs at most `⌈V s₀ / Δ⌉ · W`. -/
theorem wcet_bound {Instr : Type} (τ : S → Trace Instr) (W : ℕ) (hW : ∀ s, cost (τ s) ≤ W)
    (cond : S → Bool) (f : S → S) (V : S → ℤ) (Δ : ℤ) (hΔ : 0 < Δ)
    (h_decr : ∀ s, cond s = true → V (f s) ≤ V s - Δ)
    (h_pos : ∀ s, cond s = true → 0 < V s)
    (s₀ : S) (n : ℕ) (h_run : ∀ k < n, cond (f^[k] s₀) = true) :
    cost (runTrace τ f n s₀) ≤ rankBound (V s₀) Δ * W :=
  le_trans (runTrace_cost_le τ f W hW n s₀)
    (Nat.mul_le_mul_right W (ranking_bound cond f V Δ hΔ h_decr h_pos s₀ n h_run))

/-- WCET envelope for an arbitrary weighted cost norm. -/
theorem wcet_bound_weighted {Instr : Type} (ω : Instr → ℕ) (τ : S → Trace Instr) (W : ℕ)
    (hW : ∀ s, wcost ω (τ s) ≤ W)
    (cond : S → Bool) (f : S → S) (V : S → ℤ) (Δ : ℤ) (hΔ : 0 < Δ)
    (h_decr : ∀ s, cond s = true → V (f s) ≤ V s - Δ)
    (h_pos : ∀ s, cond s = true → 0 < V s)
    (s₀ : S) (n : ℕ) (h_run : ∀ k < n, cond (f^[k] s₀) = true) :
    wcost ω (runTrace τ f n s₀) ≤ rankBound (V s₀) Δ * W :=
  le_trans (runTrace_wcost_le ω τ f W hW n s₀)
    (Nat.mul_le_mul_right W (ranking_bound cond f V Δ hΔ h_decr h_pos s₀ n h_run))

/-- Nested loops: if the outer body costs at most `c₁` plus an inner loop of at most
    `M` iterations of cost at most `c₂` each, then `n` outer iterations cost at most
    `n · c₁ + n · M · c₂`. -/
theorem nested_wcet_bound {Instr : Type} (τ : S → Trace Instr) (f : S → S) (c₁ c₂ M : ℕ)
    (hτ : ∀ s, cost (τ s) ≤ c₁ + M * c₂) (n : ℕ) (s : S) :
    cost (runTrace τ f n s) ≤ n * c₁ + n * M * c₂ := by
  have h := runTrace_cost_le τ f (c₁ + M * c₂) hτ n s
  have he : n * (c₁ + M * c₂) = n * c₁ + n * M * c₂ := by ring
  omega

end ImperativeOptimization
