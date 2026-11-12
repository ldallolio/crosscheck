/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Logic.Function.Iterate
import ImperativeOptimization.Trace
import ImperativeOptimization.Tree

namespace ImperativeOptimization

/-- Representation of an imperative loop recurrence constraint system. -/
structure LoopConstraint (S : Type) where
  cond : S → Bool
  stepState : S → S
  stepCost : ℕ

/-- Evaluates the terminal state and total work of a loop given its minimal cycle count `n_bar`. -/
def solveLoop {S : Type} (lc : LoopConstraint S) (s₀ : S) (n_bar : ℕ) : S × ℕ :=
  let s_final := (lc.stepState^[n_bar]) s₀
  let total_cost := n_bar * lc.stepCost
  (s_final, total_cost)

/-- `n` is the minimal iteration count at which the continuation condition `cond`
    fails along the orbit of `f` from `s₀` (Kleene's μ-operator on the orbit). -/
def MinimalIter {S : Type} (cond : S → Bool) (f : S → S) (s₀ : S) (n : ℕ) : Prop :=
  cond ((f^[n]) s₀) = false ∧ ∀ k < n, cond ((f^[k]) s₀) = true

/-- The minimal iteration count is unique. -/
theorem MinimalIter.unique {S : Type} {cond : S → Bool} {f : S → S} {s₀ : S} {n m : ℕ}
    (hn : MinimalIter cond f s₀ n) (hm : MinimalIter cond f s₀ m) : n = m := by
  rcases Nat.lt_trichotomy n m with h | h | h
  · have h1 := hm.2 n h
    rw [hn.1] at h1
    cases h1
  · exact h
  · have h1 := hn.2 m h
    rw [hm.1] at h1
    cases h1

/-- Verification that the solved state satisfies the exit condition (minimally). -/
def isLoopSolution {S : Type} (lc : LoopConstraint S) (s₀ : S) (n_bar : ℕ) : Prop :=
  MinimalIter lc.cond lc.stepState s₀ n_bar

/-- Linear recursion transformation into forward/backward recurrence composition. -/
structure LinearRecurrence (S : Type) where
  cond : S → Bool
  fwd : S → S
  back : S → S
  stop : S → S

def solveLinearRecurrence {S : Type} (lr : LinearRecurrence S) (s₀ : S) (n_bar : ℕ) : S :=
  let s_base := (lr.fwd^[n_bar]) s₀
  let s_stopped := lr.stop s_base
  (lr.back^[n_bar]) s_stopped

end ImperativeOptimization