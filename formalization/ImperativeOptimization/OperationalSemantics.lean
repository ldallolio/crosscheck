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

/-- Verification that the solved state satisfies the exit condition. -/
def isLoopSolution {S : Type} (lc : LoopConstraint S) (s₀ : S) (n_bar : ℕ) : Prop :=
  lc.cond ((lc.stepState^[n_bar]) s₀) = false ∧
  ∀ k < n_bar, lc.cond ((lc.stepState^[k]) s₀) = true

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