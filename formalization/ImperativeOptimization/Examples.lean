/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Logic.Function.Iterate
import ImperativeOptimization.Ranking
import ImperativeOptimization.Recursion

namespace ImperativeOptimization.Examples

/-!
# Formalization of the paper's worked examples

Each example is checked at three levels: the closed form of the iterates, the
*minimality* of the iteration count / recursion depth / call tree, and agreement
with the big-step semantics of the corresponding control structure.
-/

/--
Example: Parametric While Loop
  int i = R; int x = 1; int y = 2;
  while (i++ < 13) {
    i = i + 1; x = y + 2; y = x + 3;
  }

Modelling note: the guard `i++ < 13` compares the current `i` and then increments
it. One full iteration (successful guard + body) therefore maps
`(i, x, y) ↦ (i + 2, y + 2, y + 5)`, and the guard is evaluated on the value of `i`
at the start of the iteration. The final failing guard adds one more increment,
so the program's final value of `i` is `R + 2 n̄ + 1`.
-/

structure ParametricState where
  i : Int
  x : Int
  y : Int

def parametricLoopStep (s : ParametricState) : ParametricState :=
  { i := s.i + 2,
    x := s.y + 2,
    y := s.y + 5 }

/-- Lemma: Iterating `parametricLoopStep` k times increases `i` by `2 * k`. -/
theorem parametricLoopStep_iter_i (s : ParametricState) (k : ℕ) :
    ((parametricLoopStep^[k]) s).i = s.i + 2 * (k : Int) := by
  induction k generalizing s with
  | zero =>
    dsimp
    ring
  | succ k ih =>
    dsimp [Function.iterate_succ']
    rw [ih (parametricLoopStep s)]
    dsimp [parametricLoopStep]
    ring

/-- Lemma: Iterating `parametricLoopStep` k times increases `y` by `5 * k`. -/
theorem parametricLoopStep_iter_y (s : ParametricState) (k : ℕ) :
    ((parametricLoopStep^[k]) s).y = s.y + 5 * (k : Int) := by
  induction k generalizing s with
  | zero =>
    dsimp
    ring
  | succ k ih =>
    dsimp [Function.iterate_succ']
    rw [ih (parametricLoopStep s)]
    dsimp [parametricLoopStep]
    ring

/-- Lemma: Iterating `parametricLoopStep` (m + 1) times produces `x = s.y + 5 * m + 2`.
    Proved directly from `parametricLoopStep_iter_y` without induction. -/
theorem parametricLoopStep_iter_x_succ (s : ParametricState) (m : ℕ) :
    ((parametricLoopStep^[m + 1]) s).x = s.y + 5 * (m : Int) + 2 := by
  rw [Function.iterate_succ_apply']
  dsimp [parametricLoopStep]
  rw [parametricLoopStep_iter_y]

/-- Closed-form theorem for loop termination: after n iterations, i ≥ 13. -/
theorem parametric_loop_closed_form (R : Int) (hR : R < 13) :
    let n : ℕ := Int.toNat ((13 - R + 1) / 2)
    let s_final := (parametricLoopStep^[n]) { i := R, x := 1, y := 2 }
    s_final.i ≥ 13 := by
  intro n s_final
  dsimp [s_final]
  rw [parametricLoopStep_iter_i]
  dsimp [n]
  have h_pos : 0 ≤ (13 - R + 1) / 2 := by omega
  have h_toNat : ((Int.toNat ((13 - R + 1) / 2) : Int)) = (13 - R + 1) / 2 :=
    Int.toNat_of_nonneg h_pos
  rw [h_toNat]
  omega

/-- The loop as a recurrence constraint: guard `i < 13`, one guard evaluation plus
    three assignments per iteration. -/
def parametricLoop : LoopConstraint ParametricState :=
  { cond := fun s => decide (s.i < 13),
    stepState := parametricLoopStep,
    stepCost := 4 }

/-- The closed-form iteration count `n̄ = ⌈(13 - R) / 2⌉` (clipped at `0`). -/
def parametricIterations (R : Int) : ℕ := Int.toNat ((13 - R + 1) / 2)

/-- `n̄ = ⌈(13 - R)/2⌉` is *the* solution of the loop minimisation problem, for every
    initial value `R` (including `R ≥ 13`, where `n̄ = 0`). -/
theorem parametric_loop_minimal (R : Int) :
    isLoopSolution parametricLoop { i := R, x := 1, y := 2 } (parametricIterations R) := by
  constructor
  · show decide (((parametricLoopStep^[parametricIterations R]) _).i < 13) = false
    rw [parametricLoopStep_iter_i, decide_eq_false_iff_not]
    simp only [parametricIterations]
    omega
  · intro k hk
    show decide (((parametricLoopStep^[k]) _).i < 13) = true
    rw [parametricLoopStep_iter_i]
    simp only [decide_eq_true_eq]
    simp only [parametricIterations] at hk
    omega

/-- The big-step semantics of the loop reaches the state predicted by `solveLoop`. -/
theorem parametric_loop_bigstep (R : Int) :
    WhileBigStep parametricLoop.cond (fun s => some (parametricLoop.stepState s))
      { i := R, x := 1, y := 2 }
      (solveLoop parametricLoop { i := R, x := 1, y := 2 } (parametricIterations R)).1 :=
  solveLoop_sound parametricLoop _ _ (parametric_loop_minimal R)

/-- `V(s) = 13 - s.i` is a ranking potential with step decrease `Δ = 2`, and the
    induced bound `⌈V(s₀)/Δ⌉` is exactly the true iteration count: the Lyapunov
    envelope is tight on this example. -/
theorem parametric_loop_ranking (R : Int) (n : ℕ)
    (h_run : ∀ k < n, parametricLoop.cond
      ((parametricLoop.stepState^[k]) { i := R, x := 1, y := 2 }) = true) :
    n ≤ parametricIterations R := by
  have h := ranking_bound parametricLoop.cond parametricLoop.stepState
    (fun s => 13 - s.i) 2 (by norm_num)
    (fun s _ => by
      show 13 - (s.i + 2) ≤ 13 - s.i - 2
      omega)
    (fun s hs => by
      have hs' : s.i < 13 := by simpa [parametricLoop] using hs
      show 0 < 13 - s.i
      omega)
    { i := R, x := 1, y := 2 } n h_run
  have he : rankBound (13 - R) 2 = parametricIterations R := by
    unfold rankBound parametricIterations
    congr 1
    omega
  exact he ▸ h

/-- Closed-form theorem for y: y = 5n + 2. -/
theorem parametric_loop_y (R : Int) (n : ℕ) :
    ((parametricLoopStep^[n]) { i := R, x := 1, y := 2 }).y = 5 * (n : Int) + 2 := by
  rw [parametricLoopStep_iter_y]
  dsimp
  ring

/-- Closed-form theorem for x: for any iteration m + 1 ≥ 1, x = 5(m + 1) - 1. -/
theorem parametric_loop_x (R : Int) (m : ℕ) :
    ((parametricLoopStep^[m + 1]) { i := R, x := 1, y := 2 }).x = 5 * (m + 1 : Int) - 1 := by
  rw [parametricLoopStep_iter_x_succ]
  dsimp
  ring

/--
Example: Infinite While Loop
  int i = 0;
  while (i != 1) { i = 0; }
-/

def infiniteLoopCond (i : Int) : Bool := i ≠ 1
def infiniteLoopStep (_i : Int) : Int := 0

theorem infinite_loop_no_finite_exit (n : ℕ) :
    (infiniteLoopStep^[n]) 0 ≠ 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    dsimp [Function.iterate_succ']
    exact ih

/-- The loop has no big-step derivation: it diverges. -/
theorem infinite_loop_diverges (sf : Int) :
    ¬ WhileBigStep infiniteLoopCond (fun i => some (infiniteLoopStep i)) 0 sf := by
  intro h
  rcases (whileBigStep_total_iff _ _ _ _).mp h with ⟨n, ⟨hn, _⟩, _⟩
  have hne := infinite_loop_no_finite_exit n
  simp [infiniteLoopCond] at hn
  exact hne hn

/--
Example: Linear Recursion
  int foo(int a) {
    if (a > 4) a = foo(a - 2) + 3;
    return a + 6;
  }
  foo(10);
-/

def fooLinearRec : LinearRecurrence Int :=
  { cond := fun a => a > 4,
    fwd := fun a => a - 2,
    back := fun a => a + 3 + 6,  -- +3 from assignment, +6 from fall-through return
    stop := fun a => a + 6 }

theorem linear_recursion_solution :
    solveLinearRecurrence fooLinearRec 10 3 = 37 := by
  dsimp [solveLinearRecurrence, fooLinearRec]

/-- `n̄ = 3` is the minimal recursion depth of `foo(10)`. -/
theorem linear_recursion_depth :
    MinimalIter fooLinearRec.cond fooLinearRec.fwd 10 3 := by
  refine ⟨by decide, ?_⟩
  intro k hk
  interval_cases k <;> decide

/-- The big-step semantics of `foo(10)` returns `37`. -/
theorem linear_recursion_bigstep :
    FramedBigStep fooLinearRec.toFramed 10 37 :=
  (linRec_iff fooLinearRec 10 37).mpr
    ⟨3, linear_recursion_depth, linear_recursion_solution.symm⟩

/--
Example: Non-Linear Binary Recursion
  int foo(int x) {
    if (x > 0) return foo(x - 1) + foo(x - 1);
    return 1;
  }
  foo(2);
-/

theorem binary_recursion_work_count :
    (BTree.fullTree () 2).size = 7 := by
  exact BTree.fullTree_work_closed_form () 2

/-- Proving the synthesized return value at the root is 4 -/
theorem binary_recursion_return_value :
    BTree.cata (fun _ => (1 : Int)) (fun l r => l + r) (BTree.fullTree () 2) = 4 := by
  rfl

/-- The recursion scheme of the binary countdown. -/
def binCountdown : TreeRecurrence Int Int :=
  { cond := fun x => decide (x > 0),
    fwdL := fun x => x - 1,
    fwdR := fun x => x - 1,
    combine := fun l r => l + r,
    stop := fun _ => 1 }

/-- The call tree of `foo(2)` is the full binary tree of depth `2`
    (hence, by `exec_least`, the minimal feasible tree). -/
theorem binary_recursion_exec_tree :
    IsExecTree binCountdown (BTree.fullTree () 2) 2 := by
  simp [IsExecTree, BTree.fullTree, binCountdown]

/-- The big-step semantics of `foo(2)` returns `4`. -/
theorem binary_recursion_bigstep : TreeBigStep binCountdown 2 4 :=
  (treeBigStep_iff binCountdown 2 4).mpr ⟨BTree.fullTree () 2, binary_recursion_exec_tree, rfl⟩

/-- `V(x) = max(x, 0)` is a depth ranking potential: the call tree of `foo(x)` has at
    most `2^(x+1) - 1` nodes. For `x = 2` the envelope `7` is attained. -/
theorem binary_recursion_envelope {t : BTree Unit} {x : Int} (h : IsExecTree binCountdown t x) :
    t.size ≤ 2 ^ (Int.toNat x + 1) - 1 :=
  exec_size_le binCountdown Int.toNat
    (fun s hs => by
      have hs' : s > 0 := by simpa [binCountdown] using hs
      show Int.toNat (s - 1) < Int.toNat s ∧ Int.toNat (s - 1) < Int.toNat s
      omega)
    h

end ImperativeOptimization.Examples
