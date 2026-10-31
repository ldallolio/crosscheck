import Mathlib.Logic.Function.Iterate
import ImperativeOptimization.OperationalSemantics

namespace ImperativeOptimization.Examples

/-!
# Section 4 Examples Formalization
-/

/--
Example 4.1: Parametric While Loop
  int i = R; int x = 1; int y = 2;
  while (i++ < 13) {
    i = i + 1; x = y + 2; y = x + 3;
  }
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
    push_cast
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
    push_cast
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
Example 4.2: Infinite While Loop
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

/--
Example 4.3: Linear Recursion
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

/--
Example 4.4: Non-Linear Binary Recursion
  int foo(int x) {
    if (x > 0) return foo(x - 1) + foo(x - 1);
    return 1;
  }
  foo(2);
-/

theorem binary_recursion_work_count :
    (BTree.fullTree () 2).size = 7 := by
  exact BTree.fullTree_work_closed_form () 2

/-- Example 4.4: Proving the synthesized return value at the root is 4 -/
theorem binary_recursion_return_value :
    BTree.cata (fun _ => (1 : Int)) (fun l r => l + r) (BTree.fullTree () 2) = 4 := by
  rfl

end ImperativeOptimization.Examples
