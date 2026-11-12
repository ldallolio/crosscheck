/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic
import ImperativeOptimization.Trace

namespace ImperativeOptimization

/-!
# Branch rule and dominance
The branch rule of the timing schema (paper: `prop:tropical-dominance`,
`prop:tropical-collapse`): `branch_supremum_bound`, `condTrace`, `condTrace_cost_le`.

The big-O preorder `≼_O` and the lemmas `add_dominated_by_max`, `max_dominated_by_add`
are not used by the paper (removed in the Nov 2026 simplification); they are kept as
auxiliary material. Ranking potentials live in `Ranking.lean`.
-/

/-- Big-O preorder on cost functions (not used by the paper). -/
def AsympDominates (f g : ℕ → ℕ) : Prop :=
  ∃ C N₀, ∀ n ≥ N₀, f n ≤ C * g n

infix:50 " ≼_O " => AsympDominates

theorem dominance_refl (f : ℕ → ℕ) : f ≼_O f :=
  ⟨1, 0, fun _ _ => by omega⟩

theorem dominance_trans {f g h : ℕ → ℕ} (h1 : f ≼_O g) (h2 : g ≼_O h) : f ≼_O h := by
  rcases h1 with ⟨C₁, N₁, hf⟩
  rcases h2 with ⟨C₂, N₂, hg⟩
  use C₁ * C₂, max N₁ N₂
  intro n hn
  have hn₁ : n ≥ N₁ := le_of_max_le_left hn
  have hn₂ : n ≥ N₂ := le_of_max_le_right hn
  have h_step1 := hf n hn₁
  have h_step2 := hg n hn₂
  calc
    f n ≤ C₁ * g n := h_step1
    _   ≤ C₁ * (C₂ * h n) := Nat.mul_le_mul_left C₁ h_step2
    _   = (C₁ * C₂) * h n := by ring

/-- Branch rule on numbers: the cost of a conditional is at most the guard cost plus the
    maximum of the branch costs (paper: `prop:tropical-dominance`). -/
theorem branch_supremum_bound (cost_c cost_then cost_else : ℕ) (cond_val : Bool) :
    cost_c + (if cond_val then cost_then else cost_else) ≤
      cost_c + max cost_then cost_else := by
  cases cond_val with
  | false =>
    dsimp
    have h : cost_else ≤ max cost_then cost_else := Nat.le_max_right cost_then cost_else
    omega
  | true =>
    dsimp
    have h : cost_then ≤ max cost_then cost_else := Nat.le_max_left cost_then cost_else
    omega

/-- Sequential composition is dominated by the branch-wise maximum:
    `f + g ≼_O max(f, g)` (with constant `C = 2`). -/
theorem add_dominated_by_max (f g : ℕ → ℕ) :
    (fun n => f n + g n) ≼_O (fun n => max (f n) (g n)) :=
  ⟨2, 0, fun n _ => by
    show f n + g n ≤ 2 * max (f n) (g n)
    have h1 := Nat.le_max_left (f n) (g n)
    have h2 := Nat.le_max_right (f n) (g n)
    omega⟩

/-- Conversely `max(f, g) ≼_O f + g`, so both envelopes are `Θ`-equivalent. -/
theorem max_dominated_by_add (f g : ℕ → ℕ) :
    (fun n => max (f n) (g n)) ≼_O (fun n => f n + g n) :=
  ⟨1, 0, fun n _ => by
    show max (f n) (g n) ≤ 1 * (f n + g n)
    have h : max (f n) (g n) ≤ f n + g n :=
      Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
    omega⟩

/-- Path trace emitted by a conditional `if c then t_then else t_else` at state `s`:
    the guard trace followed by the trace of the branch actually taken. -/
def condTrace {Instr S : Type} (c : S → Bool) (t_c t_then t_else : Trace Instr) (s : S) :
    Trace Instr :=
  t_c ++ (if c s then t_then else t_else)

/-- Tropical branch collapsing on traces: whatever the state, the executed trace
    of a conditional costs at most `‖t_c‖ + max(‖t_then‖, ‖t_else‖)`. -/
theorem condTrace_cost_le {Instr S : Type} (c : S → Bool) (t_c t_then t_else : Trace Instr)
    (s : S) :
    cost (condTrace c t_c t_then t_else s) ≤ cost t_c + max (cost t_then) (cost t_else) := by
  unfold condTrace
  rw [cost_additive]
  cases c s <;> simp

end ImperativeOptimization
