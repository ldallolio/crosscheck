import Mathlib.Tactic

namespace ImperativeOptimization

/-!
# Asymptotic Dominance and Tropical Bounding Envelopes
Formalization of Definitions 11, Proposition 12, and Proposition 15.
-/

/-- Definition 11: Asymptotic Dominance Preorder (Big-O) on cost functions. -/
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

/-- Proposition 12 (Branch Supremum): Cost of conditional execution is bounded by the max of branches. -/
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

/-- Proposition 15 (Ranking Function / Lyapunov Bound):
    If a state measure V decreases by at least Δ > 0 on every step,
    the number of executed steps k is bounded by V(s₀) / Δ. -/
theorem ranking_bound (V : ℕ → ℕ) (Δ : ℕ) (_hΔ : Δ > 0)
    (h_decr : ∀ k, V (k + 1) + Δ ≤ V k) (k : ℕ) :
    k * Δ ≤ V 0 := by
  have h_strong : ∀ m, m * Δ + V m ≤ V 0 := by
    intro m
    induction m with
    | zero =>
      dsimp
      omega
    | succ m ih =>
      have h_step := h_decr m
      have h_mul : (m + 1) * Δ = m * Δ + Δ := by ring
      rw [h_mul]
      omega
  have hm := h_strong k
  omega

end ImperativeOptimization
