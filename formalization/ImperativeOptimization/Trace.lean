import Mathlib.Tactic

namespace ImperativeOptimization

variable {Instr S : Type}

/--
The free monoid of finite execution traces `Σ*` under sequence concatenation `++`,
with identity element `[]` (empty trace / no-op).
-/
abbrev Trace (Instr : Type) := List Instr

/-- Intensional iteration functional: `t^n`. -/
def traceIter (t : Trace Instr) : ℕ → Trace Instr
  | 0 => []
  | n + 1 => (traceIter t n) ++ t

notation:max t " ^[" n "]" => traceIter t n

theorem traceIter_succ (t : Trace Instr) (n : ℕ) :
    t ^[n + 1] = t ++ (t ^[n]) := by
  induction n with
  | zero =>
    exact (List.append_nil t).symm
  | succ n ih =>
    calc
      t ^[n + 1 + 1] = (t ^[n + 1]) ++ t := rfl
      _ = (t ++ (t ^[n])) ++ t := by rw [ih]
      _ = t ++ ((t ^[n]) ++ t) := by rw [List.append_assoc]
      _ = t ++ (t ^[n + 1]) := rfl

/-- Operational execution cost function mapping a trace to its instruction count. -/
def cost (t : Trace Instr) : ℕ := t.length

theorem cost_additive (u v : Trace Instr) :
    cost (u ++ v) = cost u + cost v := List.length_append u v

theorem cost_iter (t : Trace Instr) (n : ℕ) :
    cost (t ^[n]) = n * cost t := by
  induction n with
  | zero =>
    dsimp [traceIter, cost]
    omega
  | succ n ih =>
    dsimp [traceIter]
    rw [cost_additive, ih]
    ring

/-- Intensional Order-by-Composition (Prefix Order) `u ⊑ w ↔ ∃ v, w = u ++ v`. -/
def OrderByComposition (u w : Trace Instr) : Prop :=
  ∃ v : Trace Instr, w = u ++ v

infix:50 " ⊑ " => OrderByComposition

theorem order_refl (t : Trace Instr) : t ⊑ t :=
  ⟨[], (List.append_nil t).symm⟩

theorem order_trans {u v w : Trace Instr} (h1 : u ⊑ v) (h2 : v ⊑ w) : u ⊑ w := by
  rcases h1 with ⟨r1, rfl⟩
  rcases h2 with ⟨r2, rfl⟩
  use r1 ++ r2
  rw [List.append_assoc]

theorem order_antisymm {u w : Trace Instr} (h1 : u ⊑ w) (h2 : w ⊑ u) : u = w := by
  rcases h1 with ⟨r1, hr1⟩
  rcases h2 with ⟨r2, hr2⟩
  have len1 : w.length = u.length + r1.length := by rw [hr1, List.length_append]
  have len2 : u.length = w.length + r2.length := by rw [hr2, List.length_append]
  have r1_nil : r1 = [] := List.length_eq_zero.mp (by omega)
  rw [r1_nil] at hr1
  rw [hr1]
  exact (List.append_nil u).symm

theorem iter_monotone (t : Trace Instr) {n m : ℕ} (h : n ≤ m) :
    (t ^[n]) ⊑ (t ^[m]) := by
  have h_ex : ∃ k, m = n + k := Nat.exists_eq_add_of_le h
  rcases h_ex with ⟨k, rfl⟩
  induction k with
  | zero =>
    rw [Nat.add_zero]
    exact order_refl (t ^[n])
  | succ k ih =>
    have h_le : n ≤ n + k := Nat.le_add_right n k
    have ih' := ih h_le
    have h_step : n + (k + 1) = (n + k) + 1 := by omega
    rw [h_step]
    dsimp [traceIter]
    rcases ih' with ⟨v, hv⟩
    use v ++ t
    rw [hv, List.append_assoc]

/-- Predicate stating that a trace execution exits a loop condition. -/
def ExitsAt (evalTrace : Trace Instr → Option S → Option S) (t : Trace Instr)
    (cond : S → Bool) (s₀ : S) (n : ℕ) : Prop :=
  match evalTrace (t ^[n]) (some s₀) with
  | some s => cond s = false
  | none => False

instance (evalTrace : Trace Instr → Option S → Option S) (t : Trace Instr)
    (cond : S → Bool) (s₀ : S) (n : ℕ) : Decidable (ExitsAt evalTrace t cond s₀ n) := by
  dsimp [ExitsAt]
  cases evalTrace (t ^[n]) (some s₀) with
  | none => exact Decidable.isFalse id
  | some s => exact inferInstance

/-- Theorem 1: Minimal Exiting Trace Existence via the Well-Ordering Principle. -/
theorem exists_minimal_iteration
    (evalTrace : Trace Instr → Option S → Option S) (t : Trace Instr)
    (cond : S → Bool) (s₀ : S)
    (h_term : ∃ n : ℕ, ExitsAt evalTrace t cond s₀ n) :
    ∃ n_bar : ℕ,
      ExitsAt evalTrace t cond s₀ n_bar ∧
      (∀ k < n_bar, ¬ ExitsAt evalTrace t cond s₀ k) ∧
      cost (t ^[n_bar]) = n_bar * cost t := by
  have _h_dec : DecidablePred (ExitsAt evalTrace t cond s₀) := inferInstance
  let n_bar := Nat.find h_term
  exact ⟨n_bar, Nat.find_spec h_term, fun k hk => Nat.find_min h_term hk, cost_iter t n_bar⟩

/- =========================================================================
   Nested Trace Exponentiation and Sequential Loops (Defs 8, Props 9 & 10)
   ========================================================================= -/

/-- Definition 8: Nested trace exponentiation (t₂^m)^(t₁^n) := (t₁ ++ t₂^m)^n -/
def nestedTrace (t₁ t₂ : Trace Instr) (n m : ℕ) : Trace Instr :=
  (t₁ ++ (t₂ ^[m])) ^[n]

/-- Proposition 9: Exact cost formula for nested loop traces -/
theorem nested_trace_cost (t₁ t₂ : Trace Instr) (n m : ℕ) :
    cost (nestedTrace t₁ t₂ n m) = n * cost t₁ + n * m * cost t₂ := by
  dsimp [nestedTrace]
  rw [cost_iter, cost_additive, cost_iter]
  ring

/-- Proposition 9: Prefix order inclusion for a single iteration -/
theorem nested_trace_prefix (t₁ t₂ : Trace Instr) (m : ℕ) {n : ℕ} (hn : n ≥ 1) :
    (t₁ ++ (t₂ ^[m])) ⊑ (nestedTrace t₁ t₂ n m) :=
  iter_monotone (t₁ ++ (t₂ ^[m])) hn

/-- Proposition 10: Sequential while loops trace cost is additive -/
theorem sequential_loops_cost (t₁ t₂ : Trace Instr) (n₁ n₂ : ℕ) :
    cost ((t₁ ^[n₁]) ++ (t₂ ^[n₂])) = n₁ * cost t₁ + n₂ * cost t₂ := by
  rw [cost_additive, cost_iter, cost_iter]

/-- Proposition 10: First loop is a prefix of sequential composition -/
theorem sequential_loops_prefix (t₁ t₂ : Trace Instr) (n₁ n₂ : ℕ) :
    (t₁ ^[n₁]) ⊑ ((t₁ ^[n₁]) ++ (t₂ ^[n₂])) := by
  use t₂ ^[n₂]

/- =========================================================================
   Structural Subsequence Order (Definition 8b & Proposition 9 bounds)
   ========================================================================= -/

/-- Structural Subsequence Order: `u ⊑_sub w` indicates `u` is embedded within `w` (sublist). -/
def SubsequenceOrder (u w : Trace Instr) : Prop :=
  u.Sublist w

infix:50 " ⊑_sub " => SubsequenceOrder

/-- Reflexivity of structural subsequence order. -/
theorem subseq_refl (t : Trace Instr) : t ⊑_sub t := by
  dsimp [SubsequenceOrder]
  induction t with
  | nil => exact List.Sublist.slnil
  | cons a l ih => exact List.Sublist.cons₂ a ih

/-- Monotonicity of cost under structural subsequence embedding. -/
theorem subseq_cost_le {u w : Trace Instr} (h : u ⊑_sub w) :
    cost u ≤ cost w := by
  dsimp [cost, SubsequenceOrder] at *
  induction h with
  | slnil => rfl
  | cons a _ ih =>
    dsimp
    omega
  | cons₂ a _ ih =>
    dsimp
    omega

/-- Prefix order strictly implies structural subsequence order. -/
theorem prefix_le_subseq {u w : Trace Instr} (h : u ⊑ w) : u ⊑_sub w := by
  rcases h with ⟨v, rfl⟩
  dsimp [SubsequenceOrder]
  induction u with
  | nil =>
    induction v with
    | nil => exact List.Sublist.slnil
    | cons b l ih => exact List.Sublist.cons b ih
  | cons a l ih =>
    exact List.Sublist.cons₂ a ih

/-- Outer loop component cost is bounded by nested trace cost. -/
theorem nested_trace_cost_outer_le (t₁ t₂ : Trace Instr) (n m : ℕ) :
    cost (t₁ ^[n]) ≤ cost (nestedTrace t₁ t₂ n m) := by
  rw [cost_iter, nested_trace_cost]
  omega

/-- Inner loop component cost (for n ≥ 1) is bounded by nested trace cost. -/
theorem nested_trace_cost_inner_le (t₁ t₂ : Trace Instr) {n : ℕ} (m : ℕ) (hn : n ≥ 1) :
    cost (t₂ ^[m]) ≤ cost (nestedTrace t₁ t₂ n m) := by
  have h_nm : m ≤ n * m := by
    have h1 : 1 * m ≤ n * m := Nat.mul_le_mul_right m hn
    rw [Nat.one_mul] at h1
    exact h1
  have h_cost : m * cost t₂ ≤ (n * m) * cost t₂ := Nat.mul_le_mul_right (cost t₂) h_nm
  rw [cost_iter, nested_trace_cost]
  omega

/-- Accumulated inner loop work cost is bounded by nested trace cost. -/
theorem nested_trace_cost_accum_inner_le (t₁ t₂ : Trace Instr) (n m : ℕ) :
    cost (t₂ ^[n * m]) ≤ cost (nestedTrace t₁ t₂ n m) := by
  rw [cost_iter, nested_trace_cost]
  omega

end ImperativeOptimization
