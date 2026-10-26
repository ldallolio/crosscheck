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
  have h_dec : DecidablePred (ExitsAt evalTrace t cond s₀) := inferInstance
  let n_bar := Nat.find h_term
  use n_bar
  refine ⟨Nat.find_spec h_term, ?_, ?_⟩
  · intro k hk
    exact Nat.find_min h_term hk
  · exact cost_iter t n_bar

end ImperativeOptimization
