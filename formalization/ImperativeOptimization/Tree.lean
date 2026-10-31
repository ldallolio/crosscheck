import Mathlib.Tactic

namespace ImperativeOptimization

/--
Free term algebra of binary computation trees `T_Σ` for non-linear branching recursion.
-/
inductive BTree (α : Type) where
  | leaf : α → BTree α
  | node : BTree α → BTree α → BTree α

namespace BTree

variable {α : Type}

/-- Node count function representing total computational work. -/
def size : BTree α → ℕ
  | leaf _ => 1
  | node l r => 1 + l.size + r.size

/-- Leaf count of a computation tree. -/
def leafCount : BTree α → ℕ
  | leaf _ => 1
  | node l r => l.leafCount + r.leafCount

theorem leafCount_le_size (t : BTree α) : t.leafCount ≤ t.size := by
  induction t with
  | leaf _ => rfl
  | node l r ih_l ih_r =>
    dsimp [size, leafCount]
    omega

/-- Operadic tree grafting: substitutes `t₂` into all leaves of `t₁`. -/
def graft (t₁ t₂ : BTree α) : BTree α :=
  match t₁ with
  | leaf _ => t₂
  | node l r => node (graft l t₂) (graft r t₂)

infix:60 " ⊗ " => graft

/-- Tree Catamorphism (bottom-up fold) -/
def cata {α β : Type} (leafVal : α → β) (combine : β → β → β) : BTree α → β
  | leaf a => leafVal a
  | node l r => combine (cata leafVal combine l) (cata leafVal combine r)

theorem graft_size (t₁ t₂ : BTree α) :
    (t₁ ⊗ t₂).size = (t₁.size - t₁.leafCount) + t₁.leafCount * t₂.size := by
  induction t₁ with
  | leaf _ =>
    dsimp [graft, size, leafCount]
    omega
  | node l r ih_l ih_r =>
    dsimp [graft, size, leafCount]
    rw [ih_l, ih_r]
    have hl := leafCount_le_size l
    have hr := leafCount_le_size r
    have h_dist : (l.leafCount + r.leafCount) * t₂.size = l.leafCount * t₂.size + r.leafCount * t₂.size := by ring
    rw [h_dist]
    omega

/-- Tree Order-by-Composition `t₁ ⊑_tree t₂ ↔ ∃ t', t₂ = t₁ ⊗ t'`. -/
def TreeOrder (t₁ t₂ : BTree α) : Prop :=
  ∃ t' : BTree α, t₂ = t₁ ⊗ t'

infix:50 " ⊑_tree " => TreeOrder

theorem graft_unit_leaf (t : BTree Unit) : t ⊗ (BTree.leaf ()) = t := by
  induction t with
  | leaf u => cases u; rfl
  | node l r ih_l ih_r =>
    dsimp [graft]
    rw [ih_l, ih_r]

theorem treeOrder_refl (t : BTree Unit) : t ⊑_tree t :=
  ⟨BTree.leaf (), (graft_unit_leaf t).symm⟩

theorem graft_assoc (t₁ t₂ t₃ : BTree α) :
    (t₁ ⊗ t₂) ⊗ t₃ = t₁ ⊗ (t₂ ⊗ t₃) := by
  induction t₁ with
  | leaf _ => rfl
  | node l r ih_l ih_r =>
    dsimp [graft]
    rw [ih_l, ih_r]

theorem treeOrder_trans {t₁ t₂ t₃ : BTree α} (h1 : t₁ ⊑_tree t₂) (h2 : t₂ ⊑_tree t₃) :
    t₁ ⊑_tree t₃ := by
  rcases h1 with ⟨u1, rfl⟩
  rcases h2 with ⟨u2, rfl⟩
  use (u1 ⊗ u2)
  rw [graft_assoc]

/-- Full symmetric binary computation tree of depth `d`. -/
def fullTree (a : α) : ℕ → BTree α
  | 0 => BTree.leaf a
  | d + 1 => BTree.node (fullTree a d) (fullTree a d)

theorem fullTree_work_closed_form (a : α) (d : ℕ) :
    (fullTree a d).size = 2^(d + 1) - 1 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp [fullTree, size]
    rw [ih]
    have h2 : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
    rw [h2]
    have h_pow : 1 ≤ 2 ^ (d + 1) := Nat.one_le_pow (d + 1) 2 (by omega)
    omega

/-- Definition 15: Uniform operadic tree power B^⊗d (tree exponentiation) -/
def treePow (b : BTree α) : ℕ → BTree α
  | 0     => b
  | d + 1 => b ⊗ (treePow b d)

end BTree

end ImperativeOptimization
