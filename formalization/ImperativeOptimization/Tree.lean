/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
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

theorem size_pos (t : BTree α) : 0 < t.size := by
  cases t with
  | leaf _ => exact Nat.one_pos
  | node l r =>
    dsimp [size]
    omega

/-- In a binary tree, internal nodes are one fewer than leaves: `|T| + 1 = 2 · leaves(T)`. -/
theorem size_add_one (t : BTree α) : t.size + 1 = 2 * t.leafCount := by
  induction t with
  | leaf _ => rfl
  | node l r ih_l ih_r =>
    dsimp [size, leafCount]
    omega

/-- Depth (height) of a computation tree: the maximal recursion depth. -/
def depth : BTree α → ℕ
  | leaf _ => 0
  | node l r => 1 + max l.depth r.depth

theorem leafCount_le_size (t : BTree α) : t.leafCount ≤ t.size := by
  induction t with
  | leaf _ => rfl
  | node l r ih_l ih_r =>
    dsimp [size, leafCount]
    omega

/-- Grafting `t₁ ⊗ t₂`: substitutes `t₂` for every leaf of `t₁` (paper: `def:tree-algebra`). -/
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

/-- Grafting multiplies leaf frontiers. -/
theorem graft_leafCount (t₁ t₂ : BTree α) :
    (t₁ ⊗ t₂).leafCount = t₁.leafCount * t₂.leafCount := by
  induction t₁ with
  | leaf _ =>
    dsimp [graft, leafCount]
    omega
  | node l r ih_l ih_r =>
    dsimp [graft, leafCount]
    rw [ih_l, ih_r]
    ring

/-- Uniform grafting order `t₁ ⊑_graft t₂ ↔ ∃ t', t₂ = t₁ ⊗ t'` (not the paper's tree
    order, which is `TreePrefix` below; kept as auxiliary material)
    (the same tree is grafted into every leaf). -/
def GraftOrder (t₁ t₂ : BTree α) : Prop :=
  ∃ t' : BTree α, t₂ = t₁ ⊗ t'

infix:50 " ⊑_graft " => GraftOrder

theorem graft_unit_leaf (t : BTree Unit) : t ⊗ (BTree.leaf ()) = t := by
  induction t with
  | leaf u => cases u; rfl
  | node l r ih_l ih_r =>
    dsimp [graft]
    rw [ih_l, ih_r]

theorem graftOrder_refl (t : BTree Unit) : t ⊑_graft t :=
  ⟨BTree.leaf (), (graft_unit_leaf t).symm⟩

theorem graft_assoc (t₁ t₂ t₃ : BTree α) :
    (t₁ ⊗ t₂) ⊗ t₃ = t₁ ⊗ (t₂ ⊗ t₃) := by
  induction t₁ with
  | leaf _ => rfl
  | node l r ih_l ih_r =>
    dsimp [graft]
    rw [ih_l, ih_r]

theorem graftOrder_trans {t₁ t₂ t₃ : BTree α} (h1 : t₁ ⊑_graft t₂) (h2 : t₂ ⊑_graft t₃) :
    t₁ ⊑_graft t₃ := by
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

theorem fullTree_depth (a : α) (d : ℕ) : (fullTree a d).depth = d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp [fullTree, depth]
    rw [ih]
    omega

/- =========================================================================
   Tree order-by-composition (structural prefix order)
   ========================================================================= -/

/-- Tree order-by-composition: `t₁ ⊑_tree t₂` iff `t₂` is obtained from `t₁` by
    substituting (possibly different) subtrees into zero or more leaves of `t₁`. -/
inductive TreePrefix : BTree α → BTree α → Prop
  | ofLeaf (a : α) (t : BTree α) : TreePrefix (BTree.leaf a) t
  | ofNode {l l' r r' : BTree α} :
      TreePrefix l l' → TreePrefix r r' → TreePrefix (BTree.node l r) (BTree.node l' r')

infix:50 " ⊑_tree " => TreePrefix

theorem treePrefix_refl (t : BTree α) : t ⊑_tree t := by
  induction t with
  | leaf a => exact TreePrefix.ofLeaf a _
  | node l r ih_l ih_r => exact TreePrefix.ofNode ih_l ih_r

theorem treePrefix_trans {t₁ t₂ t₃ : BTree α} (h1 : t₁ ⊑_tree t₂) (h2 : t₂ ⊑_tree t₃) :
    t₁ ⊑_tree t₃ := by
  induction h1 generalizing t₃ with
  | ofLeaf a t => exact TreePrefix.ofLeaf a t₃
  | ofNode _ _ ih_l ih_r =>
    cases h2 with
    | ofNode hl hr => exact TreePrefix.ofNode (ih_l hl) (ih_r hr)

/-- On unlabelled trees (tree shapes) the prefix order is antisymmetric, hence a partial order. -/
theorem treePrefix_antisymm {t₁ t₂ : BTree Unit} (h1 : t₁ ⊑_tree t₂) (h2 : t₂ ⊑_tree t₁) :
    t₁ = t₂ := by
  induction h1 with
  | ofLeaf a t =>
    cases h2 with
    | ofLeaf b _ => rfl
  | ofNode _ _ ih_l ih_r =>
    cases h2 with
    | ofNode hl hr => rw [ih_l hl, ih_r hr]

/-- Work (node count) is monotone along the tree prefix order. -/
theorem treePrefix_size_le {t₁ t₂ : BTree α} (h : t₁ ⊑_tree t₂) : t₁.size ≤ t₂.size := by
  induction h with
  | ofLeaf a t => exact size_pos t
  | ofNode _ _ ih_l ih_r =>
    dsimp [size]
    omega

/-- Depth is monotone along the tree prefix order. -/
theorem treePrefix_depth_le {t₁ t₂ : BTree α} (h : t₁ ⊑_tree t₂) : t₁.depth ≤ t₂.depth := by
  induction h with
  | ofLeaf a t => exact Nat.zero_le _
  | ofNode _ _ ih_l ih_r =>
    dsimp [depth]
    omega

/-- Grafting extends a tree in the prefix order. -/
theorem treePrefix_graft (t₁ t₂ : BTree α) : t₁ ⊑_tree (t₁ ⊗ t₂) := by
  induction t₁ with
  | leaf a => exact TreePrefix.ofLeaf a _
  | node l r ih_l ih_r => exact TreePrefix.ofNode ih_l ih_r

/-- The uniform grafting order is contained in the prefix order. -/
theorem graftOrder_treePrefix {t₁ t₂ : BTree α} (h : t₁ ⊑_graft t₂) : t₁ ⊑_tree t₂ := by
  rcases h with ⟨t', rfl⟩
  exact treePrefix_graft t₁ t'

/-- Every tree of depth at most `d` is a prefix of the full tree of depth `d`. -/
theorem treePrefix_fullTree (a : α) (t : BTree α) :
    ∀ d : ℕ, t.depth ≤ d → t ⊑_tree fullTree a d := by
  induction t with
  | leaf b => intro d _; exact TreePrefix.ofLeaf b _
  | node l r ih_l ih_r =>
    intro d h
    dsimp [depth] at h
    cases d with
    | zero => omega
    | succ d => exact TreePrefix.ofNode (ih_l d (by omega)) (ih_r d (by omega))

/-- Leftmost leaf label (witnesses that the label type of a tree is inhabited). -/
def leftLabel : BTree α → α
  | leaf a => a
  | node l _ => l.leftLabel

/-- Depth envelope: a computation tree of depth at most `d` performs at most
    `2^(d+1) - 1` work, the work of the full binary tree of depth `d`. -/
theorem size_le_of_depth_le {t : BTree α} {d : ℕ} (h : t.depth ≤ d) :
    t.size ≤ 2 ^ (d + 1) - 1 := by
  have := treePrefix_size_le (treePrefix_fullTree t.leftLabel t d h)
  rwa [fullTree_work_closed_form] at this

theorem size_le_of_depth (t : BTree α) : t.size ≤ 2 ^ (t.depth + 1) - 1 :=
  size_le_of_depth_le (Nat.le_refl _)

/- =========================================================================
   Uniform tree power (paper: `def:tree-exponentiation`)
   ========================================================================= -/

/-- Uniform tree power `B^{⊗ d}`:
    `B^{⊗ 0}` is a single leaf and `B^{⊗ (d+1)} = B ⊗ B^{⊗ d}`. -/
def treePow (b : BTree Unit) : ℕ → BTree Unit
  | 0     => BTree.leaf ()
  | d + 1 => b ⊗ (treePow b d)

/-- Leaf frontier growth: `leaves(B^{⊗ d}) = leaves(B)^d`. -/
theorem treePow_leafCount (b : BTree Unit) (d : ℕ) :
    (treePow b d).leafCount = b.leafCount ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    show (b ⊗ treePow b d).leafCount = b.leafCount ^ (d + 1)
    rw [graft_leafCount, ih, pow_succ, Nat.mul_comm]

/-- Cumulative work recurrence of the tree power (instance of `graft_size`). -/
theorem treePow_size_succ (b : BTree Unit) (d : ℕ) :
    (treePow b (d + 1)).size =
      (b.size - b.leafCount) + b.leafCount * (treePow b d).size :=
  graft_size b (treePow b d)

/-- Closed form for the cumulative work of the tree power of a binary-shaped
    branching step with `L = leaves(B)` leaves: `|B^{⊗ d}| = 2 · L^d - 1`. -/
theorem treePow_size (b : BTree Unit) (d : ℕ) :
    (treePow b d).size = 2 * b.leafCount ^ d - 1 := by
  have h := size_add_one (treePow b d)
  rw [treePow_leafCount] at h
  omega

/-- The elementary binary branching step (one node with two leaves). -/
def cherry : BTree Unit := BTree.node (BTree.leaf ()) (BTree.leaf ())

/-- The `d`-th power of the binary branching step is the full binary tree of depth `d`. -/
theorem treePow_cherry (d : ℕ) : treePow cherry d = fullTree () d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    show cherry ⊗ treePow cherry d = fullTree () (d + 1)
    rw [ih]
    rfl

theorem treePow_cherry_size (d : ℕ) : (treePow cherry d).size = 2 ^ (d + 1) - 1 := by
  rw [treePow_cherry]
  exact fullTree_work_closed_form () d

/-- Powers can be unfolded on either side: `B^{⊗ (d+1)} = B^{⊗ d} ⊗ B`. -/
theorem treePow_succ' (b : BTree Unit) (d : ℕ) :
    treePow b (d + 1) = treePow b d ⊗ b := by
  induction d with
  | zero =>
    show b ⊗ BTree.leaf () = BTree.leaf () ⊗ b
    rw [graft_unit_leaf]
    rfl
  | succ d ih =>
    show b ⊗ treePow b (d + 1) = (b ⊗ treePow b d) ⊗ b
    rw [graft_assoc, ← ih]

/-- Successive tree powers form an ascending chain in the tree prefix order. -/
theorem treePow_chain (b : BTree Unit) (d : ℕ) : treePow b d ⊑_tree treePow b (d + 1) := by
  rw [treePow_succ']
  exact treePrefix_graft _ _

end BTree

end ImperativeOptimization
