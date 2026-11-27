/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic

namespace ImperativeOptimization

/-!
# Call trees of arbitrary arity

`Tree.lean` and `Recursion.lean` treat binary computation trees. Here a node may
have any finite number of children, which is what a general recursive function
produces: the node labelled `x` is one activation with argument `x`, and its
children are the activations it starts.

Two bounds on the number of activations are proved, matching the two certificates
used by the analyser for recursion:

* `callTree_size_le_geom`: if every activation makes at most `b` self-calls and a
  natural-valued potential strictly decreases at each call, the call tree has at
  most `1 + b + … + b^(V x)` nodes (`geom_closed`: `(b^(d+1) - 1) / (b - 1)`).
* `callTree_size_le_potential`: if `U x ≥ 1 + Σ U y` over the self-calls `y` of
  `x`, the call tree of `x` has at most `U x` nodes (a *size potential*; this is
  the amortised argument that gives linear bounds for divide-and-conquer).
-/

mutual
/-- A labelled tree whose nodes have finitely many children. -/
inductive RTree (α : Type) : Type
  | node : α → Forest α → RTree α
/-- A list of trees. -/
inductive Forest (α : Type) : Type
  | nil : Forest α
  | cons : RTree α → Forest α → Forest α
end

variable {α : Type}

/-- Label of the root. -/
def RTree.root : RTree α → α
  | .node a _ => a

mutual
/-- Number of nodes. -/
def RTree.size : RTree α → ℕ
  | .node _ f => 1 + f.size
/-- Total number of nodes of a forest. -/
def Forest.size : Forest α → ℕ
  | .nil => 0
  | .cons t f => t.size + f.size
end

mutual
/-- Height (a single node has depth `0`). -/
def RTree.depth : RTree α → ℕ
  | .node _ f => f.depth
/-- `1 +` the largest depth of a tree of the forest, `0` for the empty forest. -/
def Forest.depth : Forest α → ℕ
  | .nil => 0
  | .cons t f => max (t.depth + 1) f.depth
end

/-- Number of trees in a forest. -/
def Forest.length : Forest α → ℕ
  | .nil => 0
  | .cons _ f => 1 + f.length

mutual
/-- Every node has at most `b` children. -/
def RTree.BranchLE (b : ℕ) : RTree α → Prop
  | .node _ f => f.length ≤ b ∧ f.BranchLE b
/-- Every tree of the forest satisfies `BranchLE b`. -/
def Forest.BranchLE (b : ℕ) : Forest α → Prop
  | .nil => True
  | .cons t f => t.BranchLE b ∧ f.BranchLE b
end

/-- `geom b d = 1 + b + … + b^d`. -/
def geom (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + b * geom b d

theorem geom_pos (b d : ℕ) : 1 ≤ geom b d := by
  cases d <;> simp [geom]

/-- Closed form: `(b - 1) * (1 + b + … + b^d) + 1 = b^(d+1)`, stated with `b = c + 1`. -/
theorem geom_closed (c d : ℕ) : c * geom (c + 1) d + 1 = (c + 1) ^ (d + 1) := by
  induction d with
  | zero => simp [geom]
  | succ d ih =>
    have h : c * geom (c + 1) (d + 1) + 1 = (c + 1) * (c * geom (c + 1) d + 1) := by
      simp only [geom]
      ring
    rw [h, ih]
    ring

/-- For `b = 1` the bound is `d + 1`: linear recursion. -/
theorem geom_one (d : ℕ) : geom 1 d = d + 1 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [geom, ih]; omega

theorem Forest.length_eq_zero_of_depth {f : Forest α} (h : f.depth = 0) : f.length = 0 := by
  cases f with
  | nil => rfl
  | cons t f => simp [Forest.depth] at h

mutual
/-- **Depth envelope for arbitrary arity.** A tree with branching at most `b` and
    depth at most `d` has at most `1 + b + … + b^d` nodes. -/
theorem RTree.size_le_geom (b : ℕ) :
    ∀ (t : RTree α) (d : ℕ), t.BranchLE b → t.depth ≤ d → t.size ≤ geom b d
  | .node _ f, d, hb, hd => by
    obtain ⟨hlen, hf⟩ := hb
    have hfs := Forest.size_le_geom b f d hf hd
    cases d with
    | zero =>
      have h0 : f.length = 0 := Forest.length_eq_zero_of_depth (Nat.le_zero.mp hd)
      simp only [RTree.size, geom]
      rw [h0] at hfs
      omega
    | succ d =>
      have h1 : f.length * geom b d ≤ b * geom b d := Nat.mul_le_mul_right _ hlen
      simp only [RTree.size, geom]
      simp only [Nat.add_sub_cancel] at hfs
      omega
/-- A forest of depth at most `d` consists of trees of depth at most `d - 1`. -/
theorem Forest.size_le_geom (b : ℕ) :
    ∀ (f : Forest α) (d : ℕ), f.BranchLE b → f.depth ≤ d → f.size ≤ f.length * geom b (d - 1)
  | .nil, _, _, _ => by simp [Forest.size]
  | .cons t f, d, hb, hd => by
    obtain ⟨ht, hf⟩ := hb
    simp only [Forest.depth] at hd
    have h1 := RTree.size_le_geom b t (d - 1) ht (by omega)
    have h2 := Forest.size_le_geom b f d hf (by omega)
    have h3 : (1 + f.length) * geom b (d - 1) = geom b (d - 1) + f.length * geom b (d - 1) := by
      ring
    simp only [Forest.size, Forest.length]
    omega
end

/-! ### Call trees of a recursive scheme -/

mutual
/-- `t` is the call tree of the scheme `calls` (which maps an argument to the list of
    arguments of the self-calls it performs): the children of a node labelled `x`
    are the call trees of `calls x`, in order. -/
def RTree.IsCallTree (calls : α → List α) : RTree α → Prop
  | .node a f => f.IsCallForest calls (calls a)
/-- The forest consists of the call trees of the given arguments. -/
def Forest.IsCallForest (calls : α → List α) : Forest α → List α → Prop
  | .nil, [] => True
  | .cons t f, y :: ys => t.root = y ∧ t.IsCallTree calls ∧ f.IsCallForest calls ys
  | .nil, _ :: _ => False
  | .cons _ _, [] => False
end

mutual
/-- **Size potential.** If `1 + Σ_{y ∈ calls x} U y ≤ U x` for every argument, the
    call tree of `x` has at most `U x` nodes. -/
theorem RTree.size_le_potential {β : Type} [Field β] [LinearOrder β] [IsStrictOrderedRing β] (calls : α → List α)
    (U : α → β) (hU : ∀ x, 1 + ((calls x).map U).sum ≤ U x) :
    ∀ t : RTree α, t.IsCallTree calls → (t.size : β) ≤ U t.root
  | .node a f, h => by
    have hf := Forest.size_le_potential calls U hU f (calls a) h
    have ha := hU a
    simp only [RTree.size, RTree.root]
    push_cast
    linarith
theorem Forest.size_le_potential {β : Type} [Field β] [LinearOrder β] [IsStrictOrderedRing β] (calls : α → List α)
    (U : α → β) (hU : ∀ x, 1 + ((calls x).map U).sum ≤ U x) :
    ∀ (f : Forest α) (ys : List α), f.IsCallForest calls ys → (f.size : β) ≤ (ys.map U).sum
  | .nil, [], _ => by simp [Forest.size]
  | .cons t f, y :: ys, h => by
    obtain ⟨hy, ht, hf⟩ := h
    have h1 := RTree.size_le_potential calls U hU t ht
    have h2 := Forest.size_le_potential calls U hU f ys hf
    rw [hy] at h1
    simp only [Forest.size, List.map_cons, List.sum_cons]
    push_cast
    linarith
  | .nil, _ :: _, h => by exact absurd h (by simp [Forest.IsCallForest])
  | .cons _ _, [], h => by exact absurd h (by simp [Forest.IsCallForest])
end

/-- The number reported by the analyser: `⌊U x⌋`. -/
theorem callTree_size_le_potential {β : Type} [Field β] [LinearOrder β] [IsStrictOrderedRing β] [FloorSemiring β]
    (calls : α → List α) (U : α → β) (hU : ∀ x, 1 + ((calls x).map U).sum ≤ U x)
    (t : RTree α) (ht : t.IsCallTree calls) : t.size ≤ ⌊U t.root⌋₊ :=
  Nat.le_floor (RTree.size_le_potential calls U hU t ht)

mutual
/-- A call tree of a scheme with at most `b` self-calls per activation has
    branching at most `b`, and a strictly decreasing potential bounds its depth. -/
theorem RTree.callTree_shape (calls : α → List α) (b : ℕ) (hb : ∀ x, (calls x).length ≤ b)
    (V : α → ℕ) (hV : ∀ x, ∀ y ∈ calls x, V y < V x) :
    ∀ t : RTree α, t.IsCallTree calls → t.BranchLE b ∧ t.depth ≤ V t.root
  | .node a f, h => by
    have hf := Forest.callTree_shape calls b hb V hV f (calls a) (V a) h
      (fun y hy => hV a y hy)
    exact ⟨⟨hf.2.1 ▸ hb a, hf.1⟩, hf.2.2⟩
theorem Forest.callTree_shape (calls : α → List α) (b : ℕ) (hb : ∀ x, (calls x).length ≤ b)
    (V : α → ℕ) (hV : ∀ x, ∀ y ∈ calls x, V y < V x) :
    ∀ (f : Forest α) (ys : List α) (m : ℕ), f.IsCallForest calls ys → (∀ y ∈ ys, V y < m) →
      f.BranchLE b ∧ f.length = ys.length ∧ f.depth ≤ m
  | .nil, [], _, _, _ => by simp [Forest.BranchLE, Forest.length, Forest.depth]
  | .cons t f, y :: ys, m, h, hm => by
    obtain ⟨hy, ht, hf⟩ := h
    have h1 := RTree.callTree_shape calls b hb V hV t ht
    have h2 := Forest.callTree_shape calls b hb V hV f ys m hf
      (fun z hz => hm z (List.mem_cons_of_mem _ hz))
    have h3 : V y < m := hm y (List.mem_cons_self)
    rw [hy] at h1
    refine ⟨⟨h1.1, h2.1⟩, ?_, ?_⟩
    · simp only [Forest.length, List.length_cons, h2.2.1]; omega
    · simp only [Forest.depth]; omega
  | .nil, _ :: _, _, h, _ => by exact absurd h (by simp [Forest.IsCallForest])
  | .cons _ _, [], _, h, _ => by exact absurd h (by simp [Forest.IsCallForest])
end

/-- **Depth envelope for a recursive scheme of arbitrary arity.** -/
theorem callTree_size_le_geom (calls : α → List α) (b : ℕ) (hb : ∀ x, (calls x).length ≤ b)
    (V : α → ℕ) (hV : ∀ x, ∀ y ∈ calls x, V y < V x)
    (t : RTree α) (ht : t.IsCallTree calls) : t.size ≤ geom b (V t.root) := by
  have h := RTree.callTree_shape calls b hb V hV t ht
  exact RTree.size_le_geom b t _ h.1 h.2

end ImperativeOptimization
