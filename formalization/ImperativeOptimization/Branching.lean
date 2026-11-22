/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import ImperativeOptimization.Arity

namespace ImperativeOptimization

/-!
# Computation trees of any branching factor

`Tree` and `Recursion` state the order-theoretic results of Paper I (Section "Computation
trees" and the branching recursion of Section "Loops and Recursion as Optimization
Problems") for binary trees. This module states them for a fixed branching factor `b`, as
the paper does (Definition `def:tree-algebra`):

* `KTree b`: a leaf, or a node with `b` children indexed by `Fin b`; `size` (nodes,
  leaves included), `leaves`, `depth`; `graft t₁ t₂` substitutes `t₂` for every leaf of
  `t₁`.
* `KTree.Le` (`⊑`): the least relation with `leaf ⊑ t` and `node f ⊑ node g` when
  `f i ⊑ g i` for every `i` (`def:tree-order`): reflexive, transitive, antisymmetric
  (`prop:tree-order-properties`); `size` and `depth` monotone (1); `t ⊑ t ⊗ t'` (2);
  `depth t ≤ d → t ⊑ full d` and `size (full d) = 1 + b + … + b^d` (3).
* `pow B d` (`B^{⊗ d}`, `def:tree-exponentiation`): `leaves = L^d`, the closed form
  `(L - 1) · size + I = (I + L - 1) · L^d` of the cumulative work (and its rational form
  `size = I (L^d - 1)/(L - 1) + L^d` for `L ≥ 2`), the elementary branching step gives the
  full tree, and the powers form a chain (`prop:tree-power-complexity`).
* `KRecurrence b S R`: the recursion `rtree(x) = if cond x then combine (rtree (fwd i x))_i
  else stop x`; the execution tree is the least feasible tree, unique, of least size and
  depth, and the call returns `v` iff `v` is the catamorphism over it
  (`prop:tree-optimization`).
-/

/-- Computation trees with branching factor `b`. -/
inductive KTree (b : ℕ) : Type where
  | leaf : KTree b
  | node : (Fin b → KTree b) → KTree b

namespace KTree

variable {b : ℕ}

/-- Number of nodes, leaves included (the cost of a computation tree). -/
def size : KTree b → ℕ
  | leaf => 1
  | node f => 1 + ∑ i, size (f i)

/-- Number of leaves. -/
def leaves : KTree b → ℕ
  | leaf => 1
  | node f => ∑ i, leaves (f i)

/-- Height, with `depth leaf = 0`. -/
def depth : KTree b → ℕ
  | leaf => 0
  | node f => 1 + Finset.univ.sup fun i => depth (f i)

/-- Grafting: `t₂` substituted for every leaf of `t₁`. -/
def graft (t₁ t₂ : KTree b) : KTree b :=
  match t₁ with
  | leaf => t₂
  | node f => node fun i => graft (f i) t₂

/-- The full `b`-ary tree of depth `d`. -/
def full (b : ℕ) : ℕ → KTree b
  | 0 => leaf
  | d + 1 => node fun _ => full b d

/-- Uniform tree power: `B^{⊗ 0} = leaf`, `B^{⊗ (d+1)} = B ⊗ B^{⊗ d}`. -/
def pow (B : KTree b) : ℕ → KTree b
  | 0 => leaf
  | d + 1 => graft B (pow B d)

theorem size_pos (t : KTree b) : 1 ≤ t.size := by
  cases t <;> simp [size]

theorem leaves_le_size (t : KTree b) : t.leaves ≤ t.size := by
  induction t with
  | leaf => simp [leaves, size]
  | node f ih =>
    simp only [leaves, size]
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => ih i
    omega

/-! ### The order -/

/-- **Tree order-by-composition**: `t₂` is obtained from `t₁` by a leaf substitution. -/
inductive Le : KTree b → KTree b → Prop where
  | leaf (t : KTree b) : Le leaf t
  | node {f g : Fin b → KTree b} : (∀ i, Le (f i) (g i)) → Le (node f) (node g)

theorem le_refl (t : KTree b) : Le t t := by
  induction t with
  | leaf => exact Le.leaf _
  | node f ih => exact Le.node ih

theorem le_trans {t₁ t₂ t₃ : KTree b} (h₁ : Le t₁ t₂) (h₂ : Le t₂ t₃) : Le t₁ t₃ := by
  induction h₁ generalizing t₃ with
  | leaf => exact Le.leaf _
  | node _ ih =>
    cases h₂ with
    | node h => exact Le.node fun i => ih i (h i)

theorem le_antisymm {t₁ t₂ : KTree b} (h₁ : Le t₁ t₂) (h₂ : Le t₂ t₁) : t₁ = t₂ := by
  induction h₁ with
  | leaf t => cases h₂; rfl
  | node _ ih =>
    cases h₂ with
    | node h => exact congrArg node (funext fun i => ih i (h i))

/-- `leaf` is the least element. -/
theorem leaf_le (t : KTree b) : Le leaf t := Le.leaf t

/-- (1) Cost is monotone. -/
theorem size_mono {t₁ t₂ : KTree b} (h : Le t₁ t₂) : t₁.size ≤ t₂.size := by
  induction h with
  | leaf t => exact size_pos t
  | node _ ih =>
    simp only [size]
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => ih i
    omega

/-- (1) Depth is monotone. -/
theorem depth_mono {t₁ t₂ : KTree b} (h : Le t₁ t₂) : t₁.depth ≤ t₂.depth := by
  induction h with
  | leaf t => exact Nat.zero_le _
  | node _ ih =>
    simp only [depth]
    have := Finset.sup_mono_fun fun i (_ : i ∈ Finset.univ) => ih i
    omega

/-- (2) A tree is below every grafting onto it. -/
theorem le_graft (t t' : KTree b) : Le t (graft t t') := by
  induction t with
  | leaf => exact Le.leaf _
  | node f ih => exact Le.node ih

/-- Grafting is monotone in the grafted tree. -/
theorem graft_mono_right (t : KTree b) {t₂ t₂' : KTree b} (h : Le t₂ t₂') :
    Le (graft t t₂) (graft t t₂') := by
  induction t with
  | leaf => exact h
  | node f ih => exact Le.node ih

theorem graft_leaf (t : KTree b) : graft leaf t = t := rfl

/-- Leaves multiply under grafting. -/
theorem graft_leaves (t₁ t₂ : KTree b) : (graft t₁ t₂).leaves = t₁.leaves * t₂.leaves := by
  induction t₁ with
  | leaf => simp [graft, leaves]
  | node f ih => simp only [graft, leaves, ih, Finset.sum_mul]

/-- **Grafting size identity**, `cost(T₁ ⊗ T₂) = (cost T₁ - leaves T₁) + leaves T₁ · cost T₂`,
    stated without subtraction. -/
theorem graft_size (t₁ t₂ : KTree b) :
    (graft t₁ t₂).size + t₁.leaves = t₁.size + t₁.leaves * t₂.size := by
  induction t₁ with
  | leaf => simp [graft, leaves, size]; ring
  | node f ih =>
    simp only [graft, size, leaves, Finset.sum_mul]
    have := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => ih i
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
    omega

/-! ### Full trees -/

theorem size_full (d : ℕ) : (full b d).size = geom b d := by
  induction d with
  | zero => simp [full, size, geom]
  | succ d ih => simp [full, size, geom, ih]

theorem depth_full (d : ℕ) (hb : 0 < b) : (full b d).depth = d := by
  induction d with
  | zero => simp [full, depth]
  | succ d ih =>
    simp only [full, depth, ih]
    have : (Finset.univ.sup fun _ : Fin b => d) = d :=
      Finset.sup_const ⟨⟨0, hb⟩, Finset.mem_univ _⟩ d
    rw [this]; omega

/-- (3) A tree of depth at most `d` is below the full tree of depth `d`. -/
theorem le_full {t : KTree b} {d : ℕ} (h : t.depth ≤ d) : Le t (full b d) := by
  induction t generalizing d with
  | leaf => exact Le.leaf _
  | node f ih =>
    simp only [depth] at h
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hs : (Finset.univ.sup fun i => (f i).depth) ≤ d' := by omega
    exact Le.node fun i => ih i ((Finset.sup_le_iff.mp hs) i (Finset.mem_univ i))

/-- (3) Hence `cost T ≤ 1 + b + … + b^d` ... -/
theorem size_le_of_depth {t : KTree b} {d : ℕ} (h : t.depth ≤ d) : t.size ≤ geom b d :=
  size_full (b := b) d ▸ size_mono (le_full h)

/-- ... `= (b^(d+1) - 1)/(b - 1)`: `(b - 1) · cost T + 1 ≤ b^(d+1)` for `b ≥ 1`. -/
theorem size_le_closed {t : KTree b} {d : ℕ} (hb : 1 ≤ b) (h : t.depth ≤ d) :
    (b - 1) * t.size + 1 ≤ b ^ (d + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have h1 := size_le_of_depth h
  have h2 := geom_closed c d
  simp only [Nat.add_sub_cancel]
  calc c * t.size + 1 ≤ c * geom (c + 1) d + 1 := by gcongr
    _ = (c + 1) ^ (d + 1) := h2

/-! ### Tree powers -/

/-- (1) Leaf frontier growth: `leaves (B^{⊗ d}) = L^d`. -/
theorem pow_leaves (B : KTree b) (d : ℕ) : (pow B d).leaves = B.leaves ^ d := by
  induction d with
  | zero => simp [pow, leaves]
  | succ d ih => simp only [pow, graft_leaves, ih]; ring

/-- The recurrence `cost (B^{⊗ (d+1)}) = I + L · cost (B^{⊗ d})`, `I = cost B - L`. -/
theorem pow_size_succ (B : KTree b) (d : ℕ) :
    (pow B (d + 1)).size = (B.size - B.leaves) + B.leaves * (pow B d).size := by
  have h := graft_size B (pow B d)
  have := leaves_le_size B
  simp only [pow]
  omega

/-- (2) **Cumulative work**, `cost (B^{⊗ d}) = I (L^d - 1)/(L - 1) + L^d`, stated without
    division: with `L = c + 1` leaves and `I` internal nodes,
    `c · cost (B^{⊗ d}) + I = (I + c) · L^d`. -/
theorem pow_size_closed (B : KTree b) (c : ℕ) (hL : B.leaves = c + 1) (d : ℕ) :
    c * (pow B d).size + (B.size - B.leaves) = (B.size - B.leaves + c) * (c + 1) ^ d := by
  induction d with
  | zero => simp [pow, size]; ring
  | succ d ih =>
    rw [pow_size_succ, hL]
    rw [hL] at ih
    rw [pow_succ]
    have e : c * (B.size - (c + 1) + (c + 1) * (pow B d).size) + (B.size - (c + 1))
        = (c + 1) * (c * (pow B d).size + (B.size - (c + 1))) := by ring
    rw [e, ih]; ring

/-- (2) The same over the rationals, for `L ≥ 2`. -/
theorem pow_size_rat (B : KTree b) (hL : 2 ≤ B.leaves) (d : ℕ) :
    ((pow B d).size : ℚ) =
      ((B.size : ℚ) - B.leaves) * ((B.leaves : ℚ) ^ d - 1) / ((B.leaves : ℚ) - 1)
        + (B.leaves : ℚ) ^ d := by
  obtain ⟨c, hc⟩ : ∃ c, B.leaves = c + 1 := ⟨B.leaves - 1, by omega⟩
  have h := pow_size_closed B c hc d
  have hle := leaves_le_size B
  have hc1 : (1 : ℚ) ≤ c := by exact_mod_cast (show 1 ≤ c by omega)
  have hq : (c : ℚ) * (pow B d).size + ((B.size : ℚ) - B.leaves)
      = ((B.size : ℚ) - B.leaves + c) * ((c : ℚ) + 1) ^ d := by
    have := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast [Nat.cast_sub hle] at this
    exact this
  rw [hc] at hq ⊢
  push_cast at hq ⊢
  have hne : (c : ℚ) + 1 - 1 ≠ 0 := by linarith
  field_simp
  linear_combination hq

/-- The elementary branching step `g(ε, …, ε)`. -/
def step (b : ℕ) : KTree b := node fun _ => leaf

/-- Its powers are the full trees. -/
theorem pow_step (d : ℕ) : pow (step b) d = full b d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show pow (step b) (d + 1) = graft (step b) (pow (step b) d) from rfl, ih]
    rfl

/-- (3) **Prefix chain**: `B^{⊗ d} ⊑ B^{⊗ (d+1)}`. -/
theorem pow_chain (B : KTree b) (d : ℕ) : Le (pow B d) (pow B (d + 1)) := by
  induction d with
  | zero => exact Le.leaf _
  | succ d ih => exact graft_mono_right B ih

end KTree

/-! ### Branching recursion as tree optimisation -/

/-- `rtree(x) = if cond x then combine (rtree (fwd 0 x), …, rtree (fwd (b-1) x)) else stop x`. -/
structure KRecurrence (b : ℕ) (S R : Type) where
  cond : S → Bool
  fwd : Fin b → S → S
  combine : (Fin b → R) → R
  stop : S → R

namespace KRecurrence

variable {b : ℕ} {S R : Type} (kr : KRecurrence b S R)

/-- `t` is the execution tree of the call on `s`: internal nodes exactly where `cond`
    holds, leaves where it fails. -/
def IsExec : KTree b → S → Prop
  | KTree.leaf, s => kr.cond s = false
  | KTree.node f, s => kr.cond s = true ∧ ∀ i, IsExec (f i) (kr.fwd i s)

/-- Feasibility: every leaf, at the state reached along its path, falsifies `cond`. -/
def Feasible : KTree b → S → Prop
  | KTree.leaf, s => kr.cond s = false
  | KTree.node f, s => ∀ i, Feasible (f i) (kr.fwd i s)

/-- The bottom-up catamorphism: `stop` at leaves, `combine` at nodes. -/
def eval : KTree b → S → R
  | KTree.leaf, s => kr.stop s
  | KTree.node f, s => kr.combine fun i => eval (f i) (kr.fwd i s)

theorem exec_feasible {t : KTree b} {s : S} (h : kr.IsExec t s) : kr.Feasible t s := by
  induction t generalizing s with
  | leaf => exact h
  | node f ih => exact fun i => ih i (h.2 i)

/-- **The execution tree is the least feasible tree.** -/
theorem exec_least {t t' : KTree b} {s : S} (h : kr.IsExec t s) (h' : kr.Feasible t' s) :
    KTree.Le t t' := by
  induction t generalizing s t' with
  | leaf => exact KTree.Le.leaf _
  | node f ih =>
    obtain ⟨hc, hf⟩ := h
    cases t' with
    | leaf =>
      have : kr.cond s = false := h'
      rw [hc] at this; cases this
    | node g => exact KTree.Le.node fun i => ih i (hf i) (h' i)

/-- It is unique. -/
theorem exec_unique {t t' : KTree b} {s : S} (h : kr.IsExec t s) (h' : kr.IsExec t' s) :
    t = t' :=
  KTree.le_antisymm (kr.exec_least h (kr.exec_feasible h'))
    (kr.exec_least h' (kr.exec_feasible h))

/-- It has the least cost among feasible trees ... -/
theorem exec_size_min {t t' : KTree b} {s : S} (h : kr.IsExec t s) (h' : kr.Feasible t' s) :
    t.size ≤ t'.size :=
  KTree.size_mono (kr.exec_least h h')

/-- ... and the least depth. -/
theorem exec_depth_min {t t' : KTree b} {s : S} (h : kr.IsExec t s)
    (h' : kr.Feasible t' s) : t.depth ≤ t'.depth :=
  KTree.depth_mono (kr.exec_least h h')

/-- Big-step semantics of the call. -/
inductive BigStep : S → R → Prop where
  | base {s : S} : kr.cond s = false → BigStep s (kr.stop s)
  | branch {s : S} {v : Fin b → R} : kr.cond s = true →
      (∀ i, BigStep (kr.fwd i s) (v i)) → BigStep s (kr.combine v)

/-- **The call returns `v` iff `v` is the catamorphism over the execution tree**; in
    particular the execution tree exists iff the call terminates. -/
theorem bigStep_iff (s : S) (v : R) :
    kr.BigStep s v ↔ ∃ t, kr.IsExec t s ∧ v = kr.eval t s := by
  constructor
  · intro h
    induction h with
    | base hc => exact ⟨KTree.leaf, hc, rfl⟩
    | branch hc _ ih =>
      choose t ht hv using ih
      refine ⟨KTree.node t, ⟨hc, ht⟩, ?_⟩
      simp only [eval]
      exact congrArg kr.combine (funext hv)
  · rintro ⟨t, ht, rfl⟩
    induction t generalizing s with
    | leaf => exact BigStep.base ht
    | node f ih => exact BigStep.branch ht.1 fun i => ih i _ (ht.2 i)

end KRecurrence

/-! ### Example: a ternary recursion (the hypotheses are satisfiable) -/

/-- `f(n) = if n > 0 then f(n-1) + f(n-1) + f(n-1) else 1` on natural numbers. -/
def tern : KRecurrence 3 ℕ ℕ where
  cond n := decide (0 < n)
  fwd _ n := n - 1
  combine v := v 0 + v 1 + v 2
  stop _ := 1

/-- Its execution tree from `n` is the full ternary tree of depth `n`, of cost
    `1 + 3 + … + 3^n`. -/
theorem tern_exec (n : ℕ) : tern.IsExec (KTree.full 3 n) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine ⟨by simp [tern], fun _ => ?_⟩
    simpa [tern] using ih

theorem tern_cost (n : ℕ) : (KTree.full 3 n).size = geom 3 n := KTree.size_full n

end ImperativeOptimization
