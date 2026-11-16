/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic

namespace ImperativeOptimization

/-!
# Stack depth: a high-water mark

Execution cost adds up along an execution; the stack does not. The stack used by one
activation of a function is the largest of: the depth its own code reaches, and, for each
call it makes, the depth at the call site plus the stack used by the callee. Over the tree
of activations this is a maximum over paths, where cost is a sum over nodes.

* `ActTree` / `ActForest`: an activation (labelled by its function) with its calls, each
  made at some stack depth of the caller.
* `ActTree.highWater`: the stack it uses.
* `highWater_le_of_bound`: **soundness of the composition rule**. If `B` satisfies
  `own f ≤ B f` and `d + B g ≤ B f` for every call site of `f` (depth `d`, callee `g`),
  then every activation tree that only uses these call sites needs at most `B (root)`.
  This is the rule that `benchmarks/cycles/stack.py` applies to a binary (there `B f` is
  the least such value, and the binary must have no recursion).
* `highWater_le_depth`: with frames of at most `F` bytes, an activation tree of depth `d`
  needs at most `(d + 1) * F`: a recursion depth bound gives a stack bound.

What is not formalized: that the activations of a machine program form such a tree with
the depths computed on its control-flow graph (the model of the processor).
-/

mutual
/-- An activation of the function `f`, with the calls it makes. -/
inductive ActTree (ι : Type) : Type
  | node : ι → ActForest ι → ActTree ι
/-- The calls of an activation: the stack depth of the caller at the call, and the callee. -/
inductive ActForest (ι : Type) : Type
  | nil : ActForest ι
  | cons : ℕ → ActTree ι → ActForest ι → ActForest ι
end

variable {ι : Type}

/-- The function of an activation. -/
def ActTree.root : ActTree ι → ι
  | .node f _ => f

mutual
/-- The stack used by an activation: its own largest depth `own f`, or a call depth plus
    the callee's stack. -/
def ActTree.highWater (own : ι → ℕ) : ActTree ι → ℕ
  | .node f cs => max (own f) (cs.highWater own)
/-- The largest `depth at the call + stack of the callee` among the calls. -/
def ActForest.highWater (own : ι → ℕ) : ActForest ι → ℕ
  | .nil => 0
  | .cons d t cs => max (d + t.highWater own) (cs.highWater own)
end

mutual
/-- Every call of the tree is a call site of the program: `site f d g` says that `f` may
    call `g` at stack depth `d`. -/
def ActTree.Uses (site : ι → ℕ → ι → Prop) : ActTree ι → Prop
  | .node f cs => cs.Uses site f
/-- The calls of an activation of `f` are call sites of `f`, and so on below. -/
def ActForest.Uses (site : ι → ℕ → ι → Prop) : ActForest ι → ι → Prop
  | .nil, _ => True
  | .cons d t cs, f => site f d t.root ∧ t.Uses site ∧ cs.Uses site f
end

mutual
/-- **Soundness of the stack rule.** A function `B` that dominates each function's own
    depth and, at each call site, the depth plus the callee's `B`, bounds the stack of
    every activation tree made of these call sites. -/
theorem highWater_le_of_bound (own : ι → ℕ) (site : ι → ℕ → ι → Prop) (B : ι → ℕ)
    (h_own : ∀ f, own f ≤ B f) (h_site : ∀ f d g, site f d g → d + B g ≤ B f) :
    ∀ t : ActTree ι, t.Uses site → t.highWater own ≤ B t.root
  | .node f cs, h => by
    have := forest_highWater_le_of_bound own site B h_own h_site cs f h
    simp only [ActTree.highWater, ActTree.root]
    exact max_le (h_own f) this
/-- The calls of an activation of `f` stay below `B f`. -/
theorem forest_highWater_le_of_bound (own : ι → ℕ) (site : ι → ℕ → ι → Prop) (B : ι → ℕ)
    (h_own : ∀ f, own f ≤ B f) (h_site : ∀ f d g, site f d g → d + B g ≤ B f) :
    ∀ (cs : ActForest ι) (f : ι), cs.Uses site f → cs.highWater own ≤ B f
  | .nil, _, _ => by simp [ActForest.highWater]
  | .cons d t cs, f, h => by
    obtain ⟨hs, ht, hcs⟩ := h
    have h1 := highWater_le_of_bound own site B h_own h_site t ht
    have h2 := forest_highWater_le_of_bound own site B h_own h_site cs f hcs
    have h3 := h_site f d t.root hs
    simp only [ActForest.highWater]
    exact max_le (by omega) h2
end

mutual
/-- Height of an activation tree (a single activation has depth `0`). -/
def ActTree.depth : ActTree ι → ℕ
  | .node _ cs => cs.depth
/-- `1 +` the largest depth among the callees, `0` without calls. -/
def ActForest.depth : ActForest ι → ℕ
  | .nil => 0
  | .cons _ t cs => max (t.depth + 1) cs.depth
end

mutual
/-- Calls are made at a depth of at most `F`. -/
def ActTree.CallsBelow (F : ℕ) : ActTree ι → Prop
  | .node _ cs => cs.CallsBelow F
/-- Every call of the forest, and below, is made at a depth of at most `F`. -/
def ActForest.CallsBelow (F : ℕ) : ActForest ι → Prop
  | .nil => True
  | .cons d t cs => d ≤ F ∧ t.CallsBelow F ∧ cs.CallsBelow F
end

mutual
/-- **Stack from a depth bound.** If no function uses more than `F` bytes itself and no
    call is made deeper than `F`, an activation tree of depth `n` uses at most
    `(n + 1) * F`: the recursion depth bounds of the analysis give stack bounds. -/
theorem highWater_le_depth (own : ι → ℕ) (F : ℕ) (h_own : ∀ f, own f ≤ F) :
    ∀ t : ActTree ι, t.CallsBelow F → t.highWater own ≤ (t.depth + 1) * F
  | .node f cs, h => by
    have h1 := forest_highWater_le_depth own F h_own cs h
    have h2 : F ≤ (cs.depth + 1) * F := Nat.le_mul_of_pos_left F (Nat.succ_pos _)
    simp only [ActTree.highWater, ActTree.depth]
    exact max_le (le_trans (h_own f) h2) h1
/-- The calls of an activation use at most `(depth + 1) * F`, where the depth of the
    forest counts the callees' levels. -/
theorem forest_highWater_le_depth (own : ι → ℕ) (F : ℕ) (h_own : ∀ f, own f ≤ F) :
    ∀ cs : ActForest ι, cs.CallsBelow F → cs.highWater own ≤ (cs.depth + 1) * F
  | .nil, _ => by simp [ActForest.highWater]
  | .cons d t cs, h => by
    obtain ⟨hd, ht, hcs⟩ := h
    have h1 := highWater_le_depth own F h_own t ht
    have h2 := forest_highWater_le_depth own F h_own cs hcs
    simp only [ActForest.highWater, ActForest.depth]
    have hb : (t.depth + 1) * F + F = (t.depth + 1 + 1) * F := by ring
    have hc : (t.depth + 1 + 1) * F ≤ (max (t.depth + 1) cs.depth + 1) * F :=
      Nat.mul_le_mul_right F (by omega)
    have hd' : (cs.depth + 1) * F ≤ (max (t.depth + 1) cs.depth + 1) * F :=
      Nat.mul_le_mul_right F (by omega)
    exact max_le (by omega) (le_trans h2 hd')
end

/-- The rule is not vacuous: `main` (8 bytes of its own) calls `g` (16 bytes) at depth 8;
    the activation uses 24 bytes, which is the least `B main`. -/
example :
    (ActTree.node true (.cons 8 (.node false .nil) .nil)).highWater
      (fun f => if f then 8 else 16) = 24 := by
  decide

end ImperativeOptimization
