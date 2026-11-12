/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Logic.Function.Iterate
import ImperativeOptimization.OperationalSemantics

namespace ImperativeOptimization

/-!
# Recursion: big-step semantics versus trace / tree minimisation

* Linear recursion `rlin(x) = if cond x then back(x, rlin(fwd x)) else stop x`:
  `framedBigStep_iff` shows that the call returns `r` iff `r` is obtained by
  unwinding from the minimal recursion depth; `linRec_iff` specialises this to
  frame-independent `back` and the closed form `back^n (stop (fwd^n s))`.
* Binary branching recursion
  `rtree(x) = if cond x then combine(rtree(fwdL x), rtree(fwdR x)) else stop x`:
  the execution tree is the least tree (for `⊑_tree`) all of whose leaves exit
  (`exec_least`), the returned value is its catamorphism (`treeBigStep_iff`), and
  a depth ranking potential bounds its work (`exec_size_le`).
-/

variable {S R : Type}

/- =========================================================================
   Linear recursion
   ========================================================================= -/

/-- Linear recursion whose unwinding step may read the caller's frame `s`. -/
structure FramedRecurrence (S R : Type) where
  cond : S → Bool
  fwd : S → S
  back : S → R → R
  stop : S → R

/-- Result of a linear recursion of depth exactly `n` started at `s`:
    `back s₀ (back s₁ (… (stop sₙ)))` with `s_k = fwd^k s`. -/
def unwind (fr : FramedRecurrence S R) : ℕ → S → R
  | 0, s => fr.stop s
  | n + 1, s => fr.back s (unwind fr n (fr.fwd s))

/-- Big-step (natural) semantics of the linear recursive function. -/
inductive FramedBigStep (fr : FramedRecurrence S R) : S → R → Prop
  | base {s : S} : fr.cond s = false → FramedBigStep fr s (fr.stop s)
  | call {s : S} {r : R} : fr.cond s = true → FramedBigStep fr (fr.fwd s) r →
      FramedBigStep fr s (fr.back s r)

/-- **Linear recursion as minimisation.** The call on `s` returns `r` iff `r` is the
    unwinding from the minimal recursion depth `n̄`. -/
theorem framedBigStep_iff (fr : FramedRecurrence S R) (s : S) (r : R) :
    FramedBigStep fr s r ↔ ∃ n, MinimalIter fr.cond fr.fwd s n ∧ r = unwind fr n s := by
  constructor
  · intro h
    induction h with
    | base hc => exact ⟨0, ⟨hc, fun k hk => absurd hk (Nat.not_lt_zero k)⟩, rfl⟩
    | call hc _ ih =>
      rcases ih with ⟨n, ⟨h1, h2⟩, rfl⟩
      refine ⟨n + 1, ⟨?_, ?_⟩, rfl⟩
      · rw [Function.iterate_succ_apply]
        exact h1
      · intro k hk
        cases k with
        | zero => exact hc
        | succ k =>
          rw [Function.iterate_succ_apply]
          exact h2 k (by omega)
  · rintro ⟨n, hn, rfl⟩
    induction n generalizing s with
    | zero => exact FramedBigStep.base hn.1
    | succ n ih =>
      rcases hn with ⟨h1, h2⟩
      have hc : fr.cond s = true := h2 0 (Nat.succ_pos n)
      refine FramedBigStep.call hc (ih (fr.fwd s) ⟨?_, ?_⟩)
      · rw [Function.iterate_succ_apply] at h1
        exact h1
      · intro k hk
        have h := h2 (k + 1) (by omega)
        rw [Function.iterate_succ_apply] at h
        exact h

/-- A frame-independent linear recurrence seen as a framed one. -/
def LinearRecurrence.toFramed (lr : LinearRecurrence S) : FramedRecurrence S S :=
  { cond := lr.cond, fwd := lr.fwd, back := fun _ r => lr.back r, stop := lr.stop }

/-- For frame-independent `back`, unwinding is the closed form
    `back^n (stop (fwd^n s))` computed by `solveLinearRecurrence`. -/
theorem unwind_toFramed (lr : LinearRecurrence S) (n : ℕ) (s : S) :
    unwind lr.toFramed n s = solveLinearRecurrence lr s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    show lr.back (unwind lr.toFramed n (lr.fwd s)) = _
    rw [ih]
    dsimp only [solveLinearRecurrence]
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply]

/-- **Linear recursion as dual-layer trace optimisation.** -/
theorem linRec_iff (lr : LinearRecurrence S) (s r : S) :
    FramedBigStep lr.toFramed s r ↔
      ∃ n, MinimalIter lr.cond lr.fwd s n ∧ r = solveLinearRecurrence lr s n := by
  rw [framedBigStep_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, unwind_toFramed lr n s⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (unwind_toFramed lr n s).symm⟩

/-- Intensional cost of a linear recursion of depth `n`:
    `cost (t_fwd^n · t_stop · t_back^n) = n · (‖t_fwd‖ + ‖t_back‖) + ‖t_stop‖`. -/
theorem linear_recursion_cost {Instr : Type} (t_fwd t_stop t_back : Trace Instr) (n : ℕ) :
    cost ((t_fwd ^[n]) ++ t_stop ++ (t_back ^[n])) =
      n * (cost t_fwd + cost t_back) + cost t_stop := by
  rw [cost_additive, cost_additive, cost_iter, cost_iter]
  ring

/- =========================================================================
   Binary branching recursion
   ========================================================================= -/

/-- Binary branching recursion scheme. -/
structure TreeRecurrence (S R : Type) where
  cond : S → Bool
  fwdL : S → S
  fwdR : S → S
  combine : R → R → R
  stop : S → R

/-- `t` is the execution (call) tree of the recursion started at `s`: internal nodes
    are exactly the calls where `cond` holds, leaves the calls where it fails. -/
def IsExecTree (tr : TreeRecurrence S R) : BTree Unit → S → Prop
  | BTree.leaf _, s => tr.cond s = false
  | BTree.node l r, s =>
      tr.cond s = true ∧ IsExecTree tr l (tr.fwdL s) ∧ IsExecTree tr r (tr.fwdR s)

/-- Feasibility constraint of the tree optimisation problem: every leaf of `t`
    (positioned at the state reached along its path) falsifies `cond`. -/
def LeavesExit (tr : TreeRecurrence S R) : BTree Unit → S → Prop
  | BTree.leaf _, s => tr.cond s = false
  | BTree.node l r, s => LeavesExit tr l (tr.fwdL s) ∧ LeavesExit tr r (tr.fwdR s)

/-- Bottom-up catamorphism computing the value synthesised over a call tree. -/
def evalTree (tr : TreeRecurrence S R) : BTree Unit → S → R
  | BTree.leaf _, s => tr.stop s
  | BTree.node l r, s => tr.combine (evalTree tr l (tr.fwdL s)) (evalTree tr r (tr.fwdR s))

/-- The execution tree is feasible. -/
theorem exec_leavesExit (tr : TreeRecurrence S R) (t : BTree Unit) :
    ∀ s, IsExecTree tr t s → LeavesExit tr t s := by
  induction t with
  | leaf _ => intro s h; exact h
  | node l r ih_l ih_r =>
    intro s h
    obtain ⟨_, hl, hr⟩ := h
    exact ⟨ih_l _ hl, ih_r _ hr⟩

/-- **Non-linear recursion as tree optimisation.** The execution tree is the least
    feasible tree with respect to the tree order-by-composition. -/
theorem exec_least (tr : TreeRecurrence S R) (t : BTree Unit) :
    ∀ (s : S) (t' : BTree Unit), IsExecTree tr t s → LeavesExit tr t' s → t ⊑_tree t' := by
  induction t with
  | leaf a => intro s t' _ _; exact BTree.TreePrefix.ofLeaf a t'
  | node l r ih_l ih_r =>
    intro s t' h h'
    obtain ⟨hc, hl, hr⟩ := h
    cases t' with
    | leaf b =>
      have hf : tr.cond s = false := h'
      rw [hc] at hf
      cases hf
    | node l' r' =>
      obtain ⟨hl', hr'⟩ := h'
      exact BTree.TreePrefix.ofNode (ih_l _ _ hl hl') (ih_r _ _ hr hr')

/-- The execution tree is unique. -/
theorem exec_unique (tr : TreeRecurrence S R) {t t' : BTree Unit} {s : S}
    (h : IsExecTree tr t s) (h' : IsExecTree tr t' s) : t = t' :=
  BTree.treePrefix_antisymm
    (exec_least tr t s t' h (exec_leavesExit tr t' s h'))
    (exec_least tr t' s t h' (exec_leavesExit tr t s h))

/-- Minimal work: the execution tree has the least node count among feasible trees. -/
theorem exec_size_min (tr : TreeRecurrence S R) {t t' : BTree Unit} {s : S}
    (h : IsExecTree tr t s) (h' : LeavesExit tr t' s) : t.size ≤ t'.size :=
  BTree.treePrefix_size_le (exec_least tr t s t' h h')

/-- Big-step (natural) semantics of the branching recursive function. -/
inductive TreeBigStep (tr : TreeRecurrence S R) : S → R → Prop
  | base {s : S} : tr.cond s = false → TreeBigStep tr s (tr.stop s)
  | branch {s : S} {vl vr : R} : tr.cond s = true →
      TreeBigStep tr (tr.fwdL s) vl → TreeBigStep tr (tr.fwdR s) vr →
      TreeBigStep tr s (tr.combine vl vr)

/-- The call returns `v` iff `v` is the catamorphism over the execution tree. -/
theorem treeBigStep_iff (tr : TreeRecurrence S R) (s : S) (v : R) :
    TreeBigStep tr s v ↔ ∃ t, IsExecTree tr t s ∧ v = evalTree tr t s := by
  constructor
  · intro h
    induction h with
    | base hc => exact ⟨BTree.leaf (), hc, rfl⟩
    | branch hc _ _ ih_l ih_r =>
      rcases ih_l with ⟨tl, hl, rfl⟩
      rcases ih_r with ⟨tr', hr, rfl⟩
      exact ⟨BTree.node tl tr', ⟨hc, hl, hr⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    induction t generalizing s with
    | leaf _ => exact TreeBigStep.base ht
    | node l r ih_l ih_r =>
      obtain ⟨hc, hl, hr⟩ := ht
      exact TreeBigStep.branch hc (ih_l _ hl) (ih_r _ hr)

/-- A depth ranking potential bounds the depth of the execution tree. -/
theorem exec_depth_le (tr : TreeRecurrence S R) (V : S → ℕ)
    (hV : ∀ s, tr.cond s = true → V (tr.fwdL s) < V s ∧ V (tr.fwdR s) < V s)
    (t : BTree Unit) : ∀ s, IsExecTree tr t s → t.depth ≤ V s := by
  induction t with
  | leaf _ => intro s _; exact Nat.zero_le _
  | node l r ih_l ih_r =>
    intro s h
    obtain ⟨hc, hl, hr⟩ := h
    have h1 := ih_l _ hl
    have h2 := ih_r _ hr
    obtain ⟨h3, h4⟩ := hV s hc
    dsimp [BTree.depth]
    omega

/-- **Branching recursion envelope.** With a depth ranking potential `V`, the total
    work of the recursion started at `s` is at most `2^(V s + 1) - 1`. -/
theorem exec_size_le (tr : TreeRecurrence S R) (V : S → ℕ)
    (hV : ∀ s, tr.cond s = true → V (tr.fwdL s) < V s ∧ V (tr.fwdR s) < V s)
    {t : BTree Unit} {s : S} (h : IsExecTree tr t s) :
    t.size ≤ 2 ^ (V s + 1) - 1 :=
  BTree.size_le_of_depth_le (exec_depth_le tr V hV t s h)

end ImperativeOptimization
