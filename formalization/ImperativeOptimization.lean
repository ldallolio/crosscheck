/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import ImperativeOptimization.State
import ImperativeOptimization.Trace
import ImperativeOptimization.Tree
import ImperativeOptimization.Dominance
import ImperativeOptimization.Norms
import ImperativeOptimization.WhileLoop
import ImperativeOptimization.Ranking
import ImperativeOptimization.Recursion
import ImperativeOptimization.Certificate
import ImperativeOptimization.Arity
import ImperativeOptimization.Language
import ImperativeOptimization.Branching
import ImperativeOptimization.Divergence
import ImperativeOptimization.CheckerCore
import ImperativeOptimization.Checker
import ImperativeOptimization.MiniCCore
import ImperativeOptimization.MiniC
import ImperativeOptimization.MiniCJumpCore
import ImperativeOptimization.MiniCJump
import ImperativeOptimization.ResponseCore
import ImperativeOptimization.Interrupts
import ImperativeOptimization.ForkJoin
import ImperativeOptimization.FixedPoint
import ImperativeOptimization.OperationalSemantics
import ImperativeOptimization.Examples
import ImperativeOptimization.Stack
import ImperativeOptimization.Cycles
import ImperativeOptimization.Thumb
import ImperativeOptimization.ThumbDataCore
import ImperativeOptimization.ThumbData
import ImperativeOptimization.ThumbConv

/-!
# CrossCheck: Dual-Layer Semantics of Imperative Programs and WCET Verification

Machine-checked formalization in Lean 4 accompanying the CrossCheck paper
(Paper I, `paper/theory/crosscheck-theory.tex`). Table "Correspondence between the paper and the Lean 4
development" of the paper, mirrored by `formalization.yaml`, maps paper statements
(by LaTeX label) to the theorems below.

Some material is kept here although the paper no longer uses it (it was removed from
the paper in the November 2026 simplification): the subsequence order `⊑_sub` in
`Trace`, the uniform grafting order `⊑_graft` in `Tree`, and the big-O preorder `≼_O`
in `Dominance`.

## Overview of Modules
- `State`: Pointed state spaces and partial state transition operators.
- `Trace`: Free trace monoids, prefix order `⊑` (order-by-composition), (weighted) cost,
  nested and sequential loop traces, minimal exiting trace existence; also the
  subsequence order `⊑_sub` (not used by the paper).
- `Tree`: Binary computation trees, grafting `⊗`, tree order-by-composition `⊑_tree`,
  depth envelopes, tree powers, and catamorphisms.
- `Dominance`: Branch rule (cost of a conditional ≤ guard + max of the branches);
  also the big-O preorder `≼_O` (not used by the paper).
- `FixedPoint`: Trace valuation homomorphism (`⟦t₁·t₂⟧ = ⟦t₂⟧ ∘ ⟦t₁⟧`, `⟦t^n⟧ = ⟦t⟧^n`).
- `OperationalSemantics`: Recurrence systems (`LoopConstraint`, `LinearRecurrence`) and
  the minimal iteration predicate `MinimalIter`.
- `WhileLoop`: Big-step semantics of while loops and its equivalence with trace
  minimisation; worst-case step bound for state-dependent body traces.
- `Ranking`: Ranking potentials (Lyapunov bounds), termination, and WCET envelopes.
- `Recursion`: Big-step semantics of linear and binary branching recursion and their
  equivalence with trace / tree minimisation; depth envelopes.
- `Certificate`: Soundness of the certificates used by the Clang plugin: relational ranking
  bound with field-valued potentials, Farkas certificates, loop cost formula.
- `Arity`: Call trees of arbitrary arity; depth envelope and size potentials.
- `Branching`: Computation trees of any fixed branching factor `b`: the tree order, grafting,
  tree powers and the execution tree of a `b`-ary recursion as the least feasible tree.
- `Divergence`: Infinite executions of the small language (coinductive); a valid cost bound
  excludes them when loop tests and calls have positive weights.
- `Language`: A small imperative language with a cost semantics (terminating executions and
  execution prefixes), a cost logic (`Derivable`) and its soundness; symbolic bounds and
  the call rule for function summaries.
- `Cycles` (with `CyclesCore`): cycle certificates of binary control-flow graphs (IPET dual:
  potentials and row multipliers) and their soundness for programs with calls.
- `Thumb` (with `ThumbCore`): the same on Cortex-M0 machine code: ARMv6-M decoder and cycle
  table, graphs built from the code, every run of the machine code bounded (`binary_sound`).
- `Examples`: Machine-checked versions of the paper's worked examples.
-/
