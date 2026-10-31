import ImperativeOptimization.State
import ImperativeOptimization.Trace
import ImperativeOptimization.Tree
import ImperativeOptimization.Dominance
import ImperativeOptimization.FixedPoint
import ImperativeOptimization.OperationalSemantics
import ImperativeOptimization.Examples

/-!
# Imperative Programming as an Optimization Problem

This repository provides a machine-checked formalization in Lean 4 of the paper
*Imperative Programming as an Optimization Problem*.

## Overview of Modules
- `State`: Pointed state spaces and partial state transition operators.
- `Trace`: Free trace monoids, prefix order, nested loop exponentiation, and minimal trace existence.
- `Tree`: Computation tree algebras, operadic grafting, tree powers, and catamorphisms.
- `Dominance`: Asymptotic dominance preorder (≼_O), branch supremums, and ranking function bounds.
- `FixedPoint`: Trace evaluation homomorphism and solution soundness.
- `OperationalSemantics`: Recurrence system reduction and solver interfaces.
- `Examples`: Machine-checked proofs of paper examples (including exact closed forms and root return values).
-/
