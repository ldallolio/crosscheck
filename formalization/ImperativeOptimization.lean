import ImperativeOptimization.State
import ImperativeOptimization.Trace
import ImperativeOptimization.Tree
import ImperativeOptimization.FixedPoint
import ImperativeOptimization.OperationalSemantics
import ImperativeOptimization.Examples

/-!
# Imperative Programming as an Optimization Problem

This repository provides a machine-checked formalization in Lean 4 of the paper
*Imperative Programming as an Optimization Problem*.

## Overview of Modules
- `State`: Pointed state spaces and partial state transition operators.
- `Trace`: Free trace monoids, intensional order-by-composition, and minimal trace existence.
- `Tree`: Computation tree algebras, operadic tree grafting, and branching cost envelopes.
- `FixedPoint`: Trace space completion, Scott continuity, and Kleene fixed points.
- `OperationalSemantics`: Translation of imperative loops and recursions to recurrence systems.
- `Examples`: Machine-checked proofs of concrete examples (parametric loop, infinite loop, linear recursion, non-linear recursion).
-/