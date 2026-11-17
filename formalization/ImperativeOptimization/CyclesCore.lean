/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/

/-!
# Cycle bounds of binary control-flow graphs: the executable check (no mathlib)

A function of a binary is given as a control-flow graph with a single entry node and a
single exit node: every edge carries a weight (the cycles of the instructions executed when
the edge is taken, by a timing table that is trusted) and the functions called along it.
Loop bounds are linear constraints on the number of times each edge is taken (`Row`:
`Σₑ aₑ·xₑ ≤ b`, e.g. `x_back − N·x_entry ≤ 0`).

The bound of the implicit path enumeration technique (IPET: the largest `Σₑ wₑ·xₑ` over the
edge counts allowed by flow conservation and the rows) is certified by a feasible solution
of the dual linear program, scaled to integers: a potential `π` per node and a multiplier
`λₖ ≥ 0` per row such that, for every edge `e = (u, v)`,

  `D·(wₑ + Σ_{g called on e} B_g) + π v − π u ≤ Σₖ λₖ·aₖₑ`

and `π entry − π exit + Σₖ λₖ·bₖ ≤ D·B`. `Cycles.cycles_sound` (in `Cycles`) proves that
every run of the function whose edge counts satisfy the rows then costs at most `B`, given
the bounds `B_g` of the callees, and `Cycles.program_sound` that the claims of a whole
program hold together (by induction on the depth of calls).
-/

namespace ImperativeOptimization.Cycles

/-- An edge of a control-flow graph: its weight (cycles) and the functions called on it. -/
structure Edge where
  src : Nat
  dst : Nat
  w : Nat
  calls : List Nat
  deriving Repr, DecidableEq

/-- A linear constraint on edge counts, sparse: `Σ (e, a) ∈ coef, a·x_e ≤ rhs`. -/
structure Row where
  coef : List (Nat × Int)
  rhs : Int
  deriving Repr, DecidableEq

/-- The control-flow graph of a function: nodes are numbers, edges are indexed by their
    position in `edges`. -/
structure Graph where
  entry : Nat
  exit : Nat
  edges : List Edge
  rows : List Row
  deriving Repr, DecidableEq

/-- A certificate: scale `D > 0`, potentials (default 0), multipliers, claimed bound. -/
structure Cert where
  scale : Nat
  pot : List Int
  mult : List Nat
  bound : Nat
  deriving Repr, DecidableEq

/-- The coefficient of edge `e` in a sparse row (repetitions add up). -/
def coefOf : List (Nat × Int) → Nat → Int
  | [], _ => 0
  | (i, a) :: t, e => (if i = e then a else 0) + coefOf t e

/-- `Σₖ λₖ·f(rowₖ)` over the rows that have a multiplier. -/
def dot : List Nat → List Row → (Row → Int) → Int
  | m :: ms, r :: rs, f => (m : Int) * f r + dot ms rs f
  | _, _, _ => 0

/-- The sum of the claimed bounds of the called functions (0 outside the program). -/
def callBound (bounds : List Nat) : List Nat → Nat
  | [] => 0
  | g :: gs => bounds.getD g 0 + callBound bounds gs

/-- The potential of a node (0 if not given). -/
def potOf (C : Cert) (v : Nat) : Int := C.pot.getD v 0

/-- The dual constraint of edge number `i`. -/
def edgeOk (bounds : List Nat) (G : Graph) (C : Cert) (i : Nat) (e : Edge) : Bool :=
  decide ((C.scale : Int) * ((e.w + callBound bounds e.calls : Nat) : Int) + potOf C e.dst - potOf C e.src
    ≤ dot C.mult G.rows (fun r => coefOf r.coef i))

/-- `p i eᵢ` for every edge, numbered from `i`. -/
def allEdges (p : Nat → Edge → Bool) : Nat → List Edge → Bool
  | _, [] => true
  | i, e :: es => p i e && allEdges p (i + 1) es

/-- The check of one function, given the claimed bounds of all functions. -/
def checkFn (bounds : List Nat) (G : Graph) (C : Cert) : Bool :=
  decide (0 < C.scale) && allEdges (edgeOk bounds G C) 0 G.edges &&
    decide (potOf C G.entry - potOf C G.exit + dot C.mult G.rows (·.rhs) ≤ (C.scale : Int) * C.bound)

/-- The check of a program: one certificate per function, each accepted with the claimed
    bounds of all (calls in any order, recursion included: the soundness argument is by
    induction on the depth of calls of a finite run). -/
def checkProgram (P : List Graph) (Cs : List Cert) : Bool :=
  P.length == Cs.length && (P.zip Cs).all fun (G, C) => checkFn (Cs.map Cert.bound) G C

end ImperativeOptimization.Cycles
