/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import ImperativeOptimization.CheckerCore

/-!
# Mini-C and the validation of certificates against it: definitions

A small fragment of C as an abstract syntax (`MStmt`): integer variables, assignments,
statements that only cost, conditionals, `while` and `for` loops with tests that are
conjunctions of comparisons. Its meaning is given by `lower`, a translation into the
programs of the certificate checker (`ACmd` without annotations), whose cost semantics is
that of `Language` (via `ACmd.toCmd`): **this definition is the semantics of mini-C**.

The costs of atomic statements and tests are data of the syntax (the cost model of the
analysis); the structure of the program, which variables are written, and the affine values
of assignments and tests are computed here from the syntax.

`validate c s` holds when the program of the certificate `c` is, after removing its
annotations and flattening its sequences (`nf`), the lowering of `s`. The theorem
`MiniC.validated_cost_le` (in `ImperativeOptimization.MiniC`) then bounds the cost of `s`
by the bound of the accepted certificate: the generator of certificates is not trusted.

No mathlib: compiled into the checker program.
-/

namespace ImperativeOptimization.MiniC
open Checker

/-- Integer expressions over the tracked variables. `other` is any other value (a memory
    read, a call result, a value the fragment does not model): unknown. -/
inductive MExp where
  | var (x : Nat)
  | lit (k : Int)
  | add (a b : MExp)
  | sub (a b : MExp)
  | mul (a b : MExp)
  | neg (a : MExp)
  | other
  deriving Repr, DecidableEq

inductive Cmp where
  | lt | le | gt | ge
  deriving Repr, DecidableEq

/-- Tests: comparisons, negations; `other` is a test the fragment does not model. -/
inductive MCond where
  | cmp (op : Cmp) (a b : MExp)
  | not (c : MCond)
  | other
  deriving Repr, DecidableEq

/-- The operations whose result is described by facts, not by an affine value: quotient
    and remainder by a positive constant, mask by a non-negative constant. (A right shift
    by `k` is written as the quotient by `2^k`.) -/
inductive DivOp where
  | div | rem | and
  deriving Repr, DecidableEq

/-- Statements. `assign w x e` writes the tracked variable `x` (an unknown value if `e` is
    not affine); `cost w` is a statement that writes no tracked variable; the tests of
    `ite`, `while` and `for` cost `w`. A loop test is a conjunction.
    `divStore w x op y c old` is `x = y op c` for a constant `c`: `x` receives a value of
    which only facts are known (see `divOf`). When `y` mentions `x` (`x = x / c`), `old`
    names a scratch variable, not a variable of the source, that first receives `y`. -/
inductive MStmt where
  | skip
  | assign (w x : Nat) (e : MExp)
  | divStore (w x : Nat) (op : DivOp) (y : MExp) (c : Int) (old : Option Nat)
  /-- A store into an unsigned variable whose largest value is `hi`: `x` receives the
      value of `e` if it lies in `[0, hi]`, and an unknown value otherwise (C reduces it
      modulo `hi + 1`; mini-C does not say to what). -/
  | assignU (w x : Nat) (hi : Int) (e : MExp)
  /-- A call of the function number `f` of the program: each argument `(x, hi, e)` is
      first stored (at no cost: the cost of evaluating the call is that of the statement
      around it) into the variable `x` of the callee's parameter, as an unsigned store when
      `hi` is given; then the callee runs. Parameters that are not tracked integers are not
      listed. The callee is the program of function `f` in the certificate file. -/
  | call (f : Nat) (args : List (Nat × Option Int × MExp))
  | cost (w : Nat)
  | seq (a b : MStmt)
  | ite (w : Nat) (c : MCond) (a b : MStmt)
  | while (w : Nat) (cs : List MCond) (body : MStmt)
  | for_ (init : MStmt) (w : Nat) (cs : List MCond) (inc body : MStmt)
  deriving Repr

def padd (p q : PExp) : PExp := ⟨vadd p.sv q.sv, p.c + q.c⟩
def pscale (k : Int) (p : PExp) : PExp := ⟨vsmul k p.sv, k * p.c⟩

/-- The affine value of an expression, if it is affine. -/
def MExp.affine : MExp → Option PExp
  | .var x => some ⟨unit x, 0⟩
  | .lit k => some ⟨[], k⟩
  | .add a b => do let p ← a.affine; let q ← b.affine; pure (padd p q)
  | .sub a b => do let p ← a.affine; let q ← b.affine; pure (padd p (pscale (-1) q))
  | .neg a => do let p ← a.affine; pure (pscale (-1) p)
  | .mul a b => do
      let p ← a.affine
      let q ← b.affine
      if isZero p.sv then pure (pscale p.c q)
      else if isZero q.sv then pure (pscale q.c p)
      else none
  | .other => none

/-- A test as `g ≤ 0`, if it is a comparison of affine values. -/
def MCond.test : MCond → Option PExp
  | .cmp op a b => do
      let p ← a.affine
      let q ← b.affine
      match op with
      | .lt => pure (padd (padd p (pscale (-1) q)) ⟨[], 1⟩)
      | .le => pure (padd p (pscale (-1) q))
      | .gt => pure (padd (padd q (pscale (-1) p)) ⟨[], 1⟩)
      | .ge => pure (padd q (pscale (-1) p))
  | .not c => do let g ← c.test; pure (padd (pscale (-1) g) ⟨[], 1⟩)
  | .other => none

/-- Variable `0` is the choice of an unmodelled test, variable `1` the variable that
    statements which only cost write (no assertion mentions it). -/
def choiceVar : Nat := 0
def costVar : Nat := 1

/-- The empty annotations of a lowered program (the checker never sees these). -/
def noSB : SB := SB.const 0

/-- A loop of the checker without annotations (one test: `while`, otherwise `whileAnd`). -/
def loopOf (w : Nat) (gs : List PExp) (body : ACmd) : ACmd :=
  match gs with
  | [g] => .while w g [] ⟨[], 0⟩ 1 0 [] 0 (1, []) noSB body
  | _ => .whileAnd w gs [] ⟨[], 0⟩ 1 0 [] 0 (1, []) noSB body

/-- `a ; b` without annotations. -/
def seqOf (a b : ACmd) : ACmd := .seq a [] noSB noSB b

/-- `k·a - b + cst`. -/
def linComb (a : PExp) (k : Int) (b : PExp) (cst : Int) : PExp :=
  ⟨vadd (vsmul k a.sv) (vsmul (-1) b.sv), k * a.c - b.c + cst⟩

/-- What is known of `x = y op c`: the facts that hold when `y ≥ 0`, and those that hold
    for every `y`. For `y ≥ 0`: `c·x ≤ y ≤ c·x + c - 1` (quotient), `0 ≤ x ≤ c - 1` and
    `x ≤ y` (remainder), `0 ≤ x ≤ c` and `x ≤ y` (mask). For a negative `y` nothing is
    said of a quotient or a remainder (C rounds towards zero, and a shift of a negative
    value is implementation-defined); a mask by `c ≥ 0` always lies in `[0, c]`. -/
def divFacts (op : DivOp) (x : Nat) (y : PExp) (c : Int) : List PExp × List PExp :=
  let xv : PExp := ⟨unit x, 0⟩
  match op with
  | .div => ([linComb xv c y 0, linComb y 1 ⟨vsmul c xv.sv, 0⟩ (-(c - 1))], [])
  | .rem => ([⟨vsmul (-1) xv.sv, 0⟩, ⟨xv.sv, -(c - 1)⟩, linComb xv 1 y 0], [])
  | .and => ([⟨vsmul (-1) xv.sv, 0⟩, ⟨xv.sv, -c⟩, linComb xv 1 y 0],
             [⟨vsmul (-1) xv.sv, 0⟩, ⟨xv.sv, -c⟩])

/-- `x := ?` such that the constraints `cs` hold (no constraint: any value). -/
def storeOf (w x : Nat) (cs : List PExp) : ACmd :=
  match cs with
  | [] => .havoc w x
  | _ => .havocC w x cs

/-- `x = y op c` for an affine `y` that does not mention `x`: a test of `y ≥ 0` (of weight
    0: it is not code of the source) selecting the facts. -/
def divOf (w x : Nat) (op : DivOp) (y : PExp) (c : Int) : ACmd :=
  let f := divFacts op x y c
  .ite 0 ⟨vsmul (-1) y.sv, -y.c⟩ noSB noSB (storeOf w x f.1) (storeOf w x f.2)

/-- The store of one argument of a call into the callee's parameter variable. -/
def storeArg : Nat × Option Int × MExp → ACmd
  | (x, none, e) => match e.affine with
      | some a => .assign 0 x a
      | none => .havoc 0 x
  | (x, some hi, e) => match e.affine with
      | some a =>
          .ite 0 ⟨a.sv, a.c - hi⟩ noSB noSB
            (.ite 0 (pscale (-1) a) noSB noSB (.assign 0 x a) (.havoc 0 x))
            (.havoc 0 x)
      | none => .havoc 0 x

/-- **The semantics of mini-C**, as a program of the checker. `none`: not in the fragment
    (a loop test that is not a conjunction of comparisons). A `for` loop is its
    initialisation followed by a `while` loop whose body is the body and the increment. -/
def lower : MStmt → Option ACmd
  | .skip => some .skip
  | .assign w x e => some (match e.affine with
      | some a => .assign w x a
      | none => .havoc w x)
  | .assignU w x hi e => some (match e.affine with
      | some a =>
          .ite 0 ⟨a.sv, a.c - hi⟩ noSB noSB
            (.ite 0 (pscale (-1) a) noSB noSB (.assign w x a) (.havoc w x))
            (.havoc w x)
      | none => .havoc w x)
  | .call f args =>
      some (args.foldr (fun a acc => seqOf (storeArg a) acc)
        (.call 0 f (args.map (fun a => ⟨unit a.1, 0⟩)) [] [] []))
  | .divStore w x op y c old =>
      if (op = .and ∧ c < 0) ∨ (op ≠ .and ∧ c < 1) then none
      else match y.affine with
        | none => some (.havoc w x)
        | some a => match old with
          | none => if coeff a.sv x = 0 then some (divOf w x op a c) else none
          | some t =>
              if t = x ∨ t = choiceVar ∨ t = costVar then none
              else some (seqOf (.assign 0 t a) (divOf w x op ⟨unit t, 0⟩ c))
  | .cost w => some (.havoc w costVar)
  | .seq a b => do
      let la ← lower a
      let lb ← lower b
      pure (seqOf la lb)
  | .ite w c a b => do
      let la ← lower a
      let lb ← lower b
      match c.test with
      | some g => pure (.ite w g noSB noSB la lb)
      | none => pure (seqOf (.havoc 0 choiceVar) (.ite w ⟨unit choiceVar, 0⟩ noSB noSB la lb))
  | .while w cs body => do
      let gs ← cs.mapM MCond.test
      let lb ← lower body
      pure (loopOf w gs lb)
  | .for_ init w cs inc body => do
      let li ← lower init
      let gs ← cs.mapM MCond.test
      let lb ← lower body
      let lc ← lower inc
      pure (seqOf li (loopOf w gs (seqOf lb lc)))

/-! ### Normal form: the program of a certificate without its annotations -/

/-- Trailing zero coefficients are dropped. -/
def trim : List Int → List Int
  | [] => []
  | a :: l => match trim l with
    | [] => if a = 0 then [] else [a]
    | r => a :: r

def canon (p : PExp) : PExp := ⟨trim p.sv, p.c⟩

/-- `a ; b` for programs in normal form (right-nested, without `skip`). -/
def app : ACmd → ACmd → ACmd
  | .skip, b => b
  | .seq x _ _ _ rest, b => .seq x [] noSB noSB (app rest b)
  | a, .skip => a
  | a, b => .seq a [] noSB noSB b

/-- The normal form: annotations replaced by fixed values, `weaken` and `dead` removed
    (they do not change the program), sequences flattened, `skip` removed, affine
    expressions without trailing zeros. -/
def nf : ACmd → ACmd
  | .skip => .skip
  | .assign w x a => .assign w x (canon a)
  | .havoc w x => .havoc w x
  | .havocC w x cs => .havocC w x (cs.map canon)
  | .seq a _ _ _ b => app (nf a) (nf b)
  | .ite w g _ _ a b => .ite w (canon g) noSB noSB (nf a) (nf b)
  | .while w g _ _ _ _ _ _ _ _ b => .while w (canon g) [] ⟨[], 0⟩ 1 0 [] 0 (1, []) noSB (nf b)
  | .whileAnd w gs _ _ _ _ _ _ _ _ b =>
      .whileAnd w (gs.map canon) [] ⟨[], 0⟩ 1 0 [] 0 (1, []) noSB (nf b)
  | .whileLog w gs _ _ _ _ _ _ _ b =>
      match gs with
      | [g] => .while w (canon g) [] ⟨[], 0⟩ 1 0 [] 0 (1, []) noSB (nf b)
      | _ => .whileAnd w (gs.map canon) [] ⟨[], 0⟩ 1 0 [] 0 (1, []) noSB (nf b)
  | .whileGrow w gs _ _ _ _ _ _ _ b =>
      match gs with
      | [g] => .while w (canon g) [] ⟨[], 0⟩ 1 0 [] 0 (1, []) noSB (nf b)
      | _ => .whileAnd w (gs.map canon) [] ⟨[], 0⟩ 1 0 [] 0 (1, []) noSB (nf b)
  | .whileUp w gs _ _ _ _ _ _ _ b =>
      match gs with
      | [g] => .while w (canon g) [] ⟨[], 0⟩ 1 0 [] 0 (1, []) noSB (nf b)
      | _ => .whileAnd w (gs.map canon) [] ⟨[], 0⟩ 1 0 [] 0 (1, []) noSB (nf b)
  | .weaken _ _ _ _ _ c => nf c
  | .dead _ c => nf c
  | .call w f inst _ _ _ => .call w f (inst.map canon) [] [] []

/-- The program of the certificate `c` is the lowering of the mini-C statement `s`. -/
def validate (c : ACmd) (s : MStmt) : Bool :=
  match lower s with
  | some d => decide (nf c = nf d)
  | none => false

end ImperativeOptimization.MiniC
