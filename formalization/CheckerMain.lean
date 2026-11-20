/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Lean.Data.Json
import ImperativeOptimization.CheckerCore
import ImperativeOptimization.MiniCCore
import ImperativeOptimization.MiniCJumpCore
import ImperativeOptimization.ResponseCore
import ImperativeOptimization.CyclesCore
import ImperativeOptimization.ThumbCore
import ImperativeOptimization.ThumbDataCore

/-!
# `crosscheck-check`: the certificate checker as a program

Reads cost certificates in JSON (format: `docs/certificate-format.md`), converts each
into the Lean type `Checker.ACmd`, and runs the verified function `Checker.check` on it.
`Checker.check_sound` (in `ImperativeOptimization.Checker`, which proves properties of the
definitions in `CheckerCore`) states what an accepted certificate guarantees.

What is trusted here, besides Lean's compiler and runtime: only this file's conversion
from JSON to `ACmd`. A wrong conversion can make the checker examine a different
certificate than the one in the file, never accept an invalid one; `--print` shows the
certificate as it was understood.

A function may also carry its source program in mini-C (`"source"`, the fragment
`MiniC.MStmt`); the checker then runs the verified `MiniC.validate`, and prints
`VALIDATED` when the certificate's program is the lowering of the source (theorem
`MiniC.validated_sound`: the bound then holds for the source program). The conversion of
the source from JSON is trusted in the same way. A source with early exits or `switch`
(`"jsource"`, the fragment `MiniC.JStmt`, with its return flag) is validated by the
verified `MiniC.validateJ`, which eliminates the jumps itself; the checker also requires
that no function body that the function can call (those before it) reads or writes the
source's ghost variables (`MiniC.quietCmd`), as theorem `MiniC.validatedJ_sound` does (for
contracts this is assumed).

A program may also carry response-time claims (`"responses"`): a function (the task)
preempted by interrupt handlers (functions of the same program) with minimum inter-arrival
times and per-activation overheads, which are assumed. The checker requires the task and
handlers to be accepted with constant bounds and runs the verified `Interrupts.rtaHolds`
(theorem `Interrupts.rtaHolds_sound`).

A file with `"format": "crosscheck-cycles"` holds cycle certificates of binary
control-flow graphs instead (`ImperativeOptimization.Cycles.Graph`, `ImperativeOptimization.Cycles.Cert`; format in
`docs/certificate-format.md`): the checker runs the verified `ImperativeOptimization.Cycles.checkProgram`
(theorem `Cycles.program_sound`: every completed run of each function, whose edge counts
satisfy the function's rows, costs at most its claimed bound). The graphs, weights and rows
are trusted: they are the producer's description of the machine code, its timing and its
loop bounds.

A file with `"format": "crosscheck-binary-cycles"` holds the machine code itself (Cortex-M0,
`Thumb.Code`) with, per function, its entry, the addresses of its instructions, its loop
rows on pairs of addresses and a certificate: the checker builds the graphs from the code
with the verified decoder and runs `Thumb.checkBinary` (theorem `Thumb.binary_sound`: every
run of the machine code, in the semantics of `Thumb`, on which the rows hold, costs at most
the bound). Version 2 of the format may add, per function, loop certificates on the
machine code (`"loops"`, `"kinds"`, `"inv"` with optional further disjuncts `"alt"` and their
targets `"pick"`, `"proofs"`, and `"abi"` for the program): the
checker then also runs `Thumb.checkData` (theorem `ThumbData.data_sound`: the rows of the
certified loops hold on every run of the data semantics, so only the rows left in `"rows"`
are trusted). The rows of the certified loops are generated here by `Thumb.loopRow`, and
the graphs are built with them. `--decode FILE` prints the decoding of the addresses listed in FILE (for
differential tests of the decoder).

Exit status: 0 if every certificate is accepted, 1 if one is rejected, 2 on a malformed
input.
-/

open Lean ImperativeOptimization.Checker ImperativeOptimization.MiniC ImperativeOptimization.Interrupts

namespace CheckerMain

def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{k}'"

def getNat (j : Json) (k : String) : Except String Nat := do
  let v ← field j k
  match v.getInt? with
  | .ok n => if n < 0 then .error s!"field '{k}' must be a natural number" else .ok n.toNat
  | .error _ => .error s!"field '{k}' must be an integer"

def getInt (j : Json) (k : String) : Except String Int := do
  let v ← field j k
  match v.getInt? with
  | .ok n => .ok n
  | .error _ => .error s!"field '{k}' must be an integer"

def intList (j : Json) (what : String) : Except String (List Int) := do
  let arr ← match j.getArr? with
    | .ok a => pure a
    | .error _ => throw s!"{what} must be an array of integers"
  arr.toList.mapM fun x => match x.getInt? with
    | .ok n => pure n
    | .error _ => throw s!"{what} must be an array of integers"

def natList (j : Json) (what : String) : Except String (List Nat) := do
  let l ← intList j what
  l.mapM fun n => if n < 0 then throw s!"{what} must contain natural numbers" else pure n.toNat

def optIntList (j : Json) (k : String) : Except String (List Int) :=
  match j.getObjVal? k with
  | .ok v => intList v k
  | .error _ => .ok []

def parsePExp (j : Json) : Except String PExp := do
  pure ⟨← optIntList j "sv", ← getInt j "c"⟩

def parseLin (j : Json) : Except String Lin := do
  pure ⟨← optIntList j "sv", ← optIntList j "lv", ← getInt j "c"⟩

def parseArr {α : Type} (j : Json) (k : String) (f : Json → Except String α) :
    Except String (List α) := do
  let v ← field j k
  let arr ← match v.getArr? with
    | .ok a => pure a
    | .error _ => throw s!"field '{k}' must be an array"
  arr.toList.mapM f

def parseFarkas (j : Json) : Except String (Nat × List Nat) := do
  pure (← getNat j "mu", ← natList (← field j "lam") "lam")

/-- A bound: a natural number (constant) or `{c, co}` (symbolic). -/
def parseSBv (v : Json) (what : String) : Except String SB := do
  match v.getInt? with
  | .ok n => if n < 0 then throw s!"{what} must be non-negative" else pure (SB.const n.toNat)
  | .error _ =>
    let c ← getNat v "c"
    let co ← match v.getObjVal? "co" with
      | .ok a => natList a "co"
      | .error _ => pure []
    -- quadratic terms `[a, i, j]`: a * max(0, γi) * max(0, γj) (optional)
    let q ← match v.getObjVal? "q" with
      | .ok a => do
          let ts ← match a.getArr? with
            | .ok ts => pure ts
            | .error _ => throw "field 'q' must be an array"
          ts.toList.mapM fun t => do
            match ← natList t "q" with
            | [x, i, k] => pure (x, i, k)
            | _ => throw "each quadratic term must be [a, i, j]"
      | .error _ => pure []
    pure ⟨c, co, q⟩

def getSB (j : Json) (k : String) : Except String SB := do parseSBv (← field j k) k

def optNatList (j : Json) (k : String) : Except String (List Nat) :=
  match j.getObjVal? k with
  | .ok v => natList v k
  | .error _ => .ok []

partial def parseCmd (j : Json) : Except String ACmd := do
  let node ← match (← field j "node").getStr? with
    | .ok s => pure s
    | .error _ => throw "field 'node' must be a string"
  match node with
  | "skip" => pure .skip
  | "assign" => pure (.assign (← getNat j "w") (← getNat j "x") (← parsePExp (← field j "a")))
  | "havoc" => pure (.havoc (← getNat j "w") (← getNat j "x"))
  | "havocC" => pure (.havocC (← getNat j "w") (← getNat j "x") (← parseArr j "cs" parsePExp))
  | "seq" =>
      pure (.seq (← parseCmd (← field j "c1")) (← parseArr j "mid" parseLin)
        (← getSB j "B1") (← getSB j "B2") (← parseCmd (← field j "c2")))
  | "ite" =>
      pure (.ite (← getNat j "w") (← parsePExp (← field j "g")) (← getSB j "B1")
        (← getSB j "B2") (← parseCmd (← field j "c1")) (← parseCmd (← field j "c2")))
  | "while" =>
      pure (.while (← getNat j "w") (← parsePExp (← field j "g")) (← parseArr j "inv" parseLin)
        (← parsePExp (← field j "pot")) (← getNat j "d") (← getInt j "k") (← optNatList j "kl")
        (← getNat j "j") (← parseFarkas (← field j "posCert")) (← getSB j "Wb")
        (← parseCmd (← field j "body")))
  | "whileAnd" =>
      pure (.whileAnd (← getNat j "w") (← parseArr j "gs" parsePExp) (← parseArr j "inv" parseLin)
        (← parsePExp (← field j "pot")) (← getNat j "d") (← getInt j "k") (← optNatList j "kl")
        (← getNat j "j") (← parseFarkas (← field j "posCert")) (← getSB j "Wb")
        (← parseCmd (← field j "body")))
  | "whileLog" =>
      pure (.whileLog (← getNat j "w") (← parseArr j "gs" parsePExp) (← parseArr j "inv" parseLin)
        (← parsePExp (← field j "pot")) (← getNat j "b") (← getInt j "k")
        (← getNat j "j") (← parseFarkas (← field j "posCert")) (← getSB j "Wb")
        (← parseCmd (← field j "body")))
  | "whileGrow" =>
      pure (.whileGrow (← getNat j "w") (← parseArr j "gs" parsePExp) (← parseArr j "inv" parseLin)
        (← parsePExp (← field j "pot")) (← getNat j "b") (← getInt j "K")
        (← getNat j "j") (← parseFarkas (← field j "capCert")) (← getSB j "Wb")
        (← parseCmd (← field j "body")))
  | "whileUp" =>
      pure (.whileUp (← getNat j "w") (← parseArr j "gs" parsePExp) (← parseArr j "inv" parseLin)
        (← parsePExp (← field j "pot")) (← getNat j "d") (← getInt j "k")
        (← getNat j "j") (← parseFarkas (← field j "posCert")) (← getSB j "Wb")
        (← parseCmd (← field j "body")))
  | "weaken" =>
      pure (.weaken (← parseArr j "P" parseLin) (← parseArr j "preCerts" parseFarkas)
        (← getSB j "B") (← parseArr j "Q" parseLin) (← parseArr j "postCerts" parseFarkas)
        (← parseCmd (← field j "c")))
  | "dead" => pure (.dead (← parseFarkas (← field j "cert")) (← parseCmd (← field j "c")))
  | "call" =>
      pure (.call (← getNat j "w") (← getNat j "f") (← parseArr j "inst" parsePExp)
        (← parseArr j "preCerts" parseFarkas) (← parseArr j "ubs" (fun v => parseSBv v "ubs"))
        (← parseArr j "ubCerts" parseFarkas))
  | other => throw s!"unknown node '{other}'"

/-! ### Mini-C sources -/

def strField (j : Json) (k : String) : Except String String := do
  match (← field j k).getStr? with
  | .ok s => pure s
  | .error _ => throw s!"field '{k}' must be a string"

partial def parseMExp (j : Json) : Except String MExp := do
  match ← strField j "e" with
  | "var" => pure (.var (← getNat j "x"))
  | "lit" => pure (.lit (← getInt j "k"))
  | "add" => pure (.add (← parseMExp (← field j "a")) (← parseMExp (← field j "b")))
  | "sub" => pure (.sub (← parseMExp (← field j "a")) (← parseMExp (← field j "b")))
  | "mul" => pure (.mul (← parseMExp (← field j "a")) (← parseMExp (← field j "b")))
  | "neg" => pure (.neg (← parseMExp (← field j "a")))
  | "other" => pure .other
  | o => throw s!"unknown expression '{o}'"

partial def parseMCond (j : Json) : Except String MCond := do
  match ← strField j "c" with
  | "cmp" =>
    let op ← match ← strField j "op" with
      | "<" => pure Cmp.lt
      | "<=" => pure Cmp.le
      | ">" => pure Cmp.gt
      | ">=" => pure Cmp.ge
      | o => throw s!"unknown comparison '{o}'"
    pure (.cmp op (← parseMExp (← field j "a")) (← parseMExp (← field j "b")))
  | "not" => pure (.not (← parseMCond (← field j "a")))
  | "other" => pure .other
  | o => throw s!"unknown test '{o}'"

/-- Statements; `"seq"` takes a list `ss` (nested to the right). -/
partial def parseMStmt (j : Json) : Except String MStmt := do
  match ← strField j "s" with
  | "skip" => pure .skip
  | "assign" => pure (.assign (← getNat j "w") (← getNat j "x") (← parseMExp (← field j "e")))
  | "cost" => pure (.cost (← getNat j "w"))
  | "call" =>
    let args ← parseArr j "args" (fun a => do
      let hi ← match a.getObjVal? "hi" with
        | .ok v => match v.getInt? with
          | .ok n => pure (some n)
          | .error e => throw e
        | .error _ => pure none
      pure ((← getNat a "x"), hi, (← parseMExp (← field a "e"))))
    pure (.call (← getNat j "f") args)
  | "assignU" =>
    pure (.assignU (← getNat j "w") (← getNat j "x") (← getInt j "hi") (← parseMExp (← field j "e")))
  | "div" =>
    let op ← match ← strField j "op" with
      | "div" => pure DivOp.div
      | "rem" => pure DivOp.rem
      | "and" => pure DivOp.and
      | o => throw s!"unknown operation '{o}'"
    let old ← match j.getObjVal? "old" with
      | .ok v => match v.getNat? with
        | .ok n => pure (some n)
        | .error e => throw e
      | .error _ => pure none
    pure (.divStore (← getNat j "w") (← getNat j "x") op (← parseMExp (← field j "y"))
      (← getInt j "c") old)
  | "seq" =>
    let ss ← parseArr j "ss" parseMStmt
    pure (ss.foldr (fun a b => match b with
      | .skip => a
      | _ => .seq a b) .skip)
  | "if" =>
    pure (.ite (← getNat j "w") (← parseMCond (← field j "c")) (← parseMStmt (← field j "a"))
      (← parseMStmt (← field j "b")))
  | "while" =>
    pure (.while (← getNat j "w") (← parseArr j "cs" parseMCond) (← parseMStmt (← field j "body")))
  | "for" =>
    pure (.for_ (← parseMStmt (← field j "init")) (← getNat j "w") (← parseArr j "cs" parseMCond)
      (← parseMStmt (← field j "inc")) (← parseMStmt (← field j "body")))
  | o => throw s!"unknown statement '{o}'"


def optNat (j : Json) (k : String) : Except String (Option Nat) :=
  match j.getObjVal? k with
  | .ok v => match v.getNat? with
    | .ok n => pure (some n)
    | .error e => throw e
  | .error _ => pure none

/-- Statements with jumps (`MiniC.JStmt`); `"seq"` takes a list `js`. -/
partial def parseJStmt (j : Json) : Except String JStmt := do
  match ← strField j "j" with
  | "basic" => pure (.basic (← parseMStmt (← field j "s")))
  | "seq" =>
    let ss ← parseArr j "js" parseJStmt
    match ss.reverse with
    | [] => pure (.basic .skip)
    | last :: rest => pure (rest.foldl (fun acc a => .seq a acc) last)
  | "if" =>
    pure (.ite (← getNat j "w") (← parseMCond (← field j "c")) (← parseJStmt (← field j "a"))
      (← parseJStmt (← field j "b")))
  | "loop" =>
    let inc ← match j.getObjVal? "inc" with
      | .ok v => some <$> parseMStmt v
      | .error _ => pure none
    pure (.loop (← getNat j "w") (← parseArr j "cs" parseMCond) (← parseJStmt (← field j "body"))
      inc (← optNat j "fb") (← optNat j "fc"))
  | "break" => pure (.brk (← getNat j "w"))
  | "continue" => pure (.cont (← getNat j "w"))
  | "return" => pure (.ret (← parseMStmt (← field j "s")))
  | "switch" => pure (.switch (← getNat j "w") (← getNat j "sc") (← parseArr j "groups" parseJStmt))
  | "do" =>
    pure (.doLoop (← getNat j "w") (← parseArr j "cs" parseMCond) (← parseJStmt (← field j "body"))
      (← optNat j "fb") (← optNat j "fc"))
  | o => throw s!"unknown statement '{o}'"

/-- A source: plain mini-C, or mini-C with jumps and its return flag. -/
inductive Source where
  | plain (s : MStmt)
  | jumps (r : Nat) (j : JStmt)

/-- A program certificate as read from a file: the functions (with their names, for
    the messages) and the names of the variables (for `--print`). -/
structure Program where
  name : String
  vars : List String
  funs : List (String × FunCert)
  /-- The mini-C source of each function, if given (same order as `funs`). -/
  sources : List (Option Source)
  /-- Response-time claims: name, task, handlers (function, min inter-arrival, overhead), R. -/
  responses : List (String × String × List (String × Nat × Nat) × Nat) := []

def strList (j : Json) (k : String) : List String :=
  match j.getObjVal? k with
  | .ok v => match v.getArr? with
    | .ok a => a.toList.filterMap fun x => match x.getStr? with
      | .ok s => some s
      | .error _ => none
    | .error _ => []
  | .error _ => []

def nameOf (j : Json) (k : String) : String :=
  match j.getObjValAs? String k with
  | .ok s => s
  | .error _ => "(unnamed)"

/-- Version 1: a single function, without calls. -/
def parseCert (j : Json) : Except String Program := do
  let body ← parseCmd (← field j "program")
  -- A standalone certificate is not called: its own writes serve as its frame.
  let F : FunCert := ⟨← parseArr j "pre" parseLin, ← getSB j "bound", ← parseArr j "post" parseLin,
    writes [] body, some body⟩
  pure ⟨nameOf j "function", strList j "variables", [(nameOf j "function", F)], [none], []⟩

/-- Version 2: a function of a program certificate; `"contract": true` and no body for an
    assumed contract. -/
def parseSource (j : Json) : Except String (Option Source) :=
  match j.getObjVal? "source" with
  | .ok v => (some ∘ Source.plain) <$> parseMStmt v
  | .error _ => match j.getObjVal? "jsource" with
    | .ok v => do pure (some (.jumps (← getNat v "ret") (← parseJStmt (← field v "body"))))
    | .error _ => pure none

def parseFun (j : Json) : Except String (String × FunCert) := do
  let contract := match j.getObjValAs? Bool "contract" with
    | .ok b => b
    | .error _ => false
  let body ← if contract then pure none else some <$> parseCmd (← field j "body")
  pure (nameOf j "name", ⟨← parseArr j "pre" parseLin, ← getSB j "bound",
    ← parseArr j "post" parseLin, ← natList (← field j "mods") "mods", body⟩)

def parseFile (j : Json) : Except String (List Program) := do
  let fmt := match j.getObjValAs? String "format" with
    | .ok s => s
    | .error _ => ""
  if fmt != "crosscheck-certificates" then
    throw "not a certificate file (field 'format' must be \"crosscheck-certificates\")"
  let ver ← getNat j "version"
  if ver == 1 then parseArr j "certificates" parseCert
  else if ver == 2 then
    parseArr j "programs" fun p => do
      let responses ← match p.getObjVal? "responses" with
        | .ok _ => parseArr p "responses" fun r => do
            let hs ← parseArr r "handlers" fun h => do
              let fn ← match h.getObjValAs? String "function" with
                | .ok s => pure s
                | .error _ => throw "a handler needs a 'function'"
              pure (fn, ← getNat h "min_interarrival", (match h.getObjValAs? Nat "overhead" with
                | .ok n => n
                | .error _ => 0))
            let task ← match r.getObjValAs? String "task" with
              | .ok s => pure s
              | .error _ => throw "a response claim needs a 'task'"
            pure (nameOf r "name", task, hs, ← getNat r "R")
        | .error _ => pure []
      pure ⟨nameOf p "name", strList p "variables", ← parseArr p "functions" parseFun,
        ← parseArr p "functions" parseSource, responses⟩
  else throw s!"unsupported version {ver} (this checker reads versions 1 and 2)"

/-! ### Cycle certificates (`Cycles`) -/

def parseRow (j : Json) : Except String ImperativeOptimization.Cycles.Row := do
  let coef ← parseArr j "coef" fun p => do
    match ← intList p "a row coefficient [edge, a]" with
    | [e, a] => if e < 0 then throw "a row's edge must be a natural number" else pure (e.toNat, a)
    | _ => throw "a row coefficient must be [edge, a]"
  pure ⟨coef, ← getInt j "rhs"⟩

/-- A cycle program: its name and its functions (name, graph, certificate); calls are by
    function name, converted to the function's position. -/
def parseCyclesProgram (p : Json) : Except String (String × List (String × ImperativeOptimization.Cycles.Graph × ImperativeOptimization.Cycles.Cert)) := do
  let fns ← parseArr p "functions" pure
  let names := fns.map (nameOf · "name")
  let funs ← fns.mapM fun f => do
    let edges ← parseArr f "edges" fun e => do
      let calls ← match e.getObjVal? "calls" with
        | .ok v => match v.getArr? with
          | .ok a => a.toList.mapM fun c => match c.getStr? with
            | .ok n => match names.indexOf? n with
              | some i => pure i
              | none => throw s!"call of '{n}', which is not a function of the program"
            | .error _ => throw "'calls' must be an array of function names"
          | .error _ => throw "'calls' must be an array of function names"
        | .error _ => pure []
      pure (⟨← getNat e "src", ← getNat e "dst", ← getNat e "w", calls⟩ : ImperativeOptimization.Cycles.Edge)
    let c ← field f "certificate"
    let G : ImperativeOptimization.Cycles.Graph := ⟨← getNat f "entry", ← getNat f "exit", edges, ← parseArr f "rows" parseRow⟩
    let C : ImperativeOptimization.Cycles.Cert := ⟨← getNat c "scale", ← intList (← field c "pot") "pot",
      ← natList (← field c "mult") "mult", ← getNat c "bound"⟩
    pure (nameOf f "name", G, C)
  pure (nameOf p "name", funs)

def parseCyclesFile (j : Json) : Except String (List (String × List (String × ImperativeOptimization.Cycles.Graph × ImperativeOptimization.Cycles.Cert))) := do
  let ver ← getNat j "version"
  if ver != 1 then throw s!"unsupported version {ver} of crosscheck-cycles (this checker reads version 1)"
  parseArr j "programs" parseCyclesProgram

/-- Check a cycle file; the exit status. -/
def runCycles (progs : List (String × List (String × ImperativeOptimization.Cycles.Graph × ImperativeOptimization.Cycles.Cert))) : IO UInt32 := do
  let mut status : UInt32 := 0
  for (pname, funs) in progs do
    let bounds := funs.map (·.2.2.bound)
    for (name, G, C) in funs do
      let ok := ImperativeOptimization.Cycles.checkFn bounds G C
      IO.println s!"{if ok then "ACCEPTED" else "REJECTED"} {name}: at most {C.bound} cycles ({G.edges.length} edges, {G.rows.length} rows)"
    -- the decision of the verified `checkProgram` (theorem `Cycles.program_sound`)
    let okP := ImperativeOptimization.Cycles.checkProgram (funs.map (·.2.1)) (funs.map (·.2.2))
    IO.println s!"PROGRAM  {pname}: {if okP then "ACCEPTED" else "REJECTED"} (cycle bounds; the graphs, weights and rows are trusted)"
    if !okP then status := 1
  return status

/-! ### Cycle certificates on machine code (`Thumb`) -/

def parseCode (j : Json) : Except String ImperativeOptimization.Thumb.Code := do
  let c ← field j "code"
  pure ⟨← getNat c "base", (← natList (← field c "halfwords") "halfwords").toArray⟩

def parseMRow (j : Json) : Except String ImperativeOptimization.Thumb.MRow := do
  let coef ← parseArr j "coef" fun p => do
    match ← intList p "a row coefficient [src, dst, a]" with
    | [s, t, a] =>
      if s < 0 || t < 0 then throw "row addresses must be natural numbers" else pure (s.toNat, t.toNat, a)
    | _ => throw "a row coefficient must be [src, dst, a]"
  pure ⟨coef, ← getInt j "rhs"⟩

/-- A sparse vector `[[variable, coefficient], ...]` as a dense one (repetitions add up). -/
def denseOf (l : List (Nat × Int)) : List Int :=
  let n := (l.map (·.1 + 1)).foldl max 0
  (List.range n).map fun v => (l.filter (·.1 == v)).foldl (fun s p => s + p.2) 0

def parseSparse (j : Json) (what : String) : Except String (List (Nat × Int)) := do
  let ps ← match j.getArr? with
    | .ok a => pure a.toList
    | .error _ => throw s!"{what} must be an array of [index, value]"
  ps.mapM fun p => do
    match ← intList p what with
    | [v, k] => if v < 0 then throw s!"{what}: negative index" else pure (v.toNat, k)
    | _ => throw s!"{what}: [index, value] expected"

/-- A constraint `Σ k·x_v + c ≤ 0` (`{"sv": [[v, k], ...], "c": c}`). -/
def parseDLin (j : Json) : Except String Lin := do
  pure ⟨denseOf (← parseSparse (← field j "sv") "sv"), [], ← getInt j "c"⟩

def parseDPExp (j : Json) : Except String PExp := do
  pure ⟨denseOf (← parseSparse (← field j "sv") "sv"), ← getInt j "c"⟩

def parseKind (j : Json) : Except String ImperativeOptimization.Thumb.FKind :=
  match j.getStr? with
  | .ok "none" => pure .none
  | .ok "add" => pure .add
  | .ok "sub" => pure .sub
  | _ => throw "a kind must be \"none\", \"add\" or \"sub\""

def parseLoop (j : Json) : Except String ImperativeOptimization.Thumb.LoopCert := do
  pure ⟨← getNat j "header", ← natList (← field j "body") "body", ← getNat j "scale", ← getNat j "bound",
    ← parseArr j "pot" parseDPExp⟩

/-- A Farkas certificate `[mu, [[premise, multiplier], ...]]`. -/
def parseProof (j : Json) : Except String (Nat × List Nat) := do
  let a ← match j.getArr? with
    | .ok a => pure a.toList
    | .error _ => throw "a proof must be [mu, [[premise, multiplier], ...]]"
  match a with
  | [mu, lam] =>
    let mu ← match mu.getNat? with
      | .ok n => pure n
      | .error _ => throw "a proof's mu must be a natural number"
    let l ← parseSparse lam "multipliers"
    if l.any (·.2 < 0) then throw "multipliers must be natural numbers"
    pure (mu, (denseOf l).map Int.toNat)
  | _ => throw "a proof must be [mu, [[premise, multiplier], ...]]"

def optArr {α : Type} (j : Json) (k : String) (f : Json → Except String α) : Except String (List α) :=
  match j.getObjVal? k with
  | .ok _ => parseArr j k f
  | .error _ => pure []

/-- A function: entry, instruction addresses, trusted rows, certificate (potentials per
    address in the order of `nodes`, then the exit), and its loop certificate (empty if
    absent). The rows of the certified loops are added after the trusted ones. -/
def parseBFun (f : Json) : Except String
    (String × ImperativeOptimization.Thumb.BFun × ImperativeOptimization.Cycles.Cert × ImperativeOptimization.Thumb.DFun) := do
  let c ← field f "certificate"
  let trusted ← parseArr f "rows" parseMRow
  let loops ← optArr f "loops" parseLoop
  let F0 : ImperativeOptimization.Thumb.BFun :=
    ⟨← getNat f "entry", ← natList (← field f "nodes") "nodes", trusted⟩
  let F : ImperativeOptimization.Thumb.BFun :=
    { F0 with rows := trusted ++ loops.map (ImperativeOptimization.Thumb.loopRow F0) }
  let C : ImperativeOptimization.Cycles.Cert := ⟨← getNat c "scale", ← intList (← field c "pot") "pot",
    ← natList (← field c "mult") "mult", ← getNat c "bound"⟩
  let D : ImperativeOptimization.Thumb.DFun :=
    ⟨← optArr f "kinds" parseKind, ← optArr f "inv" (fun l => match l.getArr? with
        | .ok a => a.toList.mapM parseDLin
        | .error _ => throw "an invariant must be an array of constraints"),
     loops, trusted, ← optArr f "proofs" parseProof,
     ← optArr f "sp" (fun o => match o with
        | .null => pure none
        | _ => match o.getInt? with
          | .ok d => pure (some d)
          | .error _ => throw "a stack offset must be an integer or null"),
     ← match f.getObjVal? "slots" with
        | .ok v => natList v "slots"
        | .error _ => pure [],
     match f.getObjValAs? Bool "frame" with
        | .ok b => b
        | .error _ => false,
     ← optArr f "cong" (fun l => match l.getArr? with
        | .ok a => a.toList.mapM fun x => do
            match ← natList x "a congruence" with
            | [v, e, r] => pure (v, e, r)
            | _ => throw "a congruence must be [variable, exponent, residue]"
        | .error _ => throw "the congruences of an instruction must be an array"),
     ← optArr f "alt" (fun l => match l.getArr? with
        | .ok a => a.toList.mapM fun I => match I.getArr? with
            | .ok b => b.toList.mapM parseDLin
            | .error _ => throw "a disjunct of an invariant must be an array of constraints"
        | .error _ => throw "the alternatives of an instruction must be an array"),
     ← optArr f "pick" (fun l => match l.getArr? with
        | .ok a => a.toList.mapM fun x => do
            match ← intList x "a target" with
            | [j, m, d, s, t] =>
              if j < 0 ∨ d < 0 ∨ s < 0 ∨ t < 0 then throw "a target must be [j, m, d, s, t], j, d, s, t >= 0"
              else pure (j.toNat, m, d.toNat, s.toNat, t.toNat)
            | _ => throw "a target must be [transition, wrap, fact, source disjunct, target disjunct]"
        | .error _ => throw "the targets of an instruction must be an array")⟩
  pure (nameOf f "name", F, C, D)

def parseBinaryFile (j : Json) :
    Except String (Nat × Bool × ImperativeOptimization.Thumb.Code ×
      List (String × List (String × ImperativeOptimization.Thumb.BFun × ImperativeOptimization.Cycles.Cert ×
        ImperativeOptimization.Thumb.DFun))) := do
  let ver ← getNat j "version"
  if ver != 1 && ver != 2 then
    throw s!"unsupported version {ver} of crosscheck-binary-cycles (this checker reads versions 1 and 2)"
  let progs ← parseArr j "programs" fun p => do
    pure (nameOf p "name", ← parseArr p "functions" parseBFun)
  let abi := match j.getObjValAs? Bool "abi" with
    | .ok b => b
    | .error _ => false
  pure (← getNat j "mul_cycles", abi, ← parseCode j, progs)

def runBinary (mul : Nat) (abi : Bool) (code : ImperativeOptimization.Thumb.Code)
    (progs : List (String × List (String × ImperativeOptimization.Thumb.BFun × ImperativeOptimization.Cycles.Cert ×
      ImperativeOptimization.Thumb.DFun))) :
    IO UInt32 := do
  let mut status : UInt32 := 0
  for (pname, funs) in progs do
    let fs := funs.map (·.2.1)
    let entries := fs.map (·.entry)
    let bounds := funs.map (·.2.2.1.bound)
    let Ls := funs.map (·.2.2.2)
    for (name, F, C, D) in funs do
      match ImperativeOptimization.Thumb.buildFn mul code entries F with
      | none => IO.println s!"REJECTED {name}: the graph cannot be built from the code (an instruction address without code, a stop instruction, a successor or callee missing)"
      | some G =>
        let ok := ImperativeOptimization.Cycles.checkFn bounds G C
        IO.println s!"{if ok then "ACCEPTED" else "REJECTED"} {name}: at most {C.bound} cycles ({F.nodes.length} instructions, {G.edges.length} edges, {G.rows.length} rows)"
      if !D.loops.isEmpty || !D.inv.isEmpty then
        let okD := ImperativeOptimization.Thumb.checkDFun mul abi code F D
        IO.println s!"{if okD then "ACCEPTED" else "REJECTED"} {name}: loop bounds of the machine code, {D.loops.length} rows certified, {D.trusted.length} trusted ({D.proofs.length} obligations, {D.slots.length} words of the frame tracked, {(D.cong.map List.length).foldl (· + ·) 0} congruences{if D.frame then ", frame written only through SP (assumed)" else ""})"
    -- the decision of the verified `checkBinary` (theorem `Thumb.binary_sound`)
    let okP := ImperativeOptimization.Thumb.checkBinary mul code fs (funs.map (·.2.2.1))
    let nCert := (Ls.map (·.loops.length)).foldl (· + ·) 0
    let nTrust := (Ls.map (·.trusted.length)).foldl (· + ·) 0
    if Ls.any (fun D => !D.loops.isEmpty || !D.inv.isEmpty) then
      -- the decision of the verified `checkData` (theorem `ThumbData.data_sound`)
      let okD := ImperativeOptimization.Thumb.checkData mul abi code fs Ls
      IO.println s!"PROGRAM  {pname}: {if okP && okD then "ACCEPTED" else "REJECTED"} (cycle bounds of the machine code; MULS {mul} cycles; {nCert} loop rows certified on the machine code, {nTrust} trusted; {if abi then "callees assumed to preserve r4-r7 and SP" else "no assumption on callees"}{if Ls.any (·.frame) then s!", {(Ls.filter (·.frame)).length} frames assumed written only through SP" else ""}; the decoder, the timing table and the effects of the instructions are trusted)"
      if !(okP && okD) then status := 1
    else
      IO.println s!"PROGRAM  {pname}: {if okP then "ACCEPTED" else "REJECTED"} (cycle bounds of the machine code; MULS {mul} cycles; the decoder, the timing table and the loop rows are trusted)"
      if !okP then status := 1
  return status

def showKind : ImperativeOptimization.Thumb.Kind → String
  | .seq => "seq -"
  | .cond t => s!"cond {t}"
  | .jump t => s!"jump {t}"
  | .call t => s!"call {t}"
  | .ret => "ret -"
  | .stop => "stop -"

/-- `--decode`: one line per address: `addr size kind target cycles cycles-not-taken`. -/
def runDecode (j : Json) : Except String (List String) := do
  let mul ← getNat j "mul_cycles"
  let code ← parseCode j
  let addrs ← natList (← field j "addresses") "addresses"
  pure <| addrs.map fun a => match ImperativeOptimization.Thumb.decode mul code a with
    | some i => s!"{a} {i.size} {showKind i.kind} {i.cyc} {i.cycNot}"
    | none => s!"{a} none"

/-- `--effect`: for each case (an address, the low registers, the flags N Z C V), the
    registers after the instruction as `Thumb.effect` and `Thumb.valOf` give them (`k`:
    kept, `=v`: that value, `?`: any), the flags after it (`keep`, `any` or four bits) and
    the fourteen conditions on the flags given (`Thumb.condHolds`), for differential tests. -/
def runEffect (j : Json) : Except String (List String) := do
  let code ← parseCode j
  let abi := match j.getObjValAs? Bool "abi" with
    | .ok b => b
    | .error _ => false
  let cases ← parseArr j "cases" fun c => do
    pure (← getNat c "a", ← natList (← field c "r") "r", ← natList (← field c "f") "f")
  let bit (b : Bool) : String := if b then "1" else "0"
  let showF (f : ImperativeOptimization.Thumb.Flags) : String := bit f.n ++ bit f.z ++ bit f.c ++ bit f.v
  pure <| cases.map fun (a, r, fl) =>
    let e := ImperativeOptimization.Thumb.effect abi code a
    let rf : Nat → Nat := fun i => r.getD i 0
    let regs := (List.range 8).map fun i => match e.dst.find? (fun p => p.1 == i) with
      | none => "k"
      | some (_, v) => match ImperativeOptimization.Thumb.valOf rf v with
        | some x => s!"={x}"
        | none => "?"
    let fs := match e.fl with
      | .keep => "keep"
      | .any => "any"
      | .add x y => showF (ImperativeOptimization.Thumb.flagsAdd (ImperativeOptimization.Thumb.srcVal rf x)
          (ImperativeOptimization.Thumb.srcVal rf y))
      | .sub x y => showF (ImperativeOptimization.Thumb.flagsSub (ImperativeOptimization.Thumb.srcVal rf x)
          (ImperativeOptimization.Thumb.srcVal rf y))
    let f0 : ImperativeOptimization.Thumb.Flags :=
      ⟨fl.getD 0 0 == 1, fl.getD 1 0 == 1, fl.getD 2 0 == 1, fl.getD 3 0 == 1⟩
    let conds := String.join ((List.range 14).map fun cc => bit (ImperativeOptimization.Thumb.condHolds cc f0))
    let st := ImperativeOptimization.Thumb.stackEffect abi code a
    let sps := match st.sp with
      | .keep => "k"
      | .add k => s!"{k}"
      | .any => "?"
    let mems := match st.mem with
      | .keep => "k"
      | .storeSP imm rt => s!"s{imm},{rt}"
      | .push n => s!"p{n}"
      | .other => "o"
    let lds := match st.load with
      | some (rt, imm) => s!"l{rt},{imm}"
      | none => "-"
    s!"{a} {" ".intercalate regs} {fs} {conds} {sps} {mems} {lds} {if st.escapes then 1 else 0}"

/-! ### Printing what was checked -/

def showSB (b : SB) : String :=
  let terms := (b.co.enum.filter (·.2 != 0)).map (fun (i, k) =>
    (if k == 1 then "" else s!"{k}*") ++ s!"max(0,γ{i})") ++
    (b.q.filter (·.1 != 0)).map (fun (k, i, j) =>
      (if k == 1 then "" else s!"{k}*") ++ s!"max(0,γ{i})*max(0,γ{j})")
  " + ".intercalate (if b.c != 0 || terms.isEmpty then toString b.c :: terms else terms)

def varName (vars : List String) (i : Nat) : String := vars.getD i s!"x{i}"

def showAffine (vars : List String) (sv lv : List Int) (c : Int) : String :=
  let term (k : Int) (v : String) : String :=
    if k == 1 then v else if k == -1 then s!"-{v}" else s!"{k}*{v}"
  let terms := (sv.enum.filter (·.2 != 0)).map (fun (i, k) => term k (varName vars i)) ++
    (lv.enum.filter (·.2 != 0)).map (fun (i, k) => term k s!"γ{i}")
  let terms := if c != 0 || terms.isEmpty then terms ++ [toString c] else terms
  " + ".intercalate terms

def showLin (vars : List String) (e : Lin) : String := showAffine vars e.sv e.lv e.c ++ " <= 0"

def showAssn (vars : List String) (A : List Lin) : String :=
  if A.isEmpty then "true" else " && ".intercalate (A.map (showLin vars))

partial def showCmd (vars : List String) (ind : String) : ACmd → String
  | .skip => s!"{ind}skip\n"
  | .assign w x a => s!"{ind}{varName vars x} := {showAffine vars a.sv [] a.c}    [cost {w}]\n"
  | .havoc w x => s!"{ind}{varName vars x} := ?    [cost {w}]\n"
  | .havocC w x cs =>
      s!"{ind}{varName vars x} := ? such that {" && ".intercalate (cs.map fun g => showAffine vars g.sv [] g.c ++ " <= 0")}    [cost {w}]\n"
  | .seq c₁ mid _ _ c₂ =>
      showCmd vars ind c₁ ++ s!"{ind}// {showAssn vars mid}\n" ++ showCmd vars ind c₂
  | .ite w g _ _ c₁ c₂ =>
      s!"{ind}if ({showAffine vars g.sv [] g.c} <= 0) \{    [test cost {w}]\n" ++
      showCmd vars (ind ++ "  ") c₁ ++ s!"{ind}} else \{\n" ++ showCmd vars (ind ++ "  ") c₂ ++
      s!"{ind}}\n"
  | .while w g inv pot d k kl j _ Wb body =>
      s!"{ind}while ({showAffine vars g.sv [] g.c} <= 0) \{    [test cost {w}; invariant " ++
      s!"{showAssn vars inv}; potential ({showAffine vars pot.sv [] pot.c})/{d} <= ({showAffine [] [] (kl.map Int.ofNat) k})/{d}; " ++
      s!"γ{j}; body bound {showSB Wb}]\n" ++ showCmd vars (ind ++ "  ") body ++ s!"{ind}}\n"
  | .whileAnd w gs inv pot d k kl j _ Wb body =>
      s!"{ind}while ({" && ".intercalate (gs.map fun g => showAffine vars g.sv [] g.c ++ " <= 0")}) \{" ++
      s!"    [test cost {w}; invariant {showAssn vars inv}; potential " ++
      s!"({showAffine vars pot.sv [] pot.c})/{d} <= ({showAffine [] [] (kl.map Int.ofNat) k})/{d}; γ{j}; body bound {showSB Wb}]\n" ++
      showCmd vars (ind ++ "  ") body ++ s!"{ind}}\n"
  | .whileLog w gs inv pot b k j _ Wb body =>
      s!"{ind}while ({" && ".intercalate (gs.map fun g => showAffine vars g.sv [] g.c ++ " <= 0")}) \{" ++
      s!"    [test cost {w}; invariant {showAssn vars inv}; logarithmic potential " ++
      s!"{showAffine vars pot.sv [] pot.c} <= {k}, divided by {b} per iteration ({logIters b k} iterations); γ{j}; body bound {showSB Wb}]\n" ++
      showCmd vars (ind ++ "  ") body ++ s!"{ind}}\n"
  | .whileGrow w gs inv pot b K j _ Wb body =>
      s!"{ind}while ({" && ".intercalate (gs.map fun g => showAffine vars g.sv [] g.c ++ " <= 0")}) \{" ++
      s!"    [test cost {w}; invariant {showAssn vars inv}; growing potential " ++
      s!"1 <= {showAffine vars pot.sv [] pot.c} <= {K} under the test, multiplied by {b} per iteration ({logIters b K} iterations); γ{j}; body bound {showSB Wb}]\n" ++
      showCmd vars (ind ++ "  ") body ++ s!"{ind}}\n"
  | .whileUp w gs inv pot d k j _ Wb body =>
      s!"{ind}while ({" && ".intercalate (gs.map fun g => showAffine vars g.sv [] g.c ++ " <= 0")}) \{" ++
      s!"    [test cost {w}; invariant {showAssn vars inv}; potential " ++
      s!"({showAffine vars pot.sv [] pot.c})/{d} <= {k}/{d}; γ{j} = {k} - ({showAffine vars pot.sv [] pot.c}); body bound {showSB Wb}]\n" ++
      showCmd vars (ind ++ "  ") body ++ s!"{ind}}\n"
  | .weaken _ _ _ _ _ c => showCmd vars ind c
  | .dead _ c => s!"{ind}// unreachable\n" ++ showCmd vars ind c
  | .call w f inst _ _ _ =>
      s!"{ind}call #{f}({", ".intercalate (inst.map fun a => showAffine vars a.sv [] a.c)})    [cost {w}]\n"

end CheckerMain

open CheckerMain in
def main (args : List String) : IO UInt32 := do
  let printIt := args.contains "--print"
  let decodeIt := args.contains "--decode"
  let effectIt := args.contains "--effect"
  let files := args.filter (fun a => a != "--print" && a != "--decode" && a != "--effect")
  if files.isEmpty then
    IO.eprintln "usage: crosscheck-check [--print | --decode | --effect] FILE.json..."
    return 2
  let mut status : UInt32 := 0
  for path in files do
    let read ← (IO.FS.readFile path).toBaseIO
    let text ← match read with
      | .ok t => pure t
      | .error e => do
        IO.eprintln s!"{path}: {e}"
        return 2
    if effectIt then
      match Json.parse text >>= runEffect with
      | .error e =>
        IO.eprintln s!"{path}: malformed effect request: {e}"
        return 2
      | .ok ls => ls.forM IO.println
      continue
    if decodeIt then
      match Json.parse text >>= runDecode with
      | .error e =>
        IO.eprintln s!"{path}: malformed decode request: {e}"
        return 2
      | .ok ls => ls.forM IO.println
      continue
    if (Json.parse text).toOption.bind (fun j => (j.getObjValAs? String "format").toOption) == some "crosscheck-binary-cycles" then
      match Json.parse text >>= parseBinaryFile with
      | .error e =>
        IO.eprintln s!"{path}: malformed binary cycle certificate file: {e}"
        return 2
      | .ok (mul, abi, code, progs) =>
        status := max status (← runBinary mul abi code progs)
      continue
    if (Json.parse text).toOption.bind (fun j => (j.getObjValAs? String "format").toOption) == some "crosscheck-cycles" then
      match Json.parse text >>= parseCyclesFile with
      | .error e =>
        IO.eprintln s!"{path}: malformed cycle certificate file: {e}"
        return 2
      | .ok progs =>
        status := max status (← runCycles progs)
      continue
    match Json.parse text >>= parseFile with
    | .error e =>
      IO.eprintln s!"{path}: malformed certificate file: {e}"
      return 2
    | .ok progs =>
      for p in progs do
        let fs := p.funs.map (·.2)
        for ((name, F), i) in p.funs.zip (List.range p.funs.length) do
          match F.body with
          | none =>
            IO.println s!"ASSUMED  {name} (contract): bound {showSB F.bound}"
          | some b =>
            let ok := checkFun (fs.take i) F
            IO.println s!"{if ok then "ACCEPTED" else "REJECTED"} {name}: bound {showSB F.bound}"
            if printIt then
              IO.println s!"  pre:  {showAssn p.vars F.pre}"
              IO.print (showCmd p.vars "    " b)
              IO.println s!"  post: {showAssn p.vars F.post}"
            if !ok then status := max status 1
            -- the verified `validate` (theorem `MiniC.validated_sound`)
            match p.sources.getD i none with
            | none => pure ()
            | some src =>
              -- plain mini-C: `validate`; with jumps: `validateJ`, and no body of the
              -- program touches the ghost variables (`quietCmd`)
              let (okV, lowered, note) := match src with
                | .plain s => (validate b s, lower s, "")
                | .jumps r j =>
                  let G := ghostSet r j
                  let callable := fs.take i
                  let quiet := callable.all fun F' => match F'.body with
                    | some b' => quietCmd i (costVar :: G) G b'
                    | none => true
                  (validateJ i b r j && quiet, (elim r i j).bind lower,
                    if j.ghosts.isEmpty then ""
                    else if callable.any (·.body.isNone) then
                      " (with jumps; the contracts it may call are assumed not to touch its flags)"
                    else " (with jumps)")
              if okV then
                IO.println s!"VALIDATED {name}: the certificate's program is the lowering of its source{note}"
              else
                IO.println s!"NOT VALIDATED {name}: the certificate's program is not the lowering of its source"
                if printIt then
                  IO.println "  certificate's program (normal form):"
                  IO.print (showCmd p.vars "    " (nf b))
                  match lowered with
                  | some d =>
                    IO.println "  source, lowered (normal form):"
                    IO.print (showCmd p.vars "    " (nf d))

                  | none => IO.println "  source: not in the fragment (a loop test that is not a conjunction of comparisons, or jumps that cannot be eliminated)"
                status := max status 1
        -- the decision of the verified `checkProgram` (theorem `program_sound`)
        let okP := checkProgram fs
        if p.funs.length > 1 || p.funs.any (·.2.body.isNone) then
          let rel := if p.funs.any (·.2.body.isNone) then " (relative to the assumed contracts)" else ""
          IO.println (s!"PROGRAM  {p.name}: {if okP then "ACCEPTED" else "REJECTED"}" ++ rel)
        if !okP then status := max status 1
        -- response-time claims (theorem `Interrupts.rtaHolds_sound`)
        for (rname, task, hs, R) in p.responses do
          let costOf (fname : String) : Option Nat :=
            match p.funs.find? (·.1 == fname) with
            | some (_, F) =>
              if F.body.isSome && okP && F.bound.co.all (· == 0) then some F.bound.c else none
            | none => none
          match costOf task, hs.mapM (fun (h, T, o) => (costOf h).map (fun c => (c + o, T))) with
          | some C, some hl =>
            if rtaHolds C hl R then
              IO.println s!"RESPONSE {rname}: {task} completes within {R} (cost {C}; handlers {hl}; minimum inter-arrival times and overheads assumed)"
            else
              IO.println s!"RESPONSE {rname}: REJECTED (C + interference > {R}, or a period is 0)"
              status := max status 1
          | _, _ =>
            IO.println s!"RESPONSE {rname}: REJECTED (the task or a handler has no accepted constant bound)"
            status := max status 1
  return status
