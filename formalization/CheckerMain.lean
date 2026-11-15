/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Lean.Data.Json
import ImperativeOptimization.CheckerCore
import ImperativeOptimization.MiniCCore

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
the source from JSON is trusted in the same way.

Exit status: 0 if every certificate is accepted, 1 if one is rejected, 2 on a malformed
input.
-/

open Lean ImperativeOptimization.Checker ImperativeOptimization.MiniC

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
    pure ⟨c, co⟩

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

/-- A program certificate as read from a file: the functions (with their names, for
    the messages) and the names of the variables (for `--print`). -/
structure Program where
  name : String
  vars : List String
  funs : List (String × FunCert)
  /-- The mini-C source of each function, if given (same order as `funs`). -/
  sources : List (Option MStmt)

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
  pure ⟨nameOf j "function", strList j "variables", [(nameOf j "function", F)], [none]⟩

/-- Version 2: a function of a program certificate; `"contract": true` and no body for an
    assumed contract. -/
def parseSource (j : Json) : Except String (Option MStmt) :=
  match j.getObjVal? "source" with
  | .ok v => some <$> parseMStmt v
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
      pure ⟨nameOf p "name", strList p "variables", ← parseArr p "functions" parseFun,
        ← parseArr p "functions" parseSource⟩
  else throw s!"unsupported version {ver} (this checker reads versions 1 and 2)"

/-! ### Printing what was checked -/

def showSB (b : SB) : String :=
  let terms := (b.co.enum.filter (·.2 != 0)).map (fun (i, k) =>
    (if k == 1 then "" else s!"{k}*") ++ s!"max(0,γ{i})")
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
  | .weaken _ _ _ _ _ c => showCmd vars ind c
  | .dead _ c => s!"{ind}// unreachable\n" ++ showCmd vars ind c
  | .call w f inst _ _ _ =>
      s!"{ind}call #{f}({", ".intercalate (inst.map fun a => showAffine vars a.sv [] a.c)})    [cost {w}]\n"

end CheckerMain

open CheckerMain in
def main (args : List String) : IO UInt32 := do
  let printIt := args.contains "--print"
  let files := args.filter (· != "--print")
  if files.isEmpty then
    IO.eprintln "usage: crosscheck-check [--print] FILE.json..."
    return 2
  let mut status : UInt32 := 0
  for path in files do
    let read ← (IO.FS.readFile path).toBaseIO
    let text ← match read with
      | .ok t => pure t
      | .error e => do
        IO.eprintln s!"{path}: {e}"
        return 2
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
              if validate b src then
                IO.println s!"VALIDATED {name}: the certificate's program is the lowering of its source"
              else
                IO.println s!"NOT VALIDATED {name}: the certificate's program is not the lowering of its source"
                if printIt then
                  IO.println "  certificate's program (normal form):"
                  IO.print (showCmd p.vars "    " (nf b))
                  match lower src with
                  | some d =>
                    IO.println "  source, lowered (normal form):"
                    IO.print (showCmd p.vars "    " (nf d))
                  | none => IO.println "  source: not in the fragment (a loop test that is not a conjunction of comparisons)"
                status := max status 1
        -- the decision of the verified `checkProgram` (theorem `program_sound`)
        let okP := checkProgram fs
        if p.funs.length > 1 || p.funs.any (·.2.body.isNone) then
          let rel := if p.funs.any (·.2.body.isNone) then " (relative to the assumed contracts)" else ""
          IO.println (s!"PROGRAM  {p.name}: {if okP then "ACCEPTED" else "REJECTED"}" ++ rel)
        if !okP then status := max status 1
  return status
