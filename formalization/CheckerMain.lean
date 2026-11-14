/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Lean.Data.Json
import ImperativeOptimization.CheckerCore

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

Exit status: 0 if every certificate is accepted, 1 if one is rejected, 2 on a malformed
input.
-/

open Lean ImperativeOptimization.Checker

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

partial def parseCmd (j : Json) : Except String ACmd := do
  let node ← match (← field j "node").getStr? with
    | .ok s => pure s
    | .error _ => throw "field 'node' must be a string"
  match node with
  | "skip" => pure .skip
  | "assign" => pure (.assign (← getNat j "w") (← getNat j "x") (← parsePExp (← field j "a")))
  | "havoc" => pure (.havoc (← getNat j "w") (← getNat j "x"))
  | "seq" =>
      pure (.seq (← parseCmd (← field j "c1")) (← parseArr j "mid" parseLin)
        (← getNat j "B1") (← getNat j "B2") (← parseCmd (← field j "c2")))
  | "ite" =>
      pure (.ite (← getNat j "w") (← parsePExp (← field j "g")) (← getNat j "B1")
        (← getNat j "B2") (← parseCmd (← field j "c1")) (← parseCmd (← field j "c2")))
  | "while" =>
      pure (.while (← getNat j "w") (← parsePExp (← field j "g")) (← parseArr j "inv" parseLin)
        (← parsePExp (← field j "pot")) (← getNat j "d") (← getInt j "k") (← getNat j "j")
        (← parseFarkas (← field j "posCert")) (← getNat j "Wb") (← parseCmd (← field j "body")))
  | "weaken" =>
      pure (.weaken (← parseArr j "P" parseLin) (← parseArr j "preCerts" parseFarkas)
        (← getNat j "B") (← parseArr j "Q" parseLin) (← parseArr j "postCerts" parseFarkas)
        (← parseCmd (← field j "c")))
  | "dead" => pure (.dead (← parseFarkas (← field j "cert")) (← parseCmd (← field j "c")))
  | other => throw s!"unknown node '{other}'"

structure Cert where
  name : String
  vars : List String
  pre : List Lin
  bound : Nat
  post : List Lin
  prog : ACmd

def parseCert (j : Json) : Except String Cert := do
  let name := match j.getObjValAs? String "function" with
    | .ok s => s
    | .error _ => "(unnamed)"
  let vars := match j.getObjVal? "variables" with
    | .ok v => match v.getArr? with
      | .ok a => a.toList.filterMap fun x => match x.getStr? with
        | .ok s => some s
        | .error _ => none
      | .error _ => []
    | .error _ => []
  pure ⟨name, vars, ← parseArr j "pre" parseLin, ← getNat j "bound", ← parseArr j "post" parseLin,
    ← parseCmd (← field j "program")⟩

def parseFile (j : Json) : Except String (List Cert) := do
  let fmt := match j.getObjValAs? String "format" with
    | .ok s => s
    | .error _ => ""
  if fmt != "crosscheck-certificates" then
    throw "not a certificate file (field 'format' must be \"crosscheck-certificates\")"
  let ver ← getNat j "version"
  if ver != 1 then throw s!"unsupported version {ver} (this checker reads version 1)"
  parseArr j "certificates" parseCert

/-! ### Printing what was checked -/

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
  | .seq c₁ mid _ _ c₂ =>
      showCmd vars ind c₁ ++ s!"{ind}// {showAssn vars mid}\n" ++ showCmd vars ind c₂
  | .ite w g _ _ c₁ c₂ =>
      s!"{ind}if ({showAffine vars g.sv [] g.c} <= 0) \{    [test cost {w}]\n" ++
      showCmd vars (ind ++ "  ") c₁ ++ s!"{ind}} else \{\n" ++ showCmd vars (ind ++ "  ") c₂ ++
      s!"{ind}}\n"
  | .while w g inv pot d k j _ Wb body =>
      s!"{ind}while ({showAffine vars g.sv [] g.c} <= 0) \{    [test cost {w}; invariant " ++
      s!"{showAssn vars inv}; potential ({showAffine vars pot.sv [] pot.c})/{d} <= {k}/{d}; " ++
      s!"γ{j}; body bound {Wb}]\n" ++ showCmd vars (ind ++ "  ") body ++ s!"{ind}}\n"
  | .weaken _ _ _ _ _ c => showCmd vars ind c
  | .dead _ c => s!"{ind}// unreachable\n" ++ showCmd vars ind c

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
    | .ok certs =>
      for c in certs do
        let ok := check c.pre c.prog c.bound c.post
        IO.println s!"{if ok then "ACCEPTED" else "REJECTED"} {c.name}: bound {c.bound}"
        if printIt then
          IO.println s!"  pre:  {showAssn c.vars c.pre}"
          IO.print (showCmd c.vars "    " c.prog)
          IO.println s!"  post: {showAssn c.vars c.post}"
        if !ok then status := max status 1
  return status
