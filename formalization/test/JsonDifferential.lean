/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Lean.Data.Json
import Std.Data.TreeMap.Raw
import ImperativeOptimization.JsonCore

/-!
# The checker's JSON reader against `Lean.Json.parse` (a test, not part of the checker)

`json-differential FILE...` reads each file with both readers and prints one line per file:
`AGREE` (both read the same value), `BOTHERR` (both refuse it), `COREERR` (only the checker's
reader refuses it: allowed where it is stricter), `LEANERR` (only Lean's refuses it) or `DIFF`
(different values). Values are compared in a canonical form: keys sorted, an integer as `i`
and its value, any other number as `n`. Run by `test/json_differential.py`.
-/

open ImperativeOptimization

/-- A string literal, escaped by Lean (the same function for both readers). -/
def lit (s : String) : String := s.quote

partial def canonLean : Lean.Json → String
  | .null => "null"
  | .bool b => toString b
  | .num n => if n.exponent == 0 then s!"i{n.mantissa}" else "n"
  | .str s => lit s
  | .arr a => "[" ++ ",".intercalate (a.toList.map canonLean) ++ "]"
  | .obj kvs =>
    let l := (kvs.toList : List (String × Lean.Json)).toArray.qsort (fun a b => a.1 < b.1)
    "{" ++ ",".intercalate (l.toList.map fun (k, v) => lit k ++ ":" ++ canonLean v) ++ "}"

partial def canonCore : JsonCore.Json → String
  | .null => "null"
  | .bool b => toString b
  | .int n => s!"i{n}"
  | .num _ => "n"
  | .str s => lit s
  | .arr a => "[" ++ ",".intercalate (a.toList.map canonCore) ++ "]"
  | .obj kvs =>
    let l := kvs.qsort (fun a b => a.1 < b.1)
    "{" ++ ",".intercalate (l.toList.map fun (k, v) => lit k ++ ":" ++ canonCore v) ++ "}"

def main (args : List String) : IO UInt32 := do
  for f in args do
    let s ← IO.FS.readFile f
    let out := match Lean.Json.parse s, JsonCore.Json.parse s with
      | .ok a, .ok b => if canonLean a == canonCore b then "AGREE" else "DIFF"
      | .error _, .error _ => "BOTHERR"
      | .ok _, .error e => s!"COREERR {e}"
      | .error _, .ok _ => "LEANERR"
    IO.println s!"{f} {out}"
  return 0
