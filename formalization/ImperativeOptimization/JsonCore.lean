/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/

/-!
# JSON, as the certificate checker reads it

A reader of JSON (RFC 8259) for `crosscheck-check`, with no imports: the checker program then
links only Lean's runtime and core library, not the Lean compiler that `Lean.Data.Json` brings
(124 MB instead of about 8 MB, 54 ms instead of a few ms to start).

It is trusted, as the conversion of `CheckerMain` is: a misreading makes the checker examine
another certificate than the one in the file (`--print` shows what it read). It is stricter
than `Lean.Json.parse` where certificates do not need more: a key repeated in an object is an
error (two readers could take different values), a number is an integer only when written as
one (`-?digits`; `1.0` and `1e2` are other numbers, `getInt?` refuses them), strings must be
valid UTF-8 without raw control characters, an exponent has at most five digits, and objects
and arrays nest at most `maxDepth` deep. `test/json_differential.py` compares it with `Lean.Json.parse` on generated and
malformed documents.
-/

namespace ImperativeOptimization.JsonCore

/-- A JSON value. Numbers that are not integer literals are kept as their text (`num`). -/
inductive Json where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | num (text : String)
  | str (s : String)
  | arr (elems : Array Json)
  | obj (kvs : Array (String × Json))
  deriving Inhabited

/-- The deepest nesting of arrays and objects accepted. -/
def maxDepth : Nat := 10000

namespace Json

def getObjVal? : Json → String → Except String Json
  | obj kvs, k => match kvs.find? (·.1 == k) with
    | some p => .ok p.2
    | none => .error s!"property not found: {k}"
  | _, _ => .error "object expected"

def getArr? : Json → Except String (Array Json)
  | arr a => .ok a
  | _ => .error "array expected"

def getInt? : Json → Except String Int
  | int n => .ok n
  | _ => .error "integer expected"

def getNat? : Json → Except String Nat
  | int n => if 0 ≤ n then .ok n.toNat else .error "natural number expected"
  | _ => .error "natural number expected"

def getStr? : Json → Except String String
  | str s => .ok s
  | _ => .error "string expected"

def getBool? : Json → Except String Bool
  | bool b => .ok b
  | _ => .error "Boolean expected"

/-- The types `getObjValAs?` reads. -/
class FromJ (α : Type) where
  fromJ : Json → Except String α

instance : FromJ Bool := ⟨getBool?⟩
instance : FromJ String := ⟨getStr?⟩
instance : FromJ Nat := ⟨getNat?⟩
instance : FromJ Int := ⟨getInt?⟩

def getObjValAs? (j : Json) (α : Type) [FromJ α] (k : String) : Except String α := do
  FromJ.fromJ (← j.getObjVal? k)

end Json

/-! ### The reader, on the UTF-8 bytes of the text -/

namespace Parse

/-- The parser's state: the bytes and the position. -/
abbrev P := StateT Nat (Except String)

def peek (b : ByteArray) : P (Option UInt8) := do
  let i ← get
  return if i < b.size then some b[i]! else none

def fail {α : Type} (b : ByteArray) (msg : String) : P α := do
  let i ← get
  let _ := b
  throw s!"offset {i}: {msg}"

def skipWs (b : ByteArray) : P Unit := do
  let mut i ← get
  while i < b.size && (b[i]! == 32 || b[i]! == 9 || b[i]! == 10 || b[i]! == 13) do
    i := i + 1
  set i

def expectLit (b : ByteArray) (lit : String) : P Unit := do
  let i ← get
  let l := lit.toUTF8
  if i + l.size ≤ b.size && (List.range l.size).all (fun k => b[i + k]! == l[k]!) then
    set (i + l.size)
  else fail b s!"expected '{lit}'"

def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

/-- The digits from the position; at least one. -/
def digits (b : ByteArray) : P Nat := do
  let i0 ← get
  let mut i := i0
  while i < b.size && isDigit b[i]! do
    i := i + 1
  if i == i0 then fail b "digit expected" else
  set i
  return i - i0

def textOf (b : ByteArray) (i j : Nat) : String :=
  String.fromUTF8! (b.extract i j)

/-- A number: an integer literal is `int`, anything else (fraction, exponent) `num`. -/
def number (b : ByteArray) : P Json := do
  let i0 ← get
  if (← peek b) == some 45 then set (i0 + 1)   -- '-'
  let iDig ← get
  let n ← digits b
  if n > 1 && b[iDig]! == 48 then fail b "a number may not start with 0"
  let mut integer := true
  if (← peek b) == some 46 then   -- '.'
    modify (· + 1); let _ ← digits b; integer := false
  if (← peek b) == some 101 || (← peek b) == some 69 then   -- 'e', 'E'
    modify (· + 1)
    if (← peek b) == some 43 || (← peek b) == some 45 then modify (· + 1)
    if (← digits b) > 5 then fail b "exponent too large"
    integer := false
  let i1 ← get
  let t := textOf b i0 i1
  if integer then
    match t.toInt? with
    | some k => return .int k
    | none => fail b "malformed integer"
  else return .num t

def hexVal (c : UInt8) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c - 48).toNat
  else if 97 ≤ c && c ≤ 102 then some (c - 87).toNat
  else if 65 ≤ c && c ≤ 70 then some (c - 55).toNat
  else none

def hex4 (b : ByteArray) : P Nat := do
  let i ← get
  if i + 4 > b.size then fail b "four hexadecimal digits expected" else
  let mut v := 0
  for k in [0:4] do
    match hexVal b[i + k]! with
    | some d => v := 16 * v + d
    | none => fail b "hexadecimal digit expected"
  set (i + 4)
  return v

/-- The UTF-8 encoding of a code point (below `0x110000`, not a surrogate). -/
def utf8 (c : Nat) : List UInt8 :=
  if c < 0x80 then [c.toUInt8]
  else if c < 0x800 then [(0xC0 + c / 64).toUInt8, (0x80 + c % 64).toUInt8]
  else if c < 0x10000 then
    [(0xE0 + c / 4096).toUInt8, (0x80 + c / 64 % 64).toUInt8, (0x80 + c % 64).toUInt8]
  else [(0xF0 + c / 262144).toUInt8, (0x80 + c / 4096 % 64).toUInt8,
        (0x80 + c / 64 % 64).toUInt8, (0x80 + c % 64).toUInt8]

/-- A string, after its opening quote. -/
def string (b : ByteArray) : P String := do
  let mut out : ByteArray := ByteArray.empty
  repeat
    let i ← get
    if i ≥ b.size then fail b "unterminated string" else
    let c := b[i]!
    if c == 34 then   -- '"'
      set (i + 1); break
    else if c < 32 then fail b "control character in a string"
    else if c == 92 then   -- '\'
      if i + 1 ≥ b.size then fail b "unterminated string" else
      let e := b[i + 1]!
      set (i + 2)
      match e with
      | 34 => out := out.push 34
      | 92 => out := out.push 92
      | 47 => out := out.push 47
      | 98 => out := out.push 8
      | 102 => out := out.push 12
      | 110 => out := out.push 10
      | 114 => out := out.push 13
      | 116 => out := out.push 9
      | 117 =>
        let u ← hex4 b
        let cp ← if 0xD800 ≤ u && u < 0xDC00 then do
            expectLit b "\\u"
            let l ← hex4 b
            if 0xDC00 ≤ l && l < 0xE000 then pure (0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00))
            else fail b "unpaired surrogate"
          else if 0xDC00 ≤ u && u < 0xE000 then fail b "unpaired surrogate"
          else pure u
        for x in utf8 cp do out := out.push x
      | _ => fail b "unknown escape"
    else
      out := out.push c; set (i + 1)
  match String.fromUTF8? out with
  | some s => return s
  | none => fail b "a string must be valid UTF-8"

mutual
partial def value (b : ByteArray) (depth : Nat) : P Json := do
  skipWs b
  match ← peek b with
  | none => fail b "value expected"
  | some c =>
    if c == 123 then modify (· + 1); object b (depth + 1)        -- '{'
    else if c == 91 then modify (· + 1); array b (depth + 1)     -- '['
    else if c == 34 then modify (· + 1); return .str (← string b)
    else if c == 116 then expectLit b "true"; return .bool true
    else if c == 102 then expectLit b "false"; return .bool false
    else if c == 110 then expectLit b "null"; return .null
    else if c == 45 || isDigit c then number b
    else fail b "value expected"

partial def array (b : ByteArray) (depth : Nat) : P Json := do
  if depth > maxDepth then fail b "nested too deep" else
  skipWs b
  if (← peek b) == some 93 then modify (· + 1); return .arr #[]
  let mut xs : Array Json := #[]
  repeat
    xs := xs.push (← value b depth)
    skipWs b
    match ← peek b with
    | some 44 => modify (· + 1)
    | some 93 => modify (· + 1); break
    | _ => fail b "',' or ']' expected"
  return .arr xs

partial def object (b : ByteArray) (depth : Nat) : P Json := do
  if depth > maxDepth then fail b "nested too deep" else
  skipWs b
  if (← peek b) == some 125 then modify (· + 1); return .obj #[]
  let mut kvs : Array (String × Json) := #[]
  repeat
    skipWs b
    if (← peek b) != some 34 then fail b "a key (string) expected" else
    modify (· + 1)
    let k ← string b
    if kvs.any (·.1 == k) then fail b s!"key '{k}' repeated in an object" else
    skipWs b
    if (← peek b) != some 58 then fail b "':' expected" else
    modify (· + 1)
    kvs := kvs.push (k, ← value b depth)
    skipWs b
    match ← peek b with
    | some 44 => modify (· + 1)
    | some 125 => modify (· + 1); break
    | _ => fail b "',' or '}' expected"
  return .obj kvs
end

end Parse

/-- Reads a JSON document (one value, surrounded by white space only). -/
def Json.parse (s : String) : Except String Json := do
  let b := s.toUTF8
  let (v, i) ← (do let v ← Parse.value b 0; Parse.skipWs b; pure v : Parse.P Json).run 0
  if i < b.size then throw s!"offset {i}: end of input expected" else pure v

end ImperativeOptimization.JsonCore
