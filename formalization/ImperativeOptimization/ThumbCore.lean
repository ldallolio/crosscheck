/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import ImperativeOptimization.CyclesCore

/-!
# Cycle bounds of Cortex-M0 machine code: decoder, timing table, graph construction

The executable part (no mathlib) of the cycle check on the machine code itself, instead of
on a control-flow graph supplied by the producer (`Cycles`):

* `decode`: the ARMv6-M Thumb instruction set, classified by its effect on the program
  counter (`Kind`: sequential, conditional branch, branch, call `BL`, return `BX LR` or
  `POP {.., PC}`, or `stop`: any other write of the PC, undefined or unsupported
  instructions), with its size and its cycles on the Cortex-M0 with zero-wait-state memory
  (instruction summary of the Arm Cortex-M0 Technical Reference Manual, Table 3-1; the
  same table as `benchmarks/cycles/m0.py`, compared exhaustively by
  `benchmarks/cycles/test_thumb.py`); MULS costs `mul` cycles (1 or 32 by configuration);
* `trans`: the successors of an instruction, with their cycles and calls;
* `buildFn`: the control-flow graph of a function, built from the code: one node per
  instruction address given by the producer, which must be closed under `trans` and
  contain no `stop` instruction (`closed`); loop rows given on pairs of addresses are
  translated to the graph's edges;
* `checkBinary`: the graphs of all functions, then `Cycles.checkProgram`.

`Thumb.binary_sound` proves that every run of a function in the semantics of `Thumb`
(each step allowed by `decode`/`trans`; `stop` instructions and addresses without code
may do anything) is a run of the built graph, so the certified bound holds for it.
The decoder, the timing table and that semantics are the specification of the processor:
they are trusted, as an instruction-set semantics is.
-/

namespace ImperativeOptimization.Thumb

open ImperativeOptimization.Cycles

/-- Machine code: 16-bit halfwords at consecutive even addresses from `base`. -/
structure Code where
  base : Nat
  hw : Array Nat

/-- The halfword at address `a`, if there is code there. -/
def Code.get (c : Code) (a : Nat) : Option Nat :=
  if c.base ≤ a ∧ (a - c.base) % 2 = 0 then c.hw[(a - c.base) / 2]? else none

/-- The effect of an instruction on the program counter. -/
inductive Kind where
  | seq
  | cond (t : Nat)
  | jump (t : Nat)
  | call (t : Nat)
  | ret
  | stop
  deriving DecidableEq, Repr

/-- A decoded instruction: size in bytes, kind, cycles (taken, for a conditional branch),
    cycles when a conditional branch is not taken. -/
structure Insn where
  size : Nat
  kind : Kind
  cyc : Nat
  cycNot : Nat
  deriving DecidableEq, Repr

/-- The signed value of the low `bits` bits of `v`. -/
def sx (v bits : Nat) : Int :=
  let v := v % 2 ^ bits
  if v ≥ 2 ^ (bits - 1) then (v : Int) - 2 ^ bits else v

/-- A branch target: the address of the instruction plus 4 plus the offset. -/
def target (a : Nat) (off : Int) : Option Nat :=
  let t : Int := a + 4 + off
  if t < 0 then none else some t.toNat

/-- The number of registers in the low 8 bits of a register list. -/
def popcount8 (h : Nat) : Nat := (List.range 8).foldl (fun n i => n + (h >>> i) % 2) 0

def seqI (size cyc : Nat) : Insn := ⟨size, .seq, cyc, cyc⟩
def stopI (size : Nat) : Insn := ⟨size, .stop, 0, 0⟩

/-- ARMv6-M Thumb decoding and Cortex-M0 cycles (see the module documentation). -/
def decode (mul : Nat) (c : Code) (a : Nat) : Option Insn :=
  match c.get a with
  | none => none
  | some h =>
  let top5 := h >>> 11
  if top5 = 0b11101 ∨ top5 = 0b11110 ∨ top5 = 0b11111 then
    -- 32-bit instructions: only BL is supported
    match c.get (a + 2) with
    | none => none
    | some h2 =>
      if top5 = 0b11110 ∧ h2 >>> 14 = 3 ∧ (h2 >>> 12) % 2 = 1 then
        let s := (h >>> 10) % 2
        let i1 := 1 - (((h2 >>> 13) % 2) ^^^ s)
        let i2 := 1 - (((h2 >>> 11) % 2) ^^^ s)
        let imm := s * 2 ^ 24 + i1 * 2 ^ 23 + i2 * 2 ^ 22 + (h % 1024) * 2 ^ 12 + (h2 % 2048) * 2
        match target a (sx imm 25) with
        | some t => some ⟨4, .call t, 4, 4⟩
        | none => some (stopI 4)
      else some (stopI 4)
  -- shifts, add/sub register or 3-bit immediate; move/compare/add/sub 8-bit immediate
  else if top5 ≤ 7 then some (seqI 2 1)
  -- data processing (MULS: `mul` cycles)
  else if h >>> 10 = 0b010000 then some (seqI 2 (if (h >>> 6) % 16 = 13 then mul else 1))
  -- high-register operations and branch-exchange
  else if h >>> 10 = 0b010001 then
    let opc := (h >>> 8) % 4
    let d := ((h >>> 7) % 2) * 8 + h % 8
    if opc = 3 then
      if (h >>> 7) % 2 = 0 ∧ (h >>> 3) % 16 = 14 then some ⟨2, .ret, 3, 3⟩   -- BX LR
      else some (stopI 2)                                                    -- BLX, other BX
    else if d = 15 ∧ opc ≠ 1 then some (stopI 2)                             -- ADD/MOV to PC
    else some (seqI 2 1)
  -- loads and stores: literal, register offset, immediate offset, SP-relative
  else if top5 = 0b01001 ∨ h >>> 12 = 0b0101 ∨ h >>> 13 = 0b011 ∨ h >>> 12 = 0b1000 ∨
      h >>> 12 = 0b1001 then some (seqI 2 2)
  -- ADR, ADD (SP plus immediate)
  else if top5 = 0b10100 ∨ top5 = 0b10101 then some (seqI 2 1)
  -- miscellaneous
  else if h >>> 12 = 0b1011 then
    if h >>> 8 = 0b10110000 ∨ h >>> 8 = 0b10110010 then some (seqI 2 1)   -- SP adjust, extend
    else if h >>> 9 = 0b1011010 then some (seqI 2 (1 + popcount8 h + (h >>> 8) % 2))  -- PUSH
    else if h >>> 9 = 0b1011110 then                                        -- POP
      let n := popcount8 h + (h >>> 8) % 2
      if (h >>> 8) % 2 = 1 then some ⟨2, .ret, 4 + n, 4 + n⟩ else some (seqI 2 (1 + n))
    else if h >>> 8 = 0b10111010 then                                       -- REV*
      if (h >>> 6) % 4 = 2 then some (stopI 2) else some (seqI 2 1)
    else if h = 0xBF00 ∨ h = 0xBF10 ∨ h = 0xBF40 then some (seqI 2 1)       -- NOP, YIELD, SEV
    else some (stopI 2)                                                     -- WFI, WFE, CPS, BKPT...
  -- STM, LDM
  else if h >>> 12 = 0b1100 then some (seqI 2 (1 + popcount8 h))
  -- conditional branch (condition 14: UDF, 15: SVC)
  else if h >>> 12 = 0b1101 then
    if (h >>> 8) % 16 ≥ 14 then some (stopI 2)
    else match target a (sx (h % 256) 8 * 2) with
      | some t => some ⟨2, .cond t, 3, 1⟩
      | none => some (stopI 2)
  -- unconditional branch
  else if top5 = 0b11100 then
    match target a (sx (h % 2048) 11 * 2) with
    | some t => some ⟨2, .jump t, 3, 3⟩
    | none => some (stopI 2)
  else some (stopI 2)

/-- The successors of instruction `i` at address `a`: next address (`none`: the function
    returns), cycles, called functions (by address). A `stop` instruction has none here;
    the semantics lets it do anything, and the graph construction refuses it. -/
def trans (i : Insn) (a : Nat) : List (Option Nat × Nat × List Nat) :=
  match i.kind with
  | .seq => [(some (a + i.size), i.cyc, [])]
  | .cond t => [(some t, i.cyc, []), (some (a + i.size), i.cycNot, [])]
  | .jump t => [(some t, i.cyc, [])]
  | .call t => [(some (a + i.size), i.cyc, [t])]
  | .ret => [(none, i.cyc, [])]
  | .stop => []

/-- A loop row on transitions between addresses: `Σ coef(src, dst)·x(src → dst) ≤ rhs`. -/
structure MRow where
  coef : List (Nat × Nat × Int)
  rhs : Int
  deriving DecidableEq, Repr

/-- The coefficient of the transition `a → n` in a row. -/
def coefPair : List (Nat × Nat × Int) → Nat → Option Nat → Int
  | [], _, _ => 0
  | (s, t, k) :: rest, a, n => (if s = a ∧ n = some t then k else 0) + coefPair rest a n

/-- A function of the binary: entry address, the addresses of its instructions (given by
    the producer; checked to be closed), loop rows. -/
structure BFun where
  entry : Nat
  nodes : List Nat
  rows : List MRow

/-- The position of `t` in a list. -/
def find : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: xs, t => if x = t then some 0 else (find xs t).map (· + 1)

/-- `f` on every element, if it succeeds on all. -/
def optMap {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => match f x, optMap f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

/-- Graph node of an address (`none`: the exit node, numbered after the instructions). -/
def nid (nodes : List Nat) : Option Nat → Nat
  | none => nodes.length
  | some a => (find nodes a).getD nodes.length

/-- The transitions of the instructions at `nodes`: (address, next, cycles, callees). -/
def medges (mul : Nat) (c : Code) : List Nat → List (Nat × Option Nat × Nat × List Nat)
  | [] => []
  | a :: as => (match decode mul c a with
      | some i => (trans i a).map fun p => (a, p.1, p.2.1, p.2.2)
      | none => []) ++ medges mul c as

/-- The entry is a node, every node decodes to an instruction other than `stop`, and every
    successor address is a node. -/
def closed (mul : Nat) (c : Code) (entry : Nat) (nodes : List Nat) : Bool :=
  decide (entry ∈ nodes) && nodes.all fun a => match decode mul c a with
    | some i => decide (i.kind ≠ .stop) && (trans i a).all fun p => match p.1 with
        | some q => decide (q ∈ nodes)
        | none => true
    | none => false

/-- Pairs (position from `k`, element). -/
def indexed {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | k, x :: xs => (k, x) :: indexed (k + 1) xs

/-- The graph edge of a transition (callees by position in `entries`). -/
def mkEdge (entries nodes : List Nat) (m : Nat × Option Nat × Nat × List Nat) : Option Edge :=
  match optMap (find entries) m.2.2.2 with
  | some gs => some ⟨nid nodes (some m.1), nid nodes m.2.1, m.2.2.1, gs⟩
  | none => none

/-- A row on the graph's edges (numbered as the transitions). -/
def mkRow (me : List (Nat × Option Nat × Nat × List Nat)) (r : MRow) : Row :=
  ⟨(indexed 0 me).map (fun p => (p.1, coefPair r.coef p.2.1 p.2.2.1)), r.rhs⟩

/-- The control-flow graph of a function, built from the code. -/
def buildFn (mul : Nat) (c : Code) (entries : List Nat) (f : BFun) : Option Graph :=
  if closed mul c f.entry f.nodes then
    match optMap (mkEdge entries f.nodes) (medges mul c f.nodes) with
    | some edges => some ⟨nid f.nodes (some f.entry), f.nodes.length, edges,
        f.rows.map (mkRow (medges mul c f.nodes))⟩
    | none => none
  else none

/-- The check of cycle certificates on machine code. -/
def checkBinary (mul : Nat) (c : Code) (fs : List BFun) (Cs : List Cert) : Bool :=
  match optMap (buildFn mul c (fs.map (·.entry))) fs with
  | some Ps => checkProgram Ps Cs
  | none => false

end ImperativeOptimization.Thumb
