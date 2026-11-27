/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/

/-!
# The code of a certificate against the ELF file it comes from

A certificate on machine code (`Thumb.Code`) holds the halfwords of the code and, per
function, its entry address. `Thumb.binary_sound` and `ThumbData.data_sound` are statements
about that code. This module checks, in the checker program, that the code is the one of a
given ELF file, so that the statement "the certificate's code is the binary's" is no longer
trusted: what remains trusted is that the file is loaded as read here.

The file is read as `benchmarks/cycles/m0.py` (`load`) reads it, for 32-bit little-endian
Arm ELF files:

* an executable (`ET_EXEC`): the allocated sections of the code region (addresses below
  `0x20000000` in the ARMv6-M memory map) at their addresses; the image starts at the lowest
  of them (`base`); `NOBITS` sections are zeros;
* a relocatable object (`ET_REL`): the allocated sections in file order from address 0,
  each aligned, `.ARM.exidx*` left out; then stubs for undefined symbols (16-byte aligned
  after the sections, 2 bytes each, in the order the relocations first name them, followed
  by 4096 zero bytes); relocations `R_ARM_ABS32`, `R_ARM_THM_CALL`, `R_ARM_THM_JUMP24` (as a
  `BL`) applied, `R_ARM_PREL31` ignored, any other refused. This is the checker's own link
  of the object: a bound certified on it holds for the object placed this way, and a final
  link elsewhere must preserve it (the code reads its constants through the PC, but an
  absolute address in a literal changes).

`check` then requires that the certificate's `base` be the image's, that every halfword of
the certificate be the halfword of the image at its address, and that every certified
function's entry be the address of the function symbol (`STT_FUNC`) of that name (the last
one, as in `m0.py`).

No mathlib: this module is compiled into `crosscheck-check`.
-/

namespace ImperativeOptimization.Elf

/-- A byte of the file, 0 beyond its end (every structure read is first checked to lie
inside the file). -/
def u8 (d : ByteArray) (o : Nat) : Nat := ((d.data[o]?).map UInt8.toNat).getD 0

def u16 (d : ByteArray) (o : Nat) : Nat := u8 d o + 256 * u8 d (o + 1)

def u32 (d : ByteArray) (o : Nat) : Nat := u16 d o + 65536 * u16 d (o + 2)

/-- A section header (the fields used here). -/
structure Sec where
  name : Nat
  type : Nat
  flags : Nat
  addr : Nat
  off : Nat
  size : Nat
  link : Nat
  info : Nat
  align : Nat
  deriving Inhabited

/-- A symbol: name (offset in the string table), value, size, info, section index. -/
structure Sym where
  name : Nat
  value : Nat
  size : Nat
  info : Nat
  shndx : Nat
  deriving Inhabited

/-- The zero-terminated string at `o` (at most 4096 bytes). -/
def cstr (d : ByteArray) (o : Nat) : String := Id.run do
  let mut s : List Char := []
  for k in [0:4096] do
    let b := u8 d (o + k)
    if b == 0 then break
    s := Char.ofNat b :: s
  return String.ofList s.reverse

def sections (d : ByteArray) : Except String (Array Sec) := do
  if d.size < 52 then throw "not an ELF file (too short)"
  if u32 d 0 != 0x464C457F then throw "not an ELF file (no magic number)"
  if u8 d 4 != 1 || u8 d 5 != 1 then throw "not a 32-bit little-endian ELF file"
  if u16 d 0x12 != 40 then throw "not an Arm ELF file (e_machine is not EM_ARM)"
  let shoff := u32 d 0x20
  let shentsize := u16 d 0x2E
  let shnum := u16 d 0x30
  if shentsize < 40 then throw "malformed section header table"
  if shoff + shnum * shentsize > d.size then throw "section header table beyond the end of the file"
  let mut out := #[]
  for k in [0:shnum] do
    let o := shoff + k * shentsize
    let s : Sec := ⟨u32 d o, u32 d (o + 4), u32 d (o + 8), u32 d (o + 12), u32 d (o + 16),
      u32 d (o + 20), u32 d (o + 24), u32 d (o + 28), u32 d (o + 32)⟩
    if s.type != 8 && s.size > 0 && s.off + s.size > d.size then
      throw s!"section {k} beyond the end of the file"
    out := out.push s
  return out

def symbols (d : ByteArray) (secs : Array Sec) : Except String (Array Sym × Sec) := do
  let some st := secs.find? (·.type == 2) | throw "no symbol table"
  let some strtab := secs[st.link]? | throw "the symbol table has no string table"
  let mut out := #[]
  for j in [0:st.size / 16] do
    let o := st.off + j * 16
    out := out.push ⟨u32 d o, u32 d (o + 4), u32 d (o + 8), u8 d (o + 12), u16 d (o + 14)⟩
  return (out, strtab)

/-- The image: its base address, its bytes, and the address of every function symbol
(name, address; later entries override earlier ones). -/
structure Image where
  base : Nat
  mem : ByteArray
  funcs : List (String × Nat)

/-- Bytes `[off, off + n)` of the file copied into `mem` at `pos`. -/
def copyInto (d : ByteArray) (off n : Nat) (mem : ByteArray) (pos : Nat) : ByteArray :=
  d.copySlice off mem pos n false

/-- `mem` with zero bytes up to size `n`. -/
def grow (mem : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut m := mem
  for _ in [mem.size:n] do
    m := m.push 0
  return m

def setU16 (m : ByteArray) (o v : Nat) : ByteArray :=
  (m.set! o (UInt8.ofNat (v % 256))).set! (o + 1) (UInt8.ofNat (v / 256 % 256))

def setU32 (m : ByteArray) (o v : Nat) : ByteArray :=
  setU16 (setU16 m o (v % 65536)) (o + 2) (v / 65536 % 65536)

/-- Bit `i` of `x`. -/
def bit (x i : Nat) : Nat := x / 2 ^ i % 2

/-- An executable, as `m0._load_exec`. -/
def loadExec (d : ByteArray) (secs : Array Sec) : Except String Image := do
  let code := secs.toList.filter fun s => s.flags / 2 % 2 == 1 && s.size > 0 && s.addr < 0x20000000
  if code.isEmpty then throw "no allocated section in the code region"
  let base := (code.map (·.addr)).foldl min (code.head!.addr)
  let top := (code.map (fun s => s.addr + s.size)).foldl max 0
  let mut mem := grow ByteArray.empty (top - base + 4)
  for s in code do
    if s.type != 8 then
      mem := copyInto d s.off s.size mem (s.addr - base)
  let (syms, strtab) ← symbols d secs
  let mut funcs := []
  for y in syms do
    if y.name == 0 || y.shndx == 0 || y.shndx ≥ 0xFF00 then continue
    let a := y.value - y.value % 2
    if a < base || a - base ≥ mem.size then continue
    if y.info % 16 == 2 then
      funcs := (cstr d (strtab.off + y.name), a) :: funcs
  return ⟨base, mem, funcs.reverse⟩

/-- A relocatable object, as `m0.load` (without the stack area that follows). -/
def loadRel (d : ByteArray) (secs : Array Sec) : Except String Image := do
  let some shstr := secs[u16 d 0x32]? | throw "no section name table"
  let mut addr : Array (Option Nat) := Array.replicate secs.size none
  let mut pos := 0
  let mut mem := ByteArray.empty
  for k in [0:secs.size] do
    let s := secs[k]!
    if s.flags / 2 % 2 == 0 || (cstr d (shstr.off + s.name)).startsWith ".ARM.exidx" then continue
    let al := max 1 s.align
    pos := (pos + al - 1) / al * al
    addr := addr.set! k (some pos)
    mem := grow mem (pos + s.size)
    if s.type != 8 then
      mem := copyInto d s.off s.size mem pos
    pos := pos + s.size
  let (syms, strtab) ← symbols d secs
  let stub := (mem.size + 15) / 16 * 16
  mem := grow mem (stub + 4096)
  let mut stubs : List String := []
  let mut funcs := []
  for y in syms do
    if y.name == 0 then continue
    match addr[y.shndx]? with
    | some (some p) =>
      if y.info % 16 == 2 then
        funcs := (cstr d (strtab.off + y.name), p + y.value - y.value % 2) :: funcs
    | _ => pure ()
  for k in [0:secs.size] do
    let s := secs[k]!
    if s.type != 9 then continue
    let some (some tgt) := addr[s.info]? | continue
    for j in [0:s.size / 8] do
      let rOff := u32 d (s.off + j * 8)
      let rInfo := u32 d (s.off + j * 8 + 4)
      let rtype := rInfo % 256
      let some y := syms[rInfo / 256]? | throw s!"relocation {j} of section {k}: no symbol {rInfo / 256}"
      let P := tgt + rOff
      -- the symbol's address (`m0.load`, `sym_addr`)
      let mut S := y.value
      if y.shndx == 0 then
        let nm := cstr d (strtab.off + y.name)
        match stubs.idxOf? nm with
        | some i => S := stub + 2 * i
        | none =>
          S := stub + 2 * stubs.length
          stubs := stubs ++ [nm]
      else
        match addr[y.shndx]? with
        | some (some p) => S := p + y.value
        | _ => pure ()
      if P + 4 > mem.size then throw s!"relocation {j} of section {k} beyond the image"
      if rtype == 2 then
        mem := setU32 mem P ((S + u32 mem P) % 2 ^ 32)
      else if rtype == 10 || rtype == 30 then
        let off := (S - S % 2 + 2 ^ 32 - (P + 4)) % 2 ^ 32
        let sg := bit off 24
        let j1 := (1 - bit off 23 + sg) % 2
        let j2 := (1 - bit off 22 + sg) % 2
        mem := setU16 mem P (0xF000 + sg * 1024 + off / 4096 % 1024)
        mem := setU16 mem (P + 2) (0xD000 + j1 * 8192 + j2 * 2048 + off / 2 % 2048)
      else if rtype == 42 then
        pure ()
      else
        throw s!"unsupported relocation type {rtype}"
  return ⟨0, mem, funcs.reverse⟩

def load (d : ByteArray) : Except String Image := do
  let secs ← sections d
  match u16 d 0x10 with
  | 2 => loadExec d secs
  | 1 => loadRel d secs
  | t => throw s!"ELF type {t}: neither an executable nor a relocatable object"

/-- The address of the last function symbol named `n`. -/
def funcAddr (im : Image) (n : String) : Option Nat :=
  (im.funcs.filter (·.1 == n)).getLast?.map (·.2)

/-- The certificate's code (`base`, halfwords) and its functions (name, entry) against the
image: `none` if they agree, else the first difference. -/
def check (im : Image) (base : Nat) (hw : Array Nat) (fns : List (String × Nat)) : Option String := Id.run do
  if base != im.base then
    return some s!"the code starts at {base}, the ELF file's code region at {im.base}"
  if 2 * hw.size > im.mem.size then
    return some s!"the certificate's code ({2 * hw.size} bytes) is longer than the ELF file's image ({im.mem.size} bytes)"
  for i in [0:hw.size] do
    if hw[i]! != u16 im.mem (2 * i) then
      return some s!"the halfword at {base + 2 * i} is {hw[i]!} in the certificate, {u16 im.mem (2 * i)} in the ELF file"
  for (n, e) in fns do
    match funcAddr im n with
    | none => return some s!"no function symbol {n} in the ELF file"
    | some a =>
      if a != e then
        return some s!"function {n}: entry {e} in the certificate, {a} in the ELF file"
  return none

end ImperativeOptimization.Elf
