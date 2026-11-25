# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Cortex-M0 (ARMv6-M) support for the cycle bounds of benchmarks/cycles:

* `decode`: the ARMv6-M Thumb instruction set (16-bit instructions and BL);
* `cycles`: the instruction timings of the Cortex-M0 (zero-wait-state memory), from the
  instruction summary of the Arm Cortex-M0 Technical Reference Manual (revision r0p0, Arm
  DDI 0432C, Table 3-1; `test_m0.py` holds the table and compares); a conditional
  branch costs 3 cycles if taken and 1 if not, MULS `MUL_CYCLES` (32 for the small
  multiplier, the conservative choice; 1 for the fast one);
* `load`: a minimal linker for one relocatable ELF object (R_ARM_ABS32, R_ARM_THM_CALL,
  R_ARM_THM_JUMP24), placing the allocated sections in a flat memory image;
* `Machine`: an interpreter of the instruction set that counts cycles with the same table.

No external package is needed. The interpreter is checked by the programs themselves
(TACLeBench programs return 0 when their result is correct).
"""
import struct

MUL_CYCLES = 32


def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


class Insn:
    __slots__ = ("addr", "size", "op", "a", "kind", "target", "nregs")

    def __init__(self, addr, size, op, a=(), kind="seq", target=None, nregs=0):
        self.addr, self.size, self.op, self.a = addr, size, op, a
        self.kind, self.target, self.nregs = kind, target, nregs

    def __repr__(self):
        return f"{self.addr:#x}:{self.op}{self.a}"


def decode(mem, addr):
    """Decode the instruction at `addr`. `kind`: seq, cond (conditional branch to
    `target`), jump (to `target`), call (BL to `target`), ret (bx lr, pop {..pc}),
    indirect (other writes of the PC), stop (undefined, svc, bkpt, unsupported)."""
    h = struct.unpack_from("<H", mem, addr)[0]
    top5 = h >> 11
    rd, rn = h & 7, (h >> 3) & 7
    if top5 in (0b11101, 0b11110, 0b11111):  # 32-bit
        h2 = struct.unpack_from("<H", mem, addr + 2)[0]
        if top5 == 0b11110 and (h2 >> 14) == 0b11 and (h2 >> 12) & 1:
            s = (h >> 10) & 1
            j1, j2 = (h2 >> 13) & 1, (h2 >> 11) & 1
            i1, i2 = 1 - (j1 ^ s), 1 - (j2 ^ s)
            imm = (s << 24) | (i1 << 23) | (i2 << 22) | ((h & 0x3FF) << 12) | ((h2 & 0x7FF) << 1)
            return Insn(addr, 4, "bl", kind="call", target=addr + 4 + sx(imm, 25))
        return Insn(addr, 4, "unsupported32", kind="stop")
    if top5 <= 0b00010:  # shift immediate
        imm = (h >> 6) & 31
        return Insn(addr, 2, ("lsli", "lsri", "asri")[top5], (rd, rn, imm))
    if top5 == 0b00011:
        rm_imm = (h >> 6) & 7
        opc = (h >> 9) & 3
        return Insn(addr, 2, ("addr", "subr", "addi3", "subi3")[opc], (rd, rn, rm_imm))
    if top5 >> 2 == 0b001:
        r = (h >> 8) & 7
        return Insn(addr, 2, ("movi", "cmpi", "addi8", "subi8")[top5 & 3], (r, h & 0xFF))
    if h >> 10 == 0b010000:
        opc = (h >> 6) & 15
        ops = ("and", "eor", "lslr", "lsrr", "asrr", "adc", "sbc", "ror", "tst", "neg", "cmp",
               "cmn", "orr", "mul", "bic", "mvn")
        return Insn(addr, 2, ops[opc], (rd, rn))
    if h >> 10 == 0b010001:
        opc = (h >> 8) & 3
        rm = (h >> 3) & 15
        d = ((h >> 4) & 8) | (h & 7)
        if opc == 3:
            if (h >> 7) & 1:
                return Insn(addr, 2, "blx", (rm,), kind="indirect")
            if rm == 14:
                return Insn(addr, 2, "bx", (rm,), kind="ret")
            return Insn(addr, 2, "bx", (rm,), kind="indirect")
        op = ("addhi", "cmphi", "movhi")[opc]
        k = "indirect" if d == 15 and op != "cmphi" else "seq"
        return Insn(addr, 2, op, (d, rm), kind=k)
    if top5 == 0b01001:
        return Insn(addr, 2, "ldrlit", ((h >> 8) & 7, (h & 0xFF) * 4))
    if h >> 12 == 0b0101:
        opc = (h >> 9) & 7
        ops = ("strr", "strhr", "strbr", "ldrsbr", "ldrr", "ldrhr", "ldrbr", "ldrshr")
        return Insn(addr, 2, ops[opc], (rd, rn, (h >> 6) & 7))
    if h >> 13 == 0b011:
        b, l = (h >> 12) & 1, (h >> 11) & 1
        imm = (h >> 6) & 31
        op = ("str", "ldr", "strb", "ldrb")[b * 2 + l]
        return Insn(addr, 2, op + "i", (rd, rn, imm if b else imm * 4))
    if h >> 12 == 0b1000:
        l = (h >> 11) & 1
        return Insn(addr, 2, ("strhi", "ldrhi")[l], (rd, rn, ((h >> 6) & 31) * 2))
    if h >> 12 == 0b1001:
        l = (h >> 11) & 1
        return Insn(addr, 2, ("strsp", "ldrsp")[l], ((h >> 8) & 7, (h & 0xFF) * 4))
    if top5 == 0b10100:
        return Insn(addr, 2, "adr", ((h >> 8) & 7, (h & 0xFF) * 4))
    if top5 == 0b10101:
        return Insn(addr, 2, "addspi", ((h >> 8) & 7, (h & 0xFF) * 4))
    if h >> 12 == 0b1011:
        if h >> 8 == 0b10110000:
            imm = (h & 0x7F) * 4
            return Insn(addr, 2, "subsp" if (h >> 7) & 1 else "addsp", (imm,))
        if h >> 8 == 0b10110010:
            return Insn(addr, 2, ("sxth", "sxtb", "uxth", "uxtb")[(h >> 6) & 3], (rd, rn))
        if h >> 9 == 0b1011010:
            regs = [i for i in range(8) if (h >> i) & 1] + ([14] if (h >> 8) & 1 else [])
            return Insn(addr, 2, "push", (regs,), nregs=len(regs))
        if h >> 9 == 0b1011110:
            pc = (h >> 8) & 1
            regs = [i for i in range(8) if (h >> i) & 1] + ([15] if pc else [])
            return Insn(addr, 2, "pop", (regs,), kind="ret" if pc else "seq", nregs=len(regs))
        if h >> 8 == 0b10111010:
            opc = (h >> 6) & 3
            if opc == 2:
                return Insn(addr, 2, "undef", kind="stop")
            return Insn(addr, 2, ("rev", "rev16", "", "revsh")[opc], (rd, rn))
        if h in (0xBF00, 0xBF10, 0xBF40):  # NOP, YIELD (executes as NOP), SEV: 1 cycle
            return Insn(addr, 2, "nop")
        # WFE and WFI (2 cycles plus the time spent waiting) have no cycle bound: stop.
        return Insn(addr, 2, "misc", kind="stop")
    if h >> 12 == 0b1100:
        l = (h >> 11) & 1
        rn8 = (h >> 8) & 7
        regs = [i for i in range(8) if (h >> i) & 1]
        return Insn(addr, 2, ("stm", "ldm")[l], (rn8, regs), nregs=len(regs))
    if h >> 12 == 0b1101:
        cond = (h >> 8) & 15
        if cond >= 14:
            return Insn(addr, 2, "svc", kind="stop")
        return Insn(addr, 2, "bcond", (cond,), kind="cond", target=addr + 4 + sx(h & 0xFF, 8) * 2)
    if top5 == 0b11100:
        return Insn(addr, 2, "b", kind="jump", target=addr + 4 + sx(h & 0x7FF, 11) * 2)
    return Insn(addr, 2, "unknown", kind="stop")


def cycles(i, taken=True):
    """Cycles of an instruction on the Cortex-M0 (worst case for a conditional branch if
    `taken`)."""
    op = i.op
    if op == "bcond":
        return 3 if taken else 1
    if op == "b":
        return 3
    if op == "bl":
        return 4
    if op in ("bx", "blx"):
        return 3
    if op in ("addhi", "movhi") and i.a[0] == 15:
        return 3
    if op == "mul":
        return MUL_CYCLES
    if op in ("push", "stm", "ldm"):
        return 1 + i.nregs
    if op == "pop":
        # 4 + N with the PC, where N counts the PC (note c of Table 3-1 of the manual)
        return 4 + i.nregs if 15 in i.a[0] else 1 + i.nregs
    if op.startswith("ldr") or op.startswith("str"):
        return 2
    return 1


# --- the most frequent instructions, without the dispatch of `Machine.execute` ----------
# Each handler is the branch of `execute` for its operation, unchanged (`call` uses it in
# place of `execute`; the others, and those that read the PC, go through `execute`).

def _mem_access(kind):
    def h(m, a, reg):
        t, n, x = a
        ad = ((m.r[n] + m.r[x]) if reg else (m.r[n] + x)) & 0xFFFFFFFF
        m.access(kind, t, ad)
    return h


def _f_addc(sub, imm, two):
    def h(m, a):
        r = m.r
        if two:     # rd = rd op imm8
            x, y, d = r[a[0]], a[1], a[0]
        else:
            d, x = a[0], r[a[1]]
            y = a[2] if imm else r[a[2]]
        r[d] = m.addc(x, ~y & 0xFFFFFFFF, 1) if sub else m.addc(x, y, 0)
    return h


def _f_lsli(m, a):
    d, x, imm = a
    v = m.r[x]
    if imm:
        m.c = (v >> (32 - imm)) & 1
        v = (v << imm) & 0xFFFFFFFF
    m.r[d] = m.nz(v)


def _f_lsri(m, a):
    d, x, imm = a
    imm = imm or 32
    v = m.r[x]
    m.c = (v >> (imm - 1)) & 1
    m.r[d] = m.nz(v >> imm if imm < 32 else 0)


def _f_movi(m, a):
    m.r[a[0]] = m.nz(a[1])


def _f_cmpi(m, a):
    m.addc(m.r[a[0]], ~a[1] & 0xFFFFFFFF, 1)


def _f_cmp(m, a):
    m.addc(m.r[a[0]], ~m.r[a[1]] & 0xFFFFFFFF, 1)


def _f_logic(op):
    def h(m, a):
        r = m.r
        d, x = a
        u, v = r[d], r[x]
        if op == "and" or op == "tst":
            w = u & v
        elif op == "eor":
            w = u ^ v
        elif op == "orr":
            w = u | v
        elif op == "bic":
            w = u & ~v & 0xFFFFFFFF
        elif op == "mvn":
            w = ~v & 0xFFFFFFFF
        else:   # mul
            w = (u * v) & 0xFFFFFFFF
        w = m.nz(w)
        if op != "tst":
            r[d] = w
    return h


def _f_addspi(m, a):
    m.r[a[0]] = m.r[13] + a[1]


def _f_ldrsp(m, a):
    m.r[a[0]] = m.rd32(m.r[13] + a[1])


def _f_strsp(m, a):
    m.wr32(m.r[13] + a[1], m.r[a[0]])


def _f_uxtb(m, a):
    m.r[a[0]] = m.r[a[1]] & 0xFF


def _f_uxth(m, a):
    m.r[a[0]] = m.r[a[1]] & 0xFFFF


FAST = {"lsli": _f_lsli, "lsri": _f_lsri, "movi": _f_movi, "cmpi": _f_cmpi, "cmp": _f_cmp,
        "addr": _f_addc(False, False, False), "subr": _f_addc(True, False, False),
        "addi3": _f_addc(False, True, False), "subi3": _f_addc(True, True, False),
        "addi8": _f_addc(False, True, True), "subi8": _f_addc(True, True, True),
        "addspi": _f_addspi, "ldrsp": _f_ldrsp, "strsp": _f_strsp,
        "uxtb": _f_uxtb, "uxth": _f_uxth}
for _op in ("and", "eor", "orr", "bic", "mvn", "tst", "mul"):
    FAST[_op] = _f_logic(_op)
for _k in ("str", "strh", "strb", "ldr", "ldrh", "ldrb", "ldrsh", "ldrsb"):
    FAST[_k + "i"] = (lambda h: lambda m, a: h(m, a, False))(_mem_access(_k))
    FAST[_k + "r"] = (lambda h: lambda m, a: h(m, a, True))(_mem_access(_k))
del _op, _k


# --- ELF loading --------------------------------------------------------------------------

class Image:
    def __init__(self):
        self.mem = bytearray()
        self.symbols = {}      # name -> address (defined)
        self.funcs = {}        # name -> (address, size)
        self.undefined = {}    # address of a stub -> name (calls of undefined functions)
        self.base = 0          # address of mem[0] (executables: the lowest code address)


def load(path, base=0, ram=1 << 22):
    """Link one relocatable object into a flat image: allocated sections in file order from
    `base` (`img.ro_top`: the end of the read-only sections before the first writable one:
    the code and the constant tables that follow it, as `ld -r` with a run-time library
    places them), then `ram` bytes of stack. Undefined functions get stub addresses (calls
    to them stop the interpreter)."""
    with open(path, "rb") as f:
        data = f.read()
    if struct.unpack_from("<H", data, 0x10)[0] == 2:
        return _load_exec(data)
    (e_shoff,) = struct.unpack_from("<I", data, 0x20)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 0x2E)
    secs = []
    for k in range(e_shnum):
        secs.append(struct.unpack_from("<IIIIIIIIII", data, e_shoff + k * e_shentsize))
    shstr = secs[e_shstrndx]

    def name_at(tab, off):
        start = tab[4] + off
        return data[start:data.index(b"\0", start)].decode()

    names = [name_at(shstr, s[0]) for s in secs]
    img = Image()
    addr = {}
    pos = base
    img.ro_top = None
    for k, s in enumerate(secs):
        sh_type, sh_flags, sh_size, sh_align = s[1], s[2], s[5], max(1, s[8])
        if not (sh_flags & 2) or names[k].startswith(".ARM.exidx"):
            continue
        if sh_flags & 1 and img.ro_top is None:      # SHF_WRITE: the end of the read-only part
            img.ro_top = pos
        pos = (pos + sh_align - 1) // sh_align * sh_align
        addr[k] = pos
        if len(img.mem) < pos + sh_size:
            img.mem.extend(b"\0" * (pos + sh_size - len(img.mem)))
        if sh_type != 8:  # not NOBITS
            img.mem[pos:pos + sh_size] = data[s[4]:s[4] + sh_size]
        pos += sh_size
    if img.ro_top is None:
        img.ro_top = pos
    symtab = next(k for k, s in enumerate(secs) if s[1] == 2)
    strtab = secs[secs[symtab][6]]
    syms = []
    st = secs[symtab]
    for j in range(st[5] // 16):
        st_name, st_value, st_size, st_info, _, st_shndx = struct.unpack_from("<IIIBBH", data, st[4] + j * 16)
        nm = name_at(strtab, st_name) if st_name else ""
        syms.append((nm, st_value, st_size, st_info, st_shndx))
    stub = (len(img.mem) + 15) // 16 * 16
    img.mem.extend(b"\0" * (stub - len(img.mem) + 4096))
    stubs = {}

    def sym_addr(j):
        nm, val, size, info, shndx = syms[j]
        if shndx == 0:
            if nm not in stubs:
                stubs[nm] = stub + 2 * len(stubs)
                img.undefined[stubs[nm]] = nm
            return stubs[nm]
        if shndx in addr:
            return addr[shndx] + val
        return val

    for j, (nm, val, size, info, shndx) in enumerate(syms):
        if shndx in addr and nm:
            a = addr[shndx] + (val & ~1)
            img.symbols[nm] = a
            if info & 15 == 2:
                img.funcs[nm] = (a, size)
    for k, s in enumerate(secs):
        if s[1] != 9 or s[7] not in addr:  # SHT_REL for an allocated section
            continue
        tgt = addr[s[7]]
        for j in range(s[5] // 8):
            r_off, r_info = struct.unpack_from("<II", data, s[4] + j * 8)
            rtype, rsym = r_info & 0xFF, r_info >> 8
            P = tgt + r_off
            S = sym_addr(rsym)
            if rtype == 2:  # R_ARM_ABS32
                A = struct.unpack_from("<I", img.mem, P)[0]
                struct.pack_into("<I", img.mem, P, (S + A) & 0xFFFFFFFF)
            elif rtype in (10, 30):  # R_ARM_THM_CALL, R_ARM_THM_JUMP24 (BL)
                off = (S & ~1) - (P + 4)
                s_ = (off >> 24) & 1
                i1, i2 = (off >> 23) & 1, (off >> 22) & 1
                j1, j2 = (1 - i1) ^ s_, (1 - i2) ^ s_
                hi = 0xF000 | (s_ << 10) | ((off >> 12) & 0x3FF)
                lo = 0xD000 | (j1 << 13) | (j2 << 11) | ((off >> 1) & 0x7FF)
                struct.pack_into("<HH", img.mem, P, hi, lo)
            elif rtype == 42:  # R_ARM_PREL31 (unwind tables): ignored
                pass
            else:
                raise ValueError(f"unsupported relocation type {rtype} in {names[k]}")
    img.stack_top = len(img.mem) + ram
    img.mem.extend(b"\0" * ram)
    return img


def _load_exec(data):
    """A linked executable (ET_EXEC), for static analysis only: the allocated sections of
    the code region (addresses below 0x20000000 in the ARMv6-M/ARMv7-M memory map) are
    placed at their addresses minus the lowest one, `img.base` (the code is position
    independent for decoding: branches and literal loads are relative to the PC); no stack,
    no data in RAM, so the interpreter cannot run it."""
    (e_shoff,) = struct.unpack_from("<I", data, 0x20)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 0x2E)
    secs = [struct.unpack_from("<IIIIIIIIII", data, e_shoff + k * e_shentsize) for k in range(e_shnum)]
    code = [s for s in secs if (s[2] & 2) and s[5] and s[3] < 0x20000000]
    if not code:
        raise ValueError("no allocated section in the code region")
    img = Image()
    img.base = min(s[3] for s in code)
    img.mem = bytearray(max(s[3] + s[5] for s in code) - img.base + 4)
    for s in code:
        if s[1] != 8:  # not NOBITS
            img.mem[s[3] - img.base:s[3] - img.base + s[5]] = data[s[4]:s[4] + s[5]]
    symtab = next(k for k, s in enumerate(secs) if s[1] == 2)
    st, strtab = secs[symtab], secs[secs[symtab][6]]
    for j in range(st[5] // 16):
        st_name, st_value, st_size, st_info, _, st_shndx = struct.unpack_from("<IIIBBH", data, st[4] + j * 16)
        if not st_name or st_shndx == 0 or st_shndx >= 0xFF00:
            continue
        start = strtab[4] + st_name
        nm = data[start:data.index(b"\0", start)].decode()
        a = (st_value & ~1) - img.base
        if not 0 <= a < len(img.mem):
            continue
        img.symbols[nm] = a
        if st_info & 15 == 2:
            img.funcs[nm] = (a, st_size)
    img.stack_top = None
    return img


# --- interpreter --------------------------------------------------------------------------

class Stop(Exception):
    pass


def _f(u):
    return struct.unpack("<f", struct.pack("<I", u & 0xFFFFFFFF))[0]


def _uf(x):
    try:
        return struct.unpack("<I", struct.pack("<f", x))[0]
    except OverflowError:
        return 0x7F800000 if x > 0 else 0xFF800000


def _d(lo, hi):
    return struct.unpack("<d", struct.pack("<II", lo, hi))[0]


def _ud(x):
    return struct.unpack("<II", struct.pack("<d", x))


def _trunc(x, lo, hi):
    if x != x:
        return 0
    return int(max(lo, min(hi, int(x))))


def _div(a, b):  # C division (truncation)
    if b == 0:
        return 0, 0
    q = abs(a) // abs(b) * (1 if (a >= 0) == (b >= 0) else -1)
    return q, a - q * b


def helper(name, r, mem):
    """Run-time support functions without code in the object (division, floating point,
    memory), executed natively so that programs can run. They take no cycles here: a
    function that calls one has no static bound, so its observed cycles are not compared."""
    M = 0xFFFFFFFF
    u = lambda k: r[k]
    s32 = lambda k: sx(r[k], 32)
    u64 = lambda k: r[k] | (r[k + 1] << 32)
    s64 = lambda k: sx(u64(k), 64)

    def set64(v):
        v &= (1 << 64) - 1
        r[0], r[1] = v & M, v >> 32

    def setd(x):
        r[0], r[1] = _ud(x)

    D = lambda k: _d(r[k], r[k + 1])
    F = lambda k: _f(r[k])
    if name in ("__aeabi_idiv", "__aeabi_idivmod"):
        q, m = _div(s32(0), s32(1)); r[0], r[1] = q & M, m & M
    elif name in ("__aeabi_uidiv", "__aeabi_uidivmod"):
        b = u(1); q, m = (u(0) // b, u(0) % b) if b else (0, 0); r[0], r[1] = q, m
    elif name == "__aeabi_ldivmod":
        q, m = _div(s64(0), s64(2)); set64(q); r[2], r[3] = m & M, (m >> 32) & M
    elif name == "__aeabi_uldivmod":
        b = u64(2); q, m = (u64(0) // b, u64(0) % b) if b else (0, 0)
        set64(q); r[2], r[3] = m & M, m >> 32
    elif name == "__aeabi_lmul":
        set64(u64(0) * u64(2))
    elif name == "__aeabi_llsl":
        set64(u64(0) << (r[2] & 63))
    elif name == "__aeabi_llsr":
        set64(u64(0) >> (r[2] & 63))
    elif name == "__aeabi_lasr":
        set64(s64(0) >> (r[2] & 63))
    elif name in ("__aeabi_fadd", "__aeabi_fsub", "__aeabi_frsub", "__aeabi_fmul", "__aeabi_fdiv"):
        x, y = F(0), F(1)
        try:
            v = {"__aeabi_fadd": x + y, "__aeabi_fsub": x - y, "__aeabi_frsub": y - x,
                 "__aeabi_fmul": x * y, "__aeabi_fdiv": x / y if y else (float("inf") if x > 0 else float("-inf") if x < 0 else float("nan"))}[name]
        except OverflowError:
            v = float("inf")
        r[0] = _uf(v)
    elif name in ("__aeabi_dadd", "__aeabi_dsub", "__aeabi_drsub", "__aeabi_dmul", "__aeabi_ddiv"):
        x, y = D(0), D(2)
        try:
            v = {"__aeabi_dadd": x + y, "__aeabi_dsub": x - y, "__aeabi_drsub": y - x,
                 "__aeabi_dmul": x * y, "__aeabi_ddiv": x / y if y else (float("inf") if x > 0 else float("-inf") if x < 0 else float("nan"))}[name]
        except OverflowError:
            v = float("inf")
        setd(v)
    elif name.startswith("__aeabi_fcmp") or name.startswith("__aeabi_dcmp"):
        x, y = (F(0), F(1)) if "fcmp" in name else (D(0), D(2))
        op = name[-2:]
        r[0] = int({"eq": x == y, "lt": x < y, "le": x <= y, "ge": x >= y, "gt": x > y, "un": x != x or y != y}[op])
    elif name in ("__aeabi_f2iz", "__aeabi_d2iz"):
        r[0] = _trunc(F(0) if "f2" in name else D(0), -2**31, 2**31 - 1) & M
    elif name in ("__aeabi_f2uiz", "__aeabi_d2uiz"):
        r[0] = _trunc(F(0) if "f2" in name else D(0), 0, M)
    elif name in ("__aeabi_d2lz", "__aeabi_f2lz"):
        set64(_trunc(D(0) if "d2" in name else F(0), -2**63, 2**63 - 1))
    elif name == "__aeabi_i2f":
        r[0] = _uf(float(s32(0)))
    elif name == "__aeabi_ui2f":
        r[0] = _uf(float(u(0)))
    elif name == "__aeabi_i2d":
        setd(float(s32(0)))
    elif name == "__aeabi_ui2d":
        setd(float(u(0)))
    elif name == "__aeabi_l2d":
        setd(float(s64(0)))
    elif name == "__aeabi_l2f":
        r[0] = _uf(float(s64(0)))
    elif name == "__aeabi_f2d":
        setd(F(0))
    elif name == "__aeabi_d2f":
        r[0] = _uf(D(0))
    elif name in ("memset", "__aeabi_memset", "__aeabi_memset4", "__aeabi_memset8"):
        d, n, c = (r[0], r[2], r[1]) if name == "memset" else (r[0], r[1], r[2])
        mem[d:d + n] = bytes([c & 0xFF]) * n
    elif name in ("__aeabi_memclr", "__aeabi_memclr4", "__aeabi_memclr8"):
        mem[r[0]:r[0] + r[1]] = bytes(r[1])
    elif name in ("memcpy", "memmove", "__aeabi_memcpy", "__aeabi_memcpy4", "__aeabi_memcpy8",
                  "__aeabi_memmove", "__aeabi_memmove4", "__aeabi_memmove8"):
        d, s_, n = r[0], r[1], r[2]
        mem[d:d + n] = bytes(mem[s_:s_ + n])
    else:
        return False
    return True


class Machine:
    """Executes the image from a function until it returns; counts cycles."""

    HALT = 0xFFFFFFF0

    def __init__(self, img):
        self.img, self.mem = img, img.mem
        self.r = [0] * 16
        self.n = self.z = self.c = self.v = 0
        self.cyc = 0
        self.cache = {}
        self.timed = {}
        self.on_insn = None   # callback(insn, cycles_before)

    def rd32(self, a):
        return struct.unpack_from("<I", self.mem, a)[0]

    def wr32(self, a, v):
        struct.pack_into("<I", self.mem, a, v & 0xFFFFFFFF)

    def nz(self, v):
        v &= 0xFFFFFFFF
        self.n, self.z = v >> 31, int(v == 0)
        return v

    def addc(self, a, b, carry):
        u = a + b + carry
        res = u & 0xFFFFFFFF
        self.c = int(u > 0xFFFFFFFF)
        self.v = int(((a ^ res) & (b ^ res)) >> 31 & 1)
        return self.nz(res)

    def cond(self, c):
        n, z, cc, v = self.n, self.z, self.c, self.v
        return [z, not z, cc, not cc, n, not n, v, not v, cc and not z, not cc or z,
                n == v, n != v, not z and n == v, z or n != v][c]

    def call(self, fn, args=(), max_cycles=10**10, watch=None):
        """Runs `fn` until it returns; its result (r0). `watch` (a `Watch`): the observations
        of the run, made by the C core (`m0core.c`) when it is available and `on_insn` is
        not set, else by `Watch.step` as an `on_insn` callback."""
        r = self.r
        for k, a in enumerate(args):
            r[k] = a
        r[13] = self.img.stack_top
        r[14] = self.HALT | 1
        pc = self.img.funcs[fn][0]
        if watch is not None and self.on_insn is None:
            lib = core()
            if lib is not None:
                return _run_core(self, lib, pc, max_cycles, watch)
            self.on_insn = watch.bind(self)
            try:
                return self._loop(pc, max_cycles)
            finally:
                self.on_insn = None
        if watch is not None:
            raise ValueError("a Watch and an on_insn callback together")
        return self._loop(pc, max_cycles)

    def _loop(self, pc, max_cycles):
        while pc != self.HALT:
            pc = self._step(pc, max_cycles)
        return self.r[0]

    def _step(self, pc, max_cycles):
        """Executes the instruction at `pc` (or the function without code at `pc`), counts
        its cycles, calls `on_insn`; the next PC."""
        r, mem, on_insn = self.r, self.mem, self.on_insn
        undefined = self.img.undefined
        if pc in undefined:
            name = undefined[pc]
            if not helper(name, r, mem):
                raise Stop(f"call to the undefined function {name}")
            if on_insn:
                on_insn(None, self.cyc, r[14] & ~1)
            return r[14] & ~1
        # pc -> (instruction, cycles if taken, cycles if not), decoded once
        tm = self.timed.get(pc)
        if tm is None:
            i = self.cache.get(pc)
            if i is None:
                i = self.cache[pc] = decode(mem, pc)
            tm = self.timed[pc] = (i, cycles(i, True), cycles(i, False))
        i = tm[0]
        before = self.cyc
        nxt = pc + i.size
        op, a = i.op, i.a
        taken = True
        if op == "bcond":
            taken = bool(self.cond(a[0]))
            if taken:
                nxt = i.target
        elif op == "b":
            nxt = i.target
        elif op == "bl":
            r[14] = (pc + 4) | 1
            nxt = i.target
        elif op == "bx" or op == "blx":
            t = r[a[0]]
            if op == "blx":
                r[14] = (pc + 2) | 1
            nxt = t & ~1
        elif op == "push":
            regs = a[0]
            sp = r[13] - 4 * len(regs)
            for k, reg in enumerate(regs):
                self.wr32(sp + 4 * k, r[reg])
            r[13] = sp
        elif op == "pop":
            sp = r[13]
            for k, reg in enumerate(a[0]):
                val = self.rd32(sp + 4 * k)
                if reg == 15:
                    nxt = val & ~1
                else:
                    r[reg] = val
            r[13] = sp + 4 * len(a[0])
        else:
            h = FAST.get(op)
            if h is not None:
                h(self, a)
            else:
                self.execute(i, pc)
                if (op in ("addhi", "movhi")) and a[0] == 15:
                    nxt = r[15] & ~1
        self.cyc += tm[1] if taken else tm[2]
        if on_insn:
            on_insn(i, before, nxt)
        if self.cyc > max_cycles:
            raise Stop("cycle limit")
        return nxt

    def execute(self, i, pc):
        r, op, a = self.r, i.op, i.a
        M = 0xFFFFFFFF
        if op == "lsli":
            d, m, imm = a
            v = r[m]
            if imm:
                self.c = (v >> (32 - imm)) & 1
                v = (v << imm) & M
            r[d] = self.nz(v)
        elif op == "lsri":
            d, m, imm = a
            imm = imm or 32
            v = r[m]
            self.c = (v >> (imm - 1)) & 1
            r[d] = self.nz(v >> imm if imm < 32 else 0)
        elif op == "asri":
            d, m, imm = a
            imm = imm or 32
            v = sx(r[m], 32)
            self.c = (v >> (imm - 1)) & 1
            r[d] = self.nz(v >> imm if imm < 32 else (M if v < 0 else 0))
        elif op == "addr":
            r[a[0]] = self.addc(r[a[1]], r[a[2]], 0)
        elif op == "subr":
            r[a[0]] = self.addc(r[a[1]], ~r[a[2]] & M, 1)
        elif op == "addi3":
            r[a[0]] = self.addc(r[a[1]], a[2], 0)
        elif op == "subi3":
            r[a[0]] = self.addc(r[a[1]], ~a[2] & M, 1)
        elif op == "movi":
            r[a[0]] = self.nz(a[1])
        elif op == "cmpi":
            self.addc(r[a[0]], ~a[1] & M, 1)
        elif op == "addi8":
            r[a[0]] = self.addc(r[a[0]], a[1], 0)
        elif op == "subi8":
            r[a[0]] = self.addc(r[a[0]], ~a[1] & M, 1)
        elif op in ("and", "eor", "orr", "bic", "mvn", "tst", "mul"):
            d, m = a
            x, y = r[d], r[m]
            v = {"and": x & y, "tst": x & y, "eor": x ^ y, "orr": x | y, "bic": x & ~y & M,
                 "mvn": ~y & M, "mul": (x * y) & M}[op]
            v = self.nz(v)
            if op != "tst":
                r[d] = v
        elif op in ("lslr", "lsrr", "asrr", "ror"):
            d, m = a
            s = r[m] & 0xFF
            v = r[d]
            if op == "lslr":
                if s == 0:
                    pass
                elif s < 32:
                    self.c = (v >> (32 - s)) & 1
                    v = (v << s) & M
                elif s == 32:
                    self.c, v = v & 1, 0
                else:
                    self.c, v = 0, 0
            elif op == "lsrr":
                if s == 0:
                    pass
                elif s < 32:
                    self.c = (v >> (s - 1)) & 1
                    v >>= s
                elif s == 32:
                    self.c, v = v >> 31, 0
                else:
                    self.c, v = 0, 0
            elif op == "asrr":
                sv = sx(v, 32)
                if s == 0:
                    pass
                elif s < 32:
                    self.c = (sv >> (s - 1)) & 1
                    v = (sv >> s) & M
                else:
                    self.c = (sv >> 31) & 1
                    v = M if sv < 0 else 0
            else:
                if s:
                    k = s & 31
                    if k:
                        v = ((v >> k) | (v << (32 - k))) & M
                    self.c = v >> 31
            r[d] = self.nz(v)
        elif op == "adc":
            r[a[0]] = self.addc(r[a[0]], r[a[1]], self.c)
        elif op == "sbc":
            r[a[0]] = self.addc(r[a[0]], ~r[a[1]] & M, self.c)
        elif op == "neg":
            r[a[0]] = self.addc(0, ~r[a[1]] & M, 1)
        elif op == "cmp":
            self.addc(r[a[0]], ~r[a[1]] & M, 1)
        elif op == "cmn":
            self.addc(r[a[0]], r[a[1]], 0)
        elif op in ("addhi", "movhi", "cmphi"):
            d, m = a
            vm = (pc + 4) if m == 15 else r[m]
            vd = (pc + 4) if d == 15 else r[d]
            if op == "addhi":
                r[d] = (vd + vm) & M
            elif op == "movhi":
                r[d] = vm
            else:
                self.addc(vd, ~vm & M, 1)
        elif op == "ldrlit":
            r[a[0]] = self.rd32(((pc + 4) & ~3) + a[1])
        elif op == "adr":
            r[a[0]] = ((pc + 4) & ~3) + a[1]
        elif op == "addspi":
            r[a[0]] = r[13] + a[1]
        elif op == "addsp":
            r[13] += a[0]
        elif op == "subsp":
            r[13] -= a[0]
        elif op in ("strsp", "ldrsp"):
            ad = r[13] + a[1]
            if op == "strsp":
                self.wr32(ad, r[a[0]])
            else:
                r[a[0]] = self.rd32(ad)
        elif op.endswith("r") and op[:3] in ("str", "ldr"):  # register offset
            t, n, m = a
            self.access(op[:-1], t, (r[n] + r[m]) & M)
        elif op.endswith("i") and op[:3] in ("str", "ldr"):  # immediate offset
            t, n, imm = a
            self.access(op[:-1], t, (r[n] + imm) & M)
        elif op in ("sxth", "sxtb", "uxth", "uxtb"):
            d, m = a
            v = r[m]
            r[d] = {"sxth": sx(v, 16) & M, "sxtb": sx(v, 8) & M, "uxth": v & 0xFFFF, "uxtb": v & 0xFF}[op]
        elif op in ("rev", "rev16", "revsh"):
            d, m = a
            v = r[m]
            b = v.to_bytes(4, "little")
            if op == "rev":
                r[d] = int.from_bytes(b, "big")
            elif op == "rev16":
                r[d] = (b[1] | (b[0] << 8)) | ((b[3] | (b[2] << 8)) << 16)
            else:
                r[d] = sx(b[1] | (b[0] << 8), 16) & M
        elif op == "stm":
            n, regs = a
            ad = r[n]
            for k, reg in enumerate(regs):
                self.wr32(ad + 4 * k, r[reg])
            r[n] = ad + 4 * len(regs)
        elif op == "ldm":
            n, regs = a
            ad = r[n]
            for k, reg in enumerate(regs):
                r[reg] = self.rd32(ad + 4 * k)
            if n not in regs:
                r[n] = ad + 4 * len(regs)
        elif op == "nop":
            pass
        else:
            raise Stop(f"unsupported instruction {op} at {pc:#x}")

    def access(self, kind, t, ad):
        r, mem = self.r, self.mem
        if ad >= len(mem):
            raise Stop(f"access outside memory at {ad:#x}")
        if kind == "str":
            self.wr32(ad, r[t])
        elif kind == "strh":
            struct.pack_into("<H", mem, ad, r[t] & 0xFFFF)
        elif kind == "strb":
            mem[ad] = r[t] & 0xFF
        elif kind == "ldr":
            r[t] = self.rd32(ad)
        elif kind == "ldrh":
            r[t] = struct.unpack_from("<H", mem, ad)[0]
        elif kind == "ldrb":
            r[t] = mem[ad]
        elif kind == "ldrsh":
            r[t] = sx(struct.unpack_from("<H", mem, ad)[0], 16) & 0xFFFFFFFF
        elif kind == "ldrsb":
            r[t] = sx(mem[ad], 8) & 0xFFFFFFFF
        else:
            raise Stop(f"unknown access {kind}")


# --- the observations of a run, and the C core ---------------------------------------------

class Watch:
    """What run_cycles.py observes during a run: the cycles of the longest call of each
    function (`observed`), the bytes of stack of its deepest activation (`sobserved`), and
    the back edges of each loop against its bound (`worst_loop`, `viol`); `frames`: the
    stack pointer at the entry of each activation in progress and the lowest one seen since
    (the first is the run's). `entry`: {address: function}; `bodies`, `cbodies`: {header:
    (body, bound, function)} (bounds of the schema, certified bounds)."""

    def __init__(self, entry, bodies, cbodies, stack_top):
        self.entry, self.bodies, self.cbodies = entry, bodies, cbodies
        self.observed, self.sobserved, self.worst_loop = {}, {}, {}
        self.viol = []
        self.frames = [[stack_top, stack_top]]
        self.stack, self.count, self.ccount = [], {}, {}

    def bind(self, mach):
        """The `on_insn` callback of `mach` that makes the observations (`step`)."""
        return lambda i, before, nxt: self.step(mach, i, nxt)

    def step(self, mach, i, nxt):
        frames, stack = self.frames, self.stack
        sp = mach.r[13]
        if frames and sp < frames[-1][1]:
            frames[-1][1] = sp
        if i is not None and i.kind == "call":
            stack.append((self.entry.get(i.target), mach.cyc, i.addr + 4))
            frames.append([sp, sp])
        elif stack and nxt == stack[-1][2] and (i is None or i.kind == "ret"):
            fn, start, _ = stack.pop()
            at_entry, low = frames.pop()
            if frames and low < frames[-1][1]:
                frames[-1][1] = low
            if fn is not None:
                self.observed[fn] = max(self.observed.get(fn, 0), mach.cyc - start)
                self.sobserved[fn] = max(self.sobserved.get(fn, 0), at_entry - low)
        if i is None:
            return
        for loops, count, what in ((self.bodies, self.count, "bound"),
                                   (self.cbodies, self.ccount, "certified bound")):
            if nxt in loops:
                body, N, fn = loops[nxt]
                if i.addr in body:
                    count[nxt] = count.get(nxt, 0) + 1
                    if count[nxt] > N:
                        self.viol.append(f"loop {nxt:#x} of {fn}: {count[nxt]} back edges > {what} {N}")
                    if loops is self.bodies:
                        self.worst_loop[nxt] = max(self.worst_loop.get(nxt, 0), count[nxt])
                else:
                    count[nxt] = 0


_CORE = []      # [the library or None], loaded once


def core():
    """The C core (`m0core.c`, built with the C compiler `$CC` or `cc` into `.build/` when
    needed), or None. `CROSSCHECK_M0_CORE=python` disables it; `=c` requires it."""
    if _CORE:
        return _CORE[0]
    import ctypes
    import hashlib
    import os
    import pathlib
    import subprocess
    import tempfile
    mode = os.environ.get("CROSSCHECK_M0_CORE", "auto")
    lib = None
    if mode != "python":
        here = pathlib.Path(__file__).resolve().parent
        src = here / "m0core.c"
        try:
            tag = hashlib.sha256(src.read_bytes()).hexdigest()[:12]
            so = here / ".build" / f"m0core-{tag}.so"
            if not so.exists():
                so.parent.mkdir(exist_ok=True)
                fd, tmp = tempfile.mkstemp(suffix=".so", dir=so.parent)
                os.close(fd)
                try:
                    subprocess.run([os.environ.get("CC", "cc"), "-O2", "-shared", "-fPIC", str(src),
                                    "-o", tmp], check=True, capture_output=True)
                    os.replace(tmp, so)     # atomic: processes building it at once
                finally:
                    if os.path.exists(tmp):
                        os.unlink(tmp)
            lib = ctypes.CDLL(str(so))
            _declare(lib)
        except (OSError, subprocess.CalledProcessError):
            if mode == "c":
                raise
            lib = None
    _CORE.append(lib)
    return lib


def _declare(lib):
    import ctypes as C
    P = C.POINTER

    class M0(C.Structure):
        _fields_ = [("r", C.c_uint32 * 16), ("n", C.c_uint32), ("z", C.c_uint32), ("c", C.c_uint32),
                    ("v", C.c_uint32), ("cyc", C.c_uint64), ("max_cycles", C.c_uint64),
                    ("pc", C.c_uint32), ("mem", P(C.c_uint8)), ("mem_len", C.c_uint64),
                    ("lo", C.c_uint32), ("hi", C.c_uint32),
                    ("op", P(C.c_uint8)), ("kind", P(C.c_uint8)), ("size", P(C.c_uint8)),
                    ("cond", P(C.c_uint8)), ("a0", P(C.c_int32)), ("a1", P(C.c_int32)),
                    ("a2", P(C.c_int32)), ("target", P(C.c_uint32)), ("cyt", P(C.c_uint32)),
                    ("cyn", P(C.c_uint32)), ("regs", P(C.c_uint16))]

    class Mon(C.Structure):
        _fields_ = [("fn_of", P(C.c_int32)), ("nfn", C.c_int32),
                    ("obs", P(C.c_uint64)), ("obs_seen", P(C.c_uint8)),
                    ("sobs", P(C.c_int64)), ("sobs_seen", P(C.c_uint8)),
                    ("ncs", C.c_int64), ("ccap", C.c_int64),
                    ("cs_fn", P(C.c_int32)), ("cs_start", P(C.c_uint64)), ("cs_ret", P(C.c_uint32)),
                    ("nfr", C.c_int64), ("fcap", C.c_int64),
                    ("fr_at", P(C.c_uint32)), ("fr_low", P(C.c_uint32)),
                    ("hdr", P(C.c_int32) * 2), ("body_off", P(C.c_int64) * 2),
                    ("body_addr", P(C.c_uint32) * 2), ("bound", P(C.c_int64) * 2),
                    ("count", P(C.c_uint64) * 2), ("worst", P(C.c_uint64) * 2),
                    ("worst_seen", P(C.c_uint8) * 2),
                    ("nviol", C.c_int64), ("vcap", C.c_int64),
                    ("viol_set", P(C.c_int32)), ("viol_loop", P(C.c_int32)),
                    ("viol_count", P(C.c_uint64)), ("failed", C.c_int)]

    lib.M0, lib.Mon = M0, Mon
    lib.m0_run.argtypes = [P(M0), P(Mon)]
    lib.m0_run.restype = C.c_int
    lib.mon_step.argtypes = [P(M0), P(Mon), C.c_int, C.c_int, C.c_uint32, C.c_uint32, C.c_uint32]
    lib.mon_step.restype = None
    lib.mon_push_frame.argtypes = [P(Mon), C.c_uint32, C.c_uint32]
    lib.mon_push_frame.restype = C.c_int
    lib.mon_free.argtypes = [P(Mon)]
    lib.mon_free.restype = None
    names = C.c_char_p * 80
    table = names.in_dll(lib, "m0_op_names")
    lib.ops = {}
    for k in range(80):
        if table[k] is None:
            break
        lib.ops[table[k].decode()] = k


_KIND = {"call": 1, "ret": 2}


def _table(lib, mach, lo, hi):
    """The decoded code of [lo, hi) as the arrays of `M0` (m0.decode, m0.cycles)."""
    import ctypes as C
    n = (hi - lo) // 2
    op, kind, size, cnd = (C.c_uint8 * n)(), (C.c_uint8 * n)(), (C.c_uint8 * n)(), (C.c_uint8 * n)()
    a0, a1, a2 = (C.c_int32 * n)(), (C.c_int32 * n)(), (C.c_int32 * n)()
    target, cyt, cyn, regs = (C.c_uint32 * n)(), (C.c_uint32 * n)(), (C.c_uint32 * n)(), (C.c_uint16 * n)()
    ops = lib.ops
    mem = mach.mem
    for x in range(n):
        addr = lo + 2 * x
        i = mach.cache.get(addr)
        if i is None:
            i = mach.cache[addr] = decode(mem, addr)
        o = ops.get(i.op, 0)
        a = i.a
        if i.op in ("push", "pop"):
            regs[x] = sum(1 << q for q in a[0])
        elif i.op in ("stm", "ldm"):
            a0[x], regs[x] = a[0], sum(1 << q for q in a[1])
        elif i.op == "bcond":
            cnd[x] = a[0]
        else:
            vals = list(a) + [0, 0, 0]
            if not all(isinstance(v, int) and -2**31 <= v < 2**31 for v in vals[:3]):
                o = 0
            else:
                a0[x], a1[x], a2[x] = vals[:3]
        op[x], kind[x], size[x] = o, _KIND.get(i.kind, 0), i.size
        target[x] = (i.target or 0) & 0xFFFFFFFF
        cyt[x], cyn[x] = cycles(i, True), cycles(i, False)
    return dict(op=op, kind=kind, size=size, cond=cnd, a0=a0, a1=a1, a2=a2, target=target,
                cyt=cyt, cyn=cyn, regs=regs)


def _monitor(lib, watch, lo, hi):
    """The `Mon` of `watch` (its arrays kept in the returned list)."""
    import ctypes as C
    keep = []
    n = (hi - lo) // 2
    names = sorted(set(watch.entry.values()))
    fid = {f: k for k, f in enumerate(names)}
    fn_of = (C.c_int32 * n)(*([-1] * n))
    for a, f in watch.entry.items():
        if lo <= a < hi and not (a - lo) % 2:
            fn_of[(a - lo) // 2] = fid[f]
    nf = max(1, len(names))
    w = lib.Mon()
    P = C.POINTER
    w.fn_of, w.nfn = C.cast(fn_of, P(C.c_int32)), len(names)
    obs, obs_seen = (C.c_uint64 * nf)(), (C.c_uint8 * nf)()
    sobs, sobs_seen = (C.c_int64 * nf)(), (C.c_uint8 * nf)()
    w.obs, w.obs_seen = C.cast(obs, P(C.c_uint64)), C.cast(obs_seen, P(C.c_uint8))
    w.sobs, w.sobs_seen = C.cast(sobs, P(C.c_int64)), C.cast(sobs_seen, P(C.c_uint8))
    keep += [fn_of, obs, obs_seen, sobs, sobs_seen]
    heads = []
    for s, loops in enumerate((watch.bodies, watch.cbodies)):
        hs = sorted(loops)
        heads.append(hs)
        hdr = (C.c_int32 * n)(*([-1] * n))
        offs, addrs = [0], []
        for k, h in enumerate(hs):
            if not (lo <= h < hi) or (h - lo) % 2:
                raise ValueError(f"loop header {h:#x} outside the code")
            hdr[(h - lo) // 2] = k
            body = sorted(set(loops[h][0]))
            addrs += body
            offs.append(len(addrs))
        m = max(1, len(hs))
        boff = (C.c_int64 * len(offs))(*offs)
        baddr = (C.c_uint32 * max(1, len(addrs)))(*addrs)
        bound = (C.c_int64 * m)(*[loops[h][1] for h in hs])
        count, worst, wseen = (C.c_uint64 * m)(), (C.c_uint64 * m)(), (C.c_uint8 * m)()
        w.hdr[s], w.body_off[s] = C.cast(hdr, P(C.c_int32)), C.cast(boff, P(C.c_int64))
        w.body_addr[s], w.bound[s] = C.cast(baddr, P(C.c_uint32)), C.cast(bound, P(C.c_int64))
        w.count[s], w.worst[s] = C.cast(count, P(C.c_uint64)), C.cast(worst, P(C.c_uint64))
        w.worst_seen[s] = C.cast(wseen, P(C.c_uint8))
        keep += [hdr, boff, baddr, bound, count, worst, wseen]
    for at, low in watch.frames:
        if not lib.mon_push_frame(C.byref(w), at, low):
            raise MemoryError("m0core: frames")
    return w, keep, names, heads


def _run_core(mach, lib, pc, max_cycles, watch):
    """`Machine.call` by the C core, with the observations of `watch`; the instructions the
    core leaves to m0.py are executed by `Machine._step`."""
    import ctypes as C
    img = mach.img
    lo = min([img.base] + [a for a, _ in img.funcs.values()]) & ~1
    hi = max([img.ro_top] + [a + s for a, s in img.funcs.values()])
    hi += hi & 1
    if any(not (lo <= h < hi) for h in list(watch.bodies) + list(watch.cbodies)):
        raise ValueError("loop header outside the code")
    t = getattr(mach, "_core_table", None)
    if t is None or t[0] != (lo, hi):
        t = mach._core_table = ((lo, hi), _table(lib, mach, lo, hi))
    tab = t[1]
    st = lib.M0()
    for k in range(16):
        st.r[k] = mach.r[k] & 0xFFFFFFFF
    st.n, st.z, st.c, st.v = mach.n, mach.z, mach.c, mach.v
    st.cyc, st.max_cycles, st.pc = mach.cyc, max_cycles, pc
    buf = (C.c_uint8 * len(mach.mem)).from_buffer(mach.mem)
    st.mem, st.mem_len = C.cast(buf, C.POINTER(C.c_uint8)), len(mach.mem)
    st.lo, st.hi = lo, hi
    ftype = dict(lib.M0._fields_)
    for f, arr in tab.items():
        setattr(st, f, C.cast(arr, ftype[f]))
    w, keep, names, heads = _monitor(lib, watch, lo, hi)
    pst, pw = C.byref(st), C.byref(w)

    def to_py():
        mach.r[:] = list(st.r)
        mach.n, mach.z, mach.c, mach.v, mach.cyc = st.n, st.z, st.c, st.v, st.cyc

    def to_c():
        for k in range(16):
            st.r[k] = mach.r[k] & 0xFFFFFFFF
        st.n, st.z, st.c, st.v, st.cyc = int(mach.n), int(mach.z), int(mach.c), int(mach.v), mach.cyc

    def observe(i, _before, nxt):
        to_c()
        if i is None:
            lib.mon_step(pst, pw, 0, 0, 0, 0, nxt & 0xFFFFFFFF)
        else:
            lib.mon_step(pst, pw, 1, _KIND.get(i.kind, 0), i.addr, (i.target or 0) & 0xFFFFFFFF,
                         nxt & 0xFFFFFFFF)
        if w.failed:
            raise MemoryError("m0core: observations")

    try:
        while True:
            status = lib.m0_run(pst, pw)
            if w.failed:
                raise MemoryError("m0core: observations")
            if status == 0:         # HALT
                to_py()
                break
            if status == 2:         # cycle limit, after the instruction (as `_step`)
                to_py()
                raise Stop("cycle limit")
            # an instruction left to m0.py
            to_py()
            mach.on_insn = observe
            try:
                nxt = mach._step(st.pc, max_cycles)
            finally:
                mach.on_insn = None
            to_c()
            st.pc = nxt & 0xFFFFFFFF
            if st.pc == Machine.HALT:
                break
        return mach.r[0]
    finally:
        _collect(watch, w, names, heads)
        lib.mon_free(pw)
        del pst
        st.mem = None
        del buf


def _collect(watch, w, names, heads):
    """The observations of the core into `watch`."""
    for k, f in enumerate(names):
        if w.obs_seen[k]:
            watch.observed[f] = max(watch.observed.get(f, 0), w.obs[k])
        if w.sobs_seen[k]:
            watch.sobserved[f] = max(watch.sobserved.get(f, 0), w.sobs[k])
    for k, h in enumerate(heads[0]):
        if w.worst_seen[0][k]:
            watch.worst_loop[h] = max(watch.worst_loop.get(h, 0), w.worst[0][k])
    for j in range(w.nviol):
        s, k, c = w.viol_set[j], w.viol_loop[j], w.viol_count[j]
        h = heads[s][k]
        _body, N, fn = (watch.bodies, watch.cbodies)[s][h]
        what = "bound" if s == 0 else "certified bound"
        watch.viol.append(f"loop {h:#x} of {fn}: {c} back edges > {what} {N}")
    watch.frames = [[w.fr_at[k], w.fr_low[k]] for k in range(w.nfr)]
