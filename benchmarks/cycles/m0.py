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
    data = open(path, "rb").read()
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

    def call(self, fn, args=(), max_cycles=10**10):
        r = self.r
        for k, a in enumerate(args):
            r[k] = a
        r[13] = self.img.stack_top
        r[14] = self.HALT | 1
        pc = self.img.funcs[fn][0]
        mem = self.mem
        while pc != self.HALT:
            if pc in self.img.undefined:
                name = self.img.undefined[pc]
                if not helper(name, r, mem):
                    raise Stop(f"call to the undefined function {name}")
                if self.on_insn:
                    self.on_insn(None, self.cyc, r[14] & ~1)
                pc = r[14] & ~1
                continue
            i = self.cache.get(pc)
            if i is None:
                i = self.cache[pc] = decode(mem, pc)
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
                self.execute(i, pc)
                if (op in ("addhi", "movhi")) and a[0] == 15:
                    nxt = r[15] & ~1
            self.cyc += cycles(i, taken)
            if self.on_insn:
                self.on_insn(i, before, nxt)
            if self.cyc > max_cycles:
                raise Stop("cycle limit")
            pc = nxt
        return r[0]

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
