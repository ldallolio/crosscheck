# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Jumps through a table (a `switch` compiled to `CMP rI, #n; BHI default; ...; ADD PC, rm`
or `MOV PC, rm`), as the Lean checker checks them (`ThumbDataCore.jumpOk`, `wstep`, `wrun`;
`ThumbCore.xop`, `xres`, `pcWrite`, `pcDestV`): keep identical.

`find(get, pos)` looks back from the jump at `pos` for the `CMP` and the `BHI` (or the
`BLS` to `start + 6`, over a branch to the default case) that start its window and evaluates the window for every value `0..n` of the compared register: the
instructions between the branch and the jump by their effect (`binloops.effect`, the mirror
of `Thumb.effect`) and, for `ADD rd, PC`, `ADR` and loads from the code, by their exact
value. The result is the window's start and the set of addresses the jump can go to, or
None. The checker evaluates the window again and proves (Lean `ThumbData.drun_mrun`) that
every run follows one of these targets, given that nothing branches into the window but
from the instruction before (`interiorOk`, also checked).

Two other forms have no CMP: the index bounded by an instruction of the window (`find_rng`,
Lean `jumpRng`), or by the certified invariant at an instruction of the window
(`inv_candidates`, `window_inv`, Lean `jumpInv`), whose bounds come from the loop analysis
(`binloops.inv_jumps`, iterated with the graph by `wcet.Analysis._resolve_jumps`)."""

import struct

import m0

U = 1 << 32
BACK = 24          # instructions searched back from the jump for its CMP


def half_at(get, A):
    if A % 2:
        return None
    h = get(A)
    return h if h is not None and h < 65536 else None


def byte_at(get, A):
    h = half_at(get, A - A % 2)
    return None if h is None else (h % 256 if A % 2 == 0 else h // 256)


def word_at(get, A):
    if A % 4:
        return None
    lo, hi = half_at(get, A), half_at(get, A + 2)
    return None if lo is None or hi is None else lo + 65536 * hi


def load_at(get, sz, A):
    return byte_at(get, A) if sz == 1 else half_at(get, A) if sz == 2 else word_at(get, A)


def xop(get, a):
    """("addpc", d) | ("adr", d, k) | ("ldimm", sz, d, n, off) | ("ldreg", sz, d, n, m) | None."""
    h = get(a)
    if h is None:
        return None
    if h >> 8 == 0b01000100 and (h >> 7) % 2 == 0 and (h >> 3) % 16 == 15:
        return ("addpc", h % 8)
    if h >> 11 == 0b10100:
        return ("adr", (h >> 8) % 8, (a + 4) // 4 * 4 + 4 * (h % 256))
    if h >> 11 == 0b01101:
        return ("ldimm", 4, h % 8, (h >> 3) % 8, 4 * ((h >> 6) % 32))
    if h >> 11 == 0b10001:
        return ("ldimm", 2, h % 8, (h >> 3) % 8, 2 * ((h >> 6) % 32))
    if h >> 11 == 0b01111:
        return ("ldimm", 1, h % 8, (h >> 3) % 8, (h >> 6) % 32)
    for code, sz in ((0b0101100, 4), (0b0101101, 2), (0b0101110, 1)):
        if h >> 9 == code:
            return ("ldreg", sz, h % 8, (h >> 3) % 8, (h >> 6) % 8)
    return None


def xdst(op):
    return op[1] if op[0] in ("addpc", "adr") else op[2]


def xres(get, a, P, op):
    if op[0] == "addpc":
        v = P.get(op[1])
        return None if v is None else (v + a + 4) % U
    if op[0] == "adr":
        return op[2]
    if op[0] == "ldimm":
        _, sz, _d, n, off = op
        v = P.get(n)
        return None if v is None else load_at(get, sz, (v + off) % U)
    _, sz, _d, n, m = op
    v, w = P.get(n), P.get(m)
    return None if v is None or w is None else load_at(get, sz, (v + w) % U)


def pc_write(get, a):
    """(add?, m) for `ADD PC, rm` / `MOV PC, rm` with m < 8."""
    h = get(a)
    if h is None:
        return None
    if h >> 8 in (0b01000100, 0b01000110) and (h >> 7) % 2 == 1 and h % 8 == 7 and (h >> 3) % 16 < 8:
        return (h >> 8 == 0b01000100, (h >> 3) % 16)
    return None


def pc_dest(a, add, v):
    x = (a + 4 + v) % U if add else v
    return x - x % 2


def src_p(P, s):
    return P.get(s[1]) if s[0] == "reg" else s[1]


def val_p(P, v):
    if v == "any":
        return None
    if v[0] == "shl":
        x = src_p(P, v[1])
        return None if x is None else (x * 2 ** v[2]) % U
    if v[0] == "shr":
        import binloops
        x = src_p(P, v[1])
        return None if x is None else binloops.shr_val(v[3], v[2], x) % U
    x, y = src_p(P, v[1]), src_p(P, v[2])
    if x is None or y is None:
        return None
    return (x + y) % U if v[0] == "add" else (x + (U - y)) % U


def wstep(abi, get, a, P):
    import binloops
    dst, _fl = binloops.effect(abi, get, a)
    op = xop(get, a)
    out = {}
    for i in range(8):
        p = next((p for p in dst if p[0] == i), None)
        if p is None:
            v = P.get(i)
        elif op is not None and xdst(op) == i:
            v = xres(get, a, P, op)
        else:
            v = val_p(P, p[1])
        if v is not None:
            out[i] = v
    return out


def wrun(abi, get, k, a, P):
    for j in range(k):
        P = wstep(abi, get, a + 2 * j, P)
    return P


def window(abi, get, start, pos):
    """The targets of the jump at `pos` with its window from the CMP at `start`
    (`jumpOk`), or None."""
    import binloops
    pw = pc_write(get, pos)
    if pw is None or start + 4 > pos or (pos - start) % 2:
        return None
    add, m = pw
    dst, fl = binloops.effect(abi, get, start)
    if dst or not (isinstance(fl, tuple) and fl[0] == "sub" and fl[1][0] == "reg" and fl[2][0] == "imm"):
        return None
    r, n = fl[1][1], fl[2][1]
    if r >= 8 or n >= U:
        return None
    h1 = get(start + 2)
    if h1 is None or h1 >> 12 != 0b1101 or (h1 >> 8) % 16 not in (8, 9):
        return None
    tb = start + 2 + 4 + m0.sx(h1 & 0xFF, 8) * 2
    ls = (h1 >> 8) % 16 == 9         # `lsForm`: BLS to start + 6, over a branch to the default
    if tb < 0 or (tb != start + 6 if ls else tb == start + 4):
        return None
    beg = start + 6 if ls else start + 4      # `wbeg`
    if beg > pos or binloops.effect(abi, get, start + 2) != ([], "keep"):
        return None
    targets = set()
    for x in range(n + 1):
        P = wrun(abi, get, (pos - beg) // 2, beg, {r: x})
        v = P.get(m)
        if v is None:
            return None
        targets.add(pc_dest(pos, add, v))
    return sorted(targets)


# windows whose index is bounded by an instruction (`ThumbDataCore.rngOps`, `jumpRng`):
# Clang's form when it knows the range of the index (`switch (x & 7)`) and emits no CMP
RCAP = 1024


def rng_ops(get, a):
    """[(d, src)]: register d is at most the value of src before the instruction
    (`rngOps`): ANDS by either operand, LSRS by a constant, UXTB, LDRB."""
    h = get(a)
    if h is None:
        return []
    if h >> 6 == 0b0100000000:
        return [(h % 8, ("reg", (h >> 3) % 8)), (h % 8, ("reg", h % 8))]
    if h >> 11 == 0b00001:
        s = (h >> 6) % 32
        return [(h % 8, ("imm", 0 if s == 0 else 2 ** (32 - s) - 1))]
    if h >> 6 == 0b1011001011 or h >> 11 == 0b01111 or h >> 9 == 0b0101110:
        return [(h % 8, ("imm", 255))]
    return []


def rng_b(get, a, P):
    for d, s in rng_ops(get, a):
        b = src_p(P, s)
        if b is not None:
            return d, b
    return None


def window_rng(abi, get, start, p, pos):
    """The targets of the jump at `pos` with its window from `start` bounded at `p`
    (`jumpRng`), or None."""
    pw = pc_write(get, pos)
    if pw is None or not start <= p < pos or (p - start) % 2 or (pos - start) % 2:
        return None
    add, m = pw
    pre = wrun(abi, get, (p - start) // 2, start, {})
    rb = rng_b(get, p, pre)
    if rb is None:
        return None
    d, b = rb
    if d >= 8 or b >= RCAP:
        return None
    after = wstep(abi, get, p, pre)
    targets = set()
    for x in range(b + 1):
        P = dict(after)
        P[d] = x
        v = wrun(abi, get, (pos - (p + 2)) // 2, p + 2, P).get(m)
        if v is None:
            return None
        targets.add(pc_dest(pos, add, v))
    return sorted(targets)


def find_rng(get, pos, abi=False, within=None):
    """(start, targets, p) of a window without CMP: the bounding instruction `p` closest to
    the jump whose window gives targets inside `within` (the function's addresses), with
    the shortest window that knows the bound; the fewest targets first."""
    best = None
    for k in range(1, BACK + 1):
        p = pos - 2 * k
        if p < 0:
            break
        if not rng_ops(get, p):
            continue
        for j in range(0, BACK + 1 - k):
            start = p - 2 * j
            if start < 0:
                break
            if rng_b(get, p, wrun(abi, get, j, start, {})) is None:
                continue
            t = window_rng(abi, get, start, p, pos)
            if t is not None and (within is None or all(within[0] <= q < within[1] for q in t)):
                if best is None or len(t) < len(best[1]):
                    best = (start, t, p)
            break
    return best


# windows whose index is bounded by the certified invariant (`ThumbDataCore.jumpInv`): an
# index bounded only by a loop (`switch (i)` in a loop on `i < 8`) or by constants set on
# several paths; the bounds come from the loop analysis (`binloops.inv_jumps`)


def window_inv(abi, get, start, p, pos, d, lo, hi, cong=(0, 0)):
    """The targets of the jump at `pos` with its window from `start`, register `d` in
    `lo..hi` at `p` with residue `cong` = (e, r) modulo 2^e (`jumpInv`), or None."""
    pw = pc_write(get, pos)
    if pw is None or not start <= p <= pos or (p - start) % 2 or (pos - start) % 2:
        return None
    if d >= 8 or hi >= RCAP or lo > hi:
        return None
    add, m = pw
    pre = wrun(abi, get, (p - start) // 2, start, {})
    e, r = cong
    targets = set()
    for x in range(lo, hi + 1):
        if x % 2 ** e != r % 2 ** e:
            continue
        P = dict(pre)
        P[d] = x
        v = wrun(abi, get, (pos - p) // 2, p, P).get(m)
        if v is None:
            return None
        targets.add(pc_dest(pos, add, v))
    return sorted(targets)


PROBE = (0, 1, 2, 4, 8)


def inv_candidates(get, pos, abi=False, within=None):
    """[(start, p, d)]: windows of the jump at `pos` without CMP whose address is computed
    from register `d` at `p` (unknown without it) and from registers the window itself sets
    from `start`; straight-line code from `start` to the jump (`m0.decode` kind `seq`); the
    shortest such window for each `p` and `d`, `p` closest to the jump first; `within`: the
    function's addresses, the window inside it."""
    pw = pc_write(get, pos)
    if pw is None:
        return []
    add, m = pw

    def straight(a):
        h = get(a)
        if h is None:
            return False
        i = m0.decode(struct.pack("<HH", h, get(a + 2) or 0), 0)
        return i.kind == "seq"

    out = []
    for k in range(0, BACK + 1):
        p = pos - 2 * k
        if p < 0 or (within is not None and p < within[0]) or (k and not straight(p)):
            break
        for d in range(8):
            for j in range(0, BACK + 1 - k):
                start = p - 2 * j
                if start < 0 or (within is not None and start < within[0]) or (j and not straight(start)):
                    break
                pre = wrun(abi, get, j, start, {})
                if d in pre:
                    break           # d is set inside the window: not this register
                if wrun(abi, get, k, p, dict(pre)).get(m) is not None:
                    continue        # the address does not depend on d
                ok = False
                for x in PROBE:
                    P = dict(pre)
                    P[d] = x
                    v = wrun(abi, get, k, p, P).get(m)
                    if v is not None and (within is None or within[0] <= pc_dest(pos, add, v) < within[1]):
                        ok = True
                        break
                if ok:
                    out.append((start, p, d))
                    break
    return out


def ub_of(g, d):
    """The bound u of a fact x_d - u <= 0 (`ubOf`); g = (coefficients, constant)."""
    sv = {v: k for v, k in g[0].items() if k}
    return -g[1] if sv == {d: 1} else None


def lb_of(g, d):
    """The bound l of a fact l - x_d <= 0 (`lbOf`)."""
    sv = {v: k for v, k in g[0].items() if k}
    return g[1] if sv == {d: -1} else None


def inv_bound(disjuncts, d, lo, hi):
    """Every disjunct of the invariant puts x_d in lo..hi (`invBound`)."""
    for I in disjuncts:
        if not any(ub_of(g, d) is not None and ub_of(g, d) <= hi for g in I):
            return False
        if lo != 0 and not any(lb_of(g, d) is not None and lb_of(g, d) >= lo for g in I):
            return False
    return True


def interior_ok_r(start, pos, entry, edges):
    """Nothing enters `start + 2 .. pos` but from the instruction before, and the entry is
    not there (`interiorOk`, window without CMP); `edges`: (source, destination)."""
    inside = set(range(start + 2, pos + 1, 2))
    if entry in inside:
        return False
    return all(t not in inside or s == t - 2 for s, t in edges)


def getter(img):
    """The halfwords of the code region of a certificate (as `ipet.code_top`)."""
    import ipet
    top, mem, base = ipet.code_top(img), img.mem, getattr(img, "base", 0)
    return lambda a: (int.from_bytes(mem[a:a + 2], "little")
                      if base <= a and a + 2 <= top and (a - base) % 2 == 0 else None)


def find(get, pos, abi=False, within=None):
    """(start, targets, ix) of the jump through a table at `pos`, or None: the window from a
    CMP (`ix` None), else a window bounded by an instruction at `ix` (`find_rng`, targets
    inside `within`)."""
    if pc_write(get, pos) is None:
        return None
    for k in range(2, BACK + 2):
        start = pos - 2 * k
        if start < 0:
            break
        t = window(abi, get, start, pos)
        if t is not None:
            return start, t, None
    return find_rng(get, pos, abi, within)
