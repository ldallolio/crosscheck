# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Loop bounds certified on Cortex-M0 machine code (Lean `ThumbDataCore`, `ThumbData`).

For a function of the binary, finds per instruction an invariant (linear constraints on
the registers r0-r7 and on two ghost variables, the operands of the operation that set
the flags) and per natural loop a potential that decreases on the back edges, and emits
the certificate that `crosscheck-check` verifies with `Thumb.checkData` (theorem
`ThumbData.data_sound`): the loop's row (at most `N` back edges per entry, `N` found here)
then holds on every run of the machine code's data semantics, and is no longer trusted.

Everything here is untrusted: the invariants come from an analysis of differences of
registers (a zone domain, with widening at loop headers and descending iterations), the
potentials from the loop exit tests, the Farkas multipliers from shortest paths (or a
linear program); what cannot be proved is dropped (an invariant constraint, or a loop,
whose row then stays trusted). The definitions mirrored from Lean (`effect`,
`condFacts`, `postE`, the obligations and their order) must stay identical to
`ThumbDataCore.lean`: the checker recomputes the obligations and compares.
"""
import itertools
import math
import os
import time
from fractions import Fraction

import ipet
import wcet


CONG = True
DISJ = True          # disjunctive invariants at a possible wrap-around (`window_transfer`)
LP = True            # potentials per instruction by a linear program (`synth_lp`)
BIG = 1 << 20       # constants above this are left out of a coarse linear program
LP_SECONDS = 5.0     # per solve: HiGHS can stall on these badly scaled programs
# per function, in CPU seconds of the process (both analyses): past it the analysis of the
# function stops (`BudgetSpent`: no loop certified) or, during the linear programs, the
# remaining loops get none. The producer is untrusted: the budget can only leave loops
# uncertified. 600 s loses no loop of the 29 kernels (the largest function, pm_kernel, needs
# about 400 s); environment variable CROSSCHECK_LOOP_SECONDS, 0 = no budget.
FUNC_SECONDS = float(os.environ.get("CROSSCHECK_LOOP_SECONDS", "600"))
_DEADLINE = None     # the deadline of the function being certified (checked by `_tick`)


class BudgetSpent(Exception):
    """The time budget of the function is spent (its analysis is abandoned)."""


def _tick():
    if _DEADLINE is not None and time.process_time() >= _DEADLINE:
        raise BudgetSpent()
HARD_VISITS = 200    # visits of a loop head after which growing bounds are dropped (forget)


def structure(an, name):
    """(entry, blocks, succ, back edges, loop bodies, headers innermost first, source bound
    by header or None): the loops of the binary even when no source loop bounds them."""
    entry, blocks, succ = an.cfg(name)
    try:
        _p, back, loops, headers, _par, bound = an.loop_structure(name, entry, blocks, succ)
        return entry, blocks, succ, back, loops, headers, dict(bound)
    except wcet.Unbounded:
        free = wcet.Analysis(an.img, {}, {None: 0})
        _p, back, loops, headers, _par, _b = free.loop_structure(name, entry, blocks, succ)
        src = {h: None for h in headers}
        return entry, blocks, succ, back, loops, headers, src

U = 1 << 32
H = 1 << 31
# variables of the certificate: 0-7 registers, 8-9 ghosts, 10-17 written registers, 18-19 fresh
# ghosts, 20.. the tracked words of the frame, then their fresh values (Lean `nVars`)
INF = 1 << 62
# BINLOOPS_CHECK_CLOSE=1: compare every shortcut of the zone closure (incremental closure,
# images of closed zones, joins) with the full closure, and fail on a difference (tests)
CHECK_CLOSE = os.environ.get("BINLOOPS_CHECK_CLOSE") == "1"
ZERO = -1        # the zero node of the difference graphs


# ----------------------------------------------------------------------------------------
# Mirror of ThumbDataCore.lean

def reg(i):
    return ("reg", i)


def imm(k):
    return ("imm", k)


def lowlist(h):
    return [i for i in range(8) if (h >> i) & 1]


def effect(abi, get, a):
    """(dst, fl): dst = [(register, value)], value = ("add"|"sub", src, src) or "any";
    fl = "keep" | "any" | ("add"|"sub", src, src). As Lean `Thumb.effect`."""
    h = get(a)
    if h is None:
        return [], "any"
    top5, rd, rn = h >> 11, h % 8, (h >> 3) % 8
    if top5 in (0b11101, 0b11110, 0b11111):
        return [(i, "any") for i in ([0, 1, 2, 3] if abi else range(8))], "any"
    if top5 == 0:
        # LSLS rd, rm, #s: (rm * 2^s) mod 2^32 (s = 0 is MOVS rd, rm)
        s = (h >> 6) % 32
        return [(rd, ("add", reg(rn), imm(0)) if s == 0 else ("shl", reg(rn), s))], "any"
    if top5 <= 2:
        return [(rd, "any")], "any"
    if top5 == 3:
        m, o = (h >> 6) % 8, (h >> 9) % 4
        op = "add" if o in (0, 2) else "sub"
        b = reg(m) if o in (0, 1) else imm(m)
        return [(rd, (op, reg(rn), b))], (op, reg(rn), b)
    if top5 <= 7:
        r, k, o = (h >> 8) % 8, h % 256, top5 % 4
        if o == 0:
            return [(r, ("add", imm(k), imm(0)))], "any"
        if o == 1:
            return [], ("sub", reg(r), imm(k))
        op = "add" if o == 2 else "sub"
        return [(r, (op, reg(r), imm(k)))], (op, reg(r), imm(k))
    if h >> 10 == 0b010000:
        opc = (h >> 6) % 16
        if opc == 10:
            return [], ("sub", reg(rd), reg(rn))
        if opc == 11:
            return [], ("add", reg(rd), reg(rn))
        if opc == 8:
            return [], "any"
        if opc == 9:
            return [(rd, ("sub", imm(0), reg(rn)))], ("sub", imm(0), reg(rn))
        if opc == 15:
            return [(rd, ("sub", imm(U - 1), reg(rn)))], "any"
        return [(rd, "any")], "any"
    if h >> 10 == 0b010001:
        opc, d, m = (h >> 8) % 4, ((h >> 7) % 2) * 8 + h % 8, (h >> 3) % 16
        if opc == 0:
            return ([(d, ("add", reg(d), reg(m)) if m < 8 else "any")] if d < 8 else []), "keep"
        if opc == 1:
            return [], "any"
        if opc == 2:
            return ([(d, ("add", reg(m), imm(0)) if m < 8 else "any")] if d < 8 else []), "keep"
        return [], "keep"
    if top5 == 0b01001:
        ad = (a + 4) // 4 * 4 + 4 * (h % 256)
        lo_, hi_ = get(ad), get(ad + 2)
        if lo_ is not None and hi_ is not None and lo_ < 65536 and hi_ < 65536:
            return [((h >> 8) % 8, ("add", imm(lo_ + 65536 * hi_), imm(0)))], "keep"
        return [((h >> 8) % 8, "any")], "keep"
    if h >> 12 == 0b0101:
        return ([(rd, "any")] if (h >> 9) % 8 >= 3 else []), "keep"
    if h >> 13 == 0b011 or h >> 12 == 0b1000:
        return ([(rd, "any")] if (h >> 11) % 2 == 1 else []), "keep"
    if h >> 12 == 0b1001:
        return ([((h >> 8) % 8, "any")] if (h >> 11) % 2 == 1 else []), "keep"
    if top5 in (0b10100, 0b10101):
        return [((h >> 8) % 8, "any")], "keep"
    if h >> 12 == 0b1011:
        if h >> 8 in (0b10110010, 0b10111010):
            return [(rd, "any")], "keep"
        if h >> 9 == 0b1011110:
            return [(i, "any") for i in lowlist(h)], "keep"
        return [], "keep"
    if h >> 12 == 0b1100:
        b, lst = (h >> 8) % 8, lowlist(h)
        if not lst:
            return [(b, "any")], "keep"
        if (h >> 11) % 2 == 0:
            return [(b, ("add", reg(b), imm(4 * len(lst))))], "keep"
        if b in lst:
            return [(i, "any") for i in lst], "keep"
        return [(b, ("add", reg(b), imm(4 * len(lst))))] + [(i, "any") for i in lst], "keep"
    return [], "keep"


# A linear constraint `Σ k·x_v + c ≤ 0` or an affine expression: (dict v -> k, c).

def lin(terms, c):
    d = {}
    for k, v in terms:
        d[v] = d.get(v, 0) + k
    return ({v: k for v, k in d.items() if k}, c)


def dle(c):
    return lin([(1, 8), (-1, 9)], c)


def dge(c):
    return lin([(-1, 8), (1, 9)], c)


def lo(v):
    return lin([(1, v)], 1 - H)


def hi(v):
    return lin([(-1, v)], H)


def sumc(s, c):
    return lin([(s, 8), (s, 9)], c)


def sub_facts(c):
    return {0: [[dle(0), dge(0)]], 1: [[dle(1)], [dge(1)]], 2: [[dge(0)]], 3: [[dle(1)]],
            8: [[dge(1)]], 9: [[dle(0)]],
            10: [[lo(8), lo(9), dge(0)], [hi(8), hi(9), dge(0)], [lo(8), hi(9)]],
            11: [[lo(8), lo(9), dle(1)], [hi(8), hi(9), dle(1)], [hi(8), lo(9)]],
            12: [[lo(8), lo(9), dge(1)], [hi(8), hi(9), dge(1)], [lo(8), hi(9)]],
            13: [[lo(8), lo(9), dle(0)], [hi(8), hi(9), dle(0)], [hi(8), lo(9)]]}.get(c, [[]])


def add_facts(c):
    return {0: [[sumc(1, 0), sumc(-1, 0)], [sumc(1, -U), sumc(-1, U)]],
            1: [[sumc(-1, 1), sumc(1, 1 - U)], [sumc(-1, U + 1)]],
            2: [[sumc(-1, U)]], 3: [[sumc(1, 1 - U)]], 8: [[sumc(-1, U + 1)]],
            9: [[sumc(1, -U)]]}.get(c, [[]])


def cond_facts(kind, cc, taken, m=(1, 1)):
    """The facts of a condition, as a disjunction of conjunctions (Lean `condFactsM`). With
    `m = (md, ms)`, powers of two such that the ghost operands are congruent modulo `md` and
    their sum is a multiple of `ms`, the facts on their difference are rounded to multiples
    of `md` and those on their sum to multiples of `ms` (Granger's congruences)."""
    md, ms = m
    c = cc if taken else cc ^ 1
    if kind == "none":
        return [[]]
    facts = add_facts(c) if kind != "sub" else sub_facts(c)
    return [[tighten_s(tighten(f, md), ms) for f in D] for D in facts]


def tighten_s(f, m):
    """`g8 + g9 + c <= 0` (or `-(g8 + g9) + c <= 0`) when `g8 + g9` is a multiple of `m`:
    `c` rounded up to a multiple of `m` (Lean `tightenS`)."""
    d, c = f
    if m > 1 and d in ({8: 1, 9: 1}, {8: -1, 9: -1}):
        return (d, -(-c // m) * m)
    return f


def tighten(f, m):
    """`g8 - g9 + c <= 0` (or `g9 - g8 + c <= 0`) when `g8 - g9` is a multiple of `m`:
    `c` rounded up to a multiple of `m`."""
    d, c = f
    if m > 1 and d in ({8: 1, 9: -1}, {8: -1, 9: 1}):
        return (d, -(-c // m) * m)
    return f


# ----------------------------------------------------------------------------------------
# Congruences modulo powers of two (Granger 1989): variable `v` of the certificate is `r`
# modulo `2^e`, `e` at most 32, so that wrapping modulo 2^32 keeps them. Mirror of
# `congOf`, `gExp`, `tightenL`, `congSv` in `ThumbDataCore` (keep identical).

def cong_of(C, v):
    return C.get(v, (0, 0)) if C else (0, 0)


def g_exp(C):
    """The largest `e` such that the ghost operands are congruent modulo `2^e`."""
    e8, r8 = cong_of(C, 8)
    e9, r9 = cong_of(C, 9)
    return max([e for e in range(33) if e <= e8 and e <= e9 and (r8 - r9) % (1 << e) == 0], default=0)


def cong_sv(C, e, P):
    """The residue of `P` modulo `2^e`, or None (`congSv` + constant)."""
    t = P[1]
    for v, k in P[0].items():
        ev, rv = cong_of(C, v)
        if (k * (1 << ev)) % (1 << e):
            return None
        t += k * rv
    return t


def cong_best(C, Ps):
    """The finest congruence `(e, r)` of a value given by every expression of `Ps` (one per
    wrap case), or None."""
    for e in range(32, 0, -1):
        ts = [cong_sv(C, e, P) for P in Ps]
        if all(t is not None for t in ts) and len({t % (1 << e) for t in ts}) == 1:
            return (e, ts[0] % (1 << e))
    return None


def cjoin(x, y):
    e = min(x[0], y[0])
    while e > 0 and (x[1] - y[1]) % (1 << e):
        e -= 1
    return (e, x[1] % (1 << e))


def congruences(ctx):
    """The congruences of the variables of the certificate (registers, ghosts, tracked
    words `20 + j`) before each instruction: a fixpoint over the transitions, from the
    entry where nothing is known."""
    S = len(ctx.slots)
    vs = list(range(10)) + [20 + j for j in range(S)]
    C = {a: None for a in ctx.nodes}
    C[ctx.entry] = {}
    work = [ctx.entry]
    while work:
        _tick()
        a = work.pop()
        Ca = C[a]
        eff, st = ctx.aeff[a], ctx.st[a]
        for nxt, _w, _cs in ipet.trans(ctx.insn[a], ctx.jumps):
            if nxt is None or nxt not in C:
                continue
            post = {}
            for v in vs:
                Ps = [post_s(eff, st, ctx.frame, ctx.sp.get(a), ctx.slots, m, v) for m in mcases(eff)]
                b = cong_best(Ca, Ps)
                if b is not None:
                    post[v] = b
            old = C[nxt]
            new = post if old is None else {v: cjoin(old[v], post[v]) for v in old if v in post}
            new = {v: x for v, x in new.items() if x[0] > 0}
            if nxt == ctx.entry:
                new = {}
            if new != old:
                C[nxt] = new
                work.append(nxt)
    return {a: (c or {}) for a, c in C.items()}


def g_exp_s(C):
    """The largest `e` such that the sum of the ghost operands is a multiple of `2^e`."""
    e8, r8 = cong_of(C, 8)
    e9, r9 = cong_of(C, 9)
    return max([e for e in range(33) if e <= e8 and e <= e9 and (r8 + r9) % (1 << e) == 0], default=0)


def cmod(C, a):
    """(`2^e`, `2^es`): `e` the exponent of the difference of the ghost operands before `a`,
    `es` that of their sum ((1, 1) when unknown)."""
    if C is None:
        return 1, 1
    return 1 << g_exp(C.get(a)), 1 << g_exp_s(C.get(a))


def padd(a, b):
    d = dict(a[0])
    for v, k in b[0].items():
        d[v] = d.get(v, 0) + k
    return ({v: k for v, k in d.items() if k}, a[1] + b[1])


def psmul(k, a):
    return ({v: k * x for v, x in a[0].items() if k * x}, k * a[1])


def pv(i):
    return ({i: 1}, 0)


def pconst(k):
    return ({}, k)


def src_e(s):
    return pv(s[1]) if s[0] == "reg" else pconst(s[1])


def val_srcs(v):
    """The operands of a written value (the shift amount of `shl` is not one)."""
    return v[1:2] if v[0] == "shl" else v[1:]


def val_e(v, m, i):
    if v == "any":
        return pv(10 + i)
    op, a, b = v
    if op == "shl":
        # no overflow (m = 0): a * 2^b; overflow: any value
        return psmul(1 << b, src_e(a)) if m == 0 else pv(10 + i)
    e = padd(src_e(a), src_e(b)) if op == "add" else padd(src_e(a), psmul(-1, src_e(b)))
    return padd(e, pconst(m * U))


def post_e(eff, m, i):
    dst, fl = eff
    if i < 8:
        for r, v in dst:
            if r == i:
                return val_e(v, m, i)
        return pv(i)
    if fl == "keep":
        return pv(i)
    if fl == "any":
        return pv(i + 10)
    return src_e(fl[1] if i == 8 else fl[2])


def popcount8(h):
    return bin(h & 0xFF).count("1")


def stack_effect(abi, get, a):
    """(sp, mem, load, escapes), as Lean `Thumb.stackEffect`: sp = "keep" | ("add", k) | "any";
    mem = "keep" | ("store", imm, rt) | ("push", n) | "other"; load = (rt, imm) or None."""
    h = get(a)
    if h is None:
        return "any", "other", None, True
    top5 = h >> 11
    if top5 in (0b11101, 0b11110, 0b11111):
        return ("keep" if abi else "any"), "other", None, False
    if h >> 12 == 0b1001:
        if (h >> 11) % 2 == 1:
            return "keep", "keep", ((h >> 8) % 8, (h % 256) * 4), False
        return "keep", ("store", (h % 256) * 4, (h >> 8) % 8), None, False
    if top5 == 0b10101:
        return "keep", "keep", None, True
    if h >> 8 == 0b10110000:
        k = (h % 128) * 4
        return ("add", -k if (h >> 7) % 2 == 1 else k), "keep", None, False
    if h >> 9 == 0b1011010:
        n = popcount8(h) + (h >> 8) % 2
        return ("add", -4 * n), ("push", n), None, False
    if h >> 9 == 0b1011110:
        n = popcount8(h) + (h >> 8) % 2
        return ("add", 4 * n), "keep", None, False
    if h >> 10 == 0b010001:
        opc, d, m = (h >> 8) % 4, ((h >> 7) % 2) * 8 + h % 8, (h >> 3) % 16
        sp = "any" if opc in (0, 2) and d == 13 else "keep"
        return sp, "keep", None, (opc in (0, 2) and m == 13 and d != 13)
    if ((h >> 12 == 0b0101 and (h >> 9) % 8 < 3) or
            ((h >> 13 == 0b011 or h >> 12 == 0b1000) and (h >> 11) % 2 == 0) or
            (h >> 12 == 0b1100 and (h >> 11) % 2 == 0)):
        return "keep", "other", None, False
    return "keep", "keep", None, False


def fp_setup(get, a):
    """`ADD r7, SP, #imm`, as Lean `Thumb.fpSetup`."""
    h = get(a)
    return h is not None and h >> 11 == 0b10101 and (h >> 8) % 8 == 7


def is_push(get, a):
    h = get(a)
    return h is not None and h >> 9 == 0b1011010


def regs_read(h):
    """As Lean `Thumb.regsRead`: the registers an instruction may read, not counting the
    base register of a load (over-approximated by encoding)."""
    f0, f3, f6, f8 = h % 8, (h >> 3) % 8, (h >> 6) % 8, (h >> 8) % 8
    top5 = h >> 11
    lst = [r for r in range(8) if (h >> r) % 2 == 1]
    if top5 in (0b11101, 0b11110, 0b11111):
        return []
    if top5 == 0b00011:
        return [f3, f6] if (h >> 10) % 2 == 0 else [f3]
    if h >> 13 == 0:
        return [f3]
    if h >> 13 == 0b001:
        return [f8]
    if h >> 10 == 0b010000:
        return [f0, f3]
    if h >> 10 == 0b010001:
        return [((h >> 7) % 2) * 8 + f0, (h >> 3) % 16]
    if top5 == 0b01001:
        return []
    if h >> 12 == 0b0101:
        return [f0, f3, f6] if (h >> 9) % 8 < 3 else [f6]
    if h >> 13 == 0b011 or h >> 12 == 0b1000:
        return [f0, f3] if (h >> 11) % 2 == 0 else []
    if h >> 12 == 0b1001:
        return [f8] if (h >> 11) % 2 == 0 else []
    if h >> 12 == 0b1010:
        return []
    if h >> 9 == 0b1011010:
        return lst
    if h >> 9 == 0b1011110 or h >> 8 == 0b10110000:
        return []
    if h >> 12 == 0b1011:
        return [f3]
    if top5 == 0b11000:
        return [f8] + lst
    return []


def reads_r7(get, a):
    h = get(a)
    return h is None or 7 in regs_read(h)


def frame_use_ok(ctx, a):
    """As Lean `Thumb.frameUseOk`: the code the assumption `frame` may be used on."""
    fp = any(fp_setup(ctx.get, b) for b in ctx.nodes)
    return ((not ctx.st[a][3] or fp_setup(ctx.get, a)) and
            (not fp or not reads_r7(ctx.get, a) or (a == ctx.entry and is_push(ctx.get, a))))


def slot_idx(slots, k):
    return slots.index(k) if k > 0 and k in slots else None


def post_s(eff, st, frame, delta, slots, m, i):
    """As Lean `Thumb.postS`."""
    _sp, mem, load, _esc = st
    S = len(slots)
    if i < 8:
        if load is not None and delta is not None and i == load[0]:
            j = slot_idx(slots, -(delta + load[1]))
            if j is not None:
                return pv(20 + j)
        return post_e(eff, m, i)
    if i < 20:
        return post_e(eff, m, i)
    jj = i - 20
    k = slots[jj] if jj < S else 0
    if mem == "keep":
        return pv(i)
    if mem[0] == "store":
        if delta is None:
            return pv(i + S)
        return pv(mem[2]) if k == -(delta + mem[1]) else pv(i)
    if mem[0] == "push":
        if delta is None:
            return pv(i + S)
        return pv(i + S) if delta - 4 * mem[1] <= -k < delta else pv(i)
    # other
    if delta is not None and frame and k <= -delta:
        return pv(i)
    return pv(i + S)


def subst(g, sigma):
    """Simultaneous substitution of `sigma(v)` for every variable of `g`."""
    out = ({}, g[1])
    for v, k in g[0].items():
        out = padd(out, psmul(k, sigma(v)))
    return out


def goal_lin(k, p, q):
    return padd(padd(pconst(k), p), psmul(-1, q))


def op_of(eff):
    for r, v in eff[0]:
        if v != "any":
            return r, v
    return None


def wrap_prem(eff, m):
    o = op_of(eff)
    if o is None:
        return []
    if o[1][0] == "shl" and m != 0:
        # overflow: a * 2^b >= 2^32
        x = psmul(1 << o[1][2], src_e(o[1][1]))
        return [padd(pconst(U), psmul(-1, x))]
    x = val_e(o[1], m, o[0])
    return [psmul(-1, x), padd(x, pconst(-(U - 1)))]


def mcases(eff):
    return [0, 1, -1] if op_of(eff) is not None else [0]


def nvars(S):
    return 20 + 2 * S


def ranges_n(n):
    return [c for v in range(n) for c in (lin([(-1, v)], 0), lin([(1, v)], 1 - U))]


class Loop:
    def __init__(self, header, body, scale, bound, pot):
        self.header, self.body, self.scale, self.bound, self.pot = header, body, scale, bound, pot

    def pot_at(self, a):
        if a is None or a not in self.body:
            return pconst(0)
        return self.pot[self.body.index(a)]

    def coef(self, a, nxt):
        if nxt != self.header:
            return 0
        return self.scale if a in self.body else -self.bound


def row_rhs(entry, lc):
    return lc.bound if entry in lc.body else 0


class Invs(dict):
    """Invariants {instruction: constraints} (the first disjunct, Lean `invAt`), with
    `alt` {instruction: [further disjuncts]} and `tags` {instruction: [tag of each
    disjunct]} (0: no wrap-around at the window's start, 1: wrap-around)."""

    def __init__(self, *args, alt=None, tags=None):
        super().__init__(*args)
        self.alt = alt or {}
        self.tags = tags or {}

    def copy(self):
        return Invs({a: list(v) for a, v in self.items()},
                    alt={a: [list(d) for d in v] for a, v in self.alt.items()}, tags=dict(self.tags))


def disjuncts(inv, a):
    """Lean `invsAt`: the invariant at `a`, then its alternatives."""
    return [inv.get(a, [])] + getattr(inv, "alt", {}).get(a, [])


def pick_of(ctx, inv, a, m, si, nxt):
    """Lean `tgtIdx`: the disjunct of `nxt` that the case lands in (the producer's choice):
    the same tag as the source disjunct, or, from the start of a window, the tag of the
    wrap-around case `m`."""
    tags = getattr(inv, "tags", {})
    if nxt not in tags:
        return 0
    if a in tags:
        tag = tags[a][si] if si < len(tags[a]) else None
    elif a in getattr(ctx, "windows", {}):
        w = wrap_op(ctx.eff[a])
        wm = 1 if w is not None and w[2] < 0 else -1
        tag = 0 if m == 0 else (1 if m == wm else None)
    else:
        tag = None
    return tags[nxt].index(tag) if tag in tags[nxt] else 0


def obligation_cases(ctx, a, inv, kinds):
    """The cases of the transitions of `a` in the checker's order (Lean `obsOf`):
    [(j, successor, m, d, facts, si, source disjunct, target index)]."""
    i, eff = ctx.insn[a], ctx.eff[a]
    ka = kinds.get(a, "none")
    out = []
    for j, (nxt, _w, _cs) in enumerate(ipet.trans(i, ctx.jumps)):
        facts = cond_facts(ka, ctx.cc[a], j == 0, cmod(ctx.cong, a)) if i.kind == "cond" else [[]]
        for m in mcases(eff):
            for d, D in enumerate(facts):
                for si, I in enumerate(disjuncts(inv, a)):
                    t = pick_of(ctx, inv, a, m, si, nxt) if nxt is not None else 0
                    out.append((j, nxt, m, d, D, si, I, t))
    return out


def obligations_of(ctx, a, inv, kinds, loops):
    """The obligations of the instruction at `a`, grouped by premises:
    [(premises, [(goal, tag)])], tag = ("inv", successor, disjunct, index) | ("loop", index)."""
    eff, st = ctx.eff[a], ctx.st[a]
    out = []
    rng = ranges_n(nvars(len(ctx.slots)))
    for _j, nxt, m, _d, D, _si, I, t in obligation_cases(ctx, a, inv, kinds):
        prem = D + wrap_prem(eff, m) + I + rng
        sigma = (lambda m: lambda v: post_s(eff, st, ctx.frame, ctx.sp.get(a), ctx.slots, m, v))(m)
        goals = []
        if nxt is not None:
            ds = disjuncts(inv, nxt)
            T = ds[t] if t < len(ds) else ds[0]
            goals += [(subst(g, sigma), ("inv", nxt, t if t < len(ds) else 0, k)) for k, g in enumerate(T)]
        goals += [(goal_lin(lc.coef(a, nxt), subst(lc.pot_at(nxt), sigma), lc.pot_at(a)), ("loop", li))
                  for li, lc in enumerate(loops)]
        out.append((prem, goals))
    return out


def picks_of(ctx, inv, kinds):
    """The certificate's `pick` field: per instruction, [j, m, d, s, t] with t != 0."""
    return [[[j, m, d, si, t] for j, _n, m, d, _D, si, _I, t in obligation_cases(ctx, a, inv, kinds) if t]
            for a in ctx.nodes]


def entails(prem, g, cert):
    """Lean `Checker.entails1`: `mu·g − Σ lam·prem` has no variable and constant ≤ 0."""
    mu, lam = cert
    if mu <= 0 or any(x < 0 for x in lam):
        return False
    d = {v: mu * k for v, k in g[0].items()}
    c = mu * g[1]
    for x, p in zip(lam, prem):
        if x:
            for v, k in p[0].items():
                d[v] = d.get(v, 0) - x * k
            c -= x * p[1]
    return all(k == 0 for k in d.values()) and c <= 0


# ----------------------------------------------------------------------------------------
# Farkas certificates

def _diff_edge(p):
    """A constraint `x_a − x_b ≤ w` as an edge (b, a, w) (ZERO: the constant)."""
    d, c = p
    items = list(d.items())
    if len(items) == 1:
        v, k = items[0]
        if k == 1:
            return (ZERO, v, -c)
        if k == -1:
            return (v, ZERO, -c)
    elif len(items) == 2:
        (v1, k1), (v2, k2) = items
        if k1 == 1 and k2 == -1:
            return (v2, v1, -c)
        if k1 == -1 and k2 == 1:
            return (v1, v2, -c)
    return None


def box_contradiction(prem):
    """Multipliers {index: k} of a contradiction among the premises `e <= 0`: a premise that
    no point of the box of the one-variable bounds satisfies, plus, for each of its
    variables, the bound that minimises it (exact, where HiGHS loses the difference of
    constants near 2^32); {} if none is found."""
    lo, hi = {}, {}         # variable -> (bound, index of the premise)
    for idx, p in enumerate(prem):
        if len(p[0]) != 1:
            continue
        (v, k), = p[0].items()
        if k == 1 and (v not in hi or -p[1] < hi[v][0]):
            hi[v] = (-p[1], idx)          # x + c <= 0: x <= -c
        elif k == -1 and (v not in lo or p[1] > lo[v][0]):
            lo[v] = (p[1], idx)           # -x + c <= 0: x >= c
    for idx, p in enumerate(prem):
        if not p[0]:
            if p[1] > 0:
                return {idx: 1}
            continue
        lam, val = {idx: 1}, p[1]
        for v, k in p[0].items():
            b = lo.get(v) if k > 0 else hi.get(v)
            if b is None:
                break
            val += k * b[0]
            lam[b[1]] = lam.get(b[1], 0) + abs(k)
        else:
            if val > 0:
                return lam
    return {}


class Prover:
    """Farkas certificates for one set of premises (the last `2·nv` are the ranges):
    shortest paths in the graph of the difference constraints on the variables that occur
    in the other premises or in the goals, a linear program otherwise."""

    def __init__(self, prem, nv, goals=()):
        self.prem, self.nv = prem, nv
        nr = len(prem) - 2 * nv
        # virtual premises: a premise on the sum of two variables (both coefficients 1 or
        # both -1) with the best bound of one of them gives a bound of the other (exact; the
        # facts of the flags of an addition are sums); `comp` maps them to real multipliers
        self.comp = {}
        ext = list(prem)
        lo, hi = {}, {}
        for idx, p in enumerate(prem):
            if len(p[0]) == 1:
                (v, k), = p[0].items()
                if k == 1 and (v not in hi or -p[1] < hi[v][0]):
                    hi[v] = (-p[1], idx)
                elif k == -1 and (v not in lo or p[1] > lo[v][0]):
                    lo[v] = (p[1], idx)
        for idx, p in enumerate(prem[:nr]):
            if len(p[0]) != 2 or len(set(p[0].values())) != 1 or abs(next(iter(p[0].values()))) != 1:
                continue
            for x, y in (tuple(p[0]), tuple(p[0])[::-1]):
                ky = p[0][y]
                b = lo.get(y) if ky == 1 else hi.get(y)
                if b is None:
                    continue
                self.comp[len(ext)] = {idx: 1, b[1]: 1}
                ext.append(({x: p[0][x]}, p[1] + ky * b[0]))
        self.ext = ext
        vs = {ZERO}
        for p in prem[:nr]:
            vs |= set(p[0])
        for g in goals:
            vs |= set(g[0])
        self.ix = {v: k for k, v in enumerate(sorted(vs))}
        n = len(self.ix)
        self.n = n
        self.edges = []
        dist = [[INF] * n for _ in range(n)]
        via = [[None] * n for _ in range(n)]
        for x in range(n):
            dist[x][x] = 0
        for idx, p in enumerate(ext):
            e = _diff_edge(p)
            if e is None or e[0] not in self.ix or e[1] not in self.ix:
                continue
            b, a, w = self.ix[e[0]], self.ix[e[1]], e[2]
            self.edges.append((b, a, w, idx))
            if w < dist[b][a]:
                dist[b][a] = w
                via[b][a] = ("e", idx)
        for k in range(n):
            dk = dist[k]
            for i in range(n):
                dik = dist[i][k]
                if dik >= INF:
                    continue
                di = dist[i]
                for j in range(n):
                    if dk[j] < INF and dik + dk[j] < di[j]:
                        di[j] = dik + dk[j]
                        via[i][j] = ("k", k)
        self.dist, self.via = dist, via
        self.neg = any(dist[x][x] < 0 for x in range(n))
        self.rng = {}
        for idx in range(nr, len(prem)):
            v, k = next(iter(prem[idx][0].items()))
            self.rng[(v, k)] = idx

    def _path(self, i, j, out, depth=0):
        if i == j or depth > 64:
            return
        w = self.via[i][j]
        if w is None:
            return
        if w[0] == "e":
            out[w[1]] = out.get(w[1], 0) + 1
        else:
            self._path(i, w[1], out, depth + 1)
            self._path(w[1], j, out, depth + 1)

    def _cycle(self, out):
        n = self.n
        dist = [0] * n
        pred = [None] * n
        last = None
        for _ in range(n):
            last = None
            for b, a, w, idx in self.edges:
                if dist[b] + w < dist[a]:
                    dist[a] = dist[b] + w
                    pred[a] = (b, idx)
                    last = a
            if last is None:
                return False
        v = last
        for _ in range(n):
            v = pred[v][0]
        start, cur = v, v
        while True:
            b, idx = pred[cur]
            out[idx] = out.get(idx, 0) + 1
            cur = b
            if cur == start:
                break
        return True

    def prove(self, g):
        d, c = g
        if not d and c <= 0:
            return (1, [])
        for idx, p in enumerate(self.prem):
            if not p[0] and p[1] > 0:
                cert = self._from_cycle(g, {idx: 1})
                if cert:
                    return cert
        if self.neg:
            cyc = {}
            if self._cycle(cyc):
                cert = self._from_cycle(g, cyc)
                if cert:
                    return cert
        box = self._box_contradiction()
        if box:
            cert = self._from_cycle(g, box)
            if cert:
                return cert
        e = _diff_edge(g)
        if e is not None and e[0] in self.ix and e[1] in self.ix:
            b, a, w = self.ix[e[0]], self.ix[e[1]], e[2]
            if self.dist[b][a] <= w:
                out = {}
                self._path(b, a, out)
                cert = self._dense(1, out)
                if entails(self.prem, g, cert):
                    return cert
        return self._lp(g)

    def _box_contradiction(self):
        if not hasattr(self, "_box"):
            self._box = box_contradiction(self.prem)
        return self._box

    def _from_cycle(self, g, cyc):
        lam = dict(cyc)
        const = sum(n * self.ext[i][1] for i, n in lam.items())
        if const <= 0:
            return None
        rest = 0
        for v, k in g[0].items():
            idx = self.rng.get((v, 1 if k > 0 else -1))
            if idx is None:
                return None
            lam[idx] = lam.get(idx, 0) + abs(k)
            rest += abs(k) * self.ext[idx][1]
        need = g[1] - rest
        K = max(1, -(-need // const)) if need > 0 else 1
        for i, n in cyc.items():
            lam[i] = lam.get(i, 0) + (K - 1) * n
        cert = self._dense(1, lam)
        return cert if entails(self.prem, g, cert) else None

    def _dense(self, mu, lam):
        real = {}
        for i, x in lam.items():
            for j, y in (self.comp[i].items() if i in self.comp else ((i, 1),)):
                real[j] = real.get(j, 0) + x * y
        n = max(real) + 1 if real else 0
        return (mu, [real.get(i, 0) for i in range(n)])

    def _lp(self, g):
        import numpy as np
        from scipy.optimize import linprog
        prem = self.prem
        # premises on the variables of the goal and of the non-range premises only
        keep = [i for i, p in enumerate(prem) if set(p[0]) <= set(self.ix) - {ZERO}]
        # and the ranges of the goal's variables (a goal follows from contradictory premises
        # only with them: the checker requires a positive multiplier of the goal)
        keep += [self.rng[(v, s)] for v in sorted(g[0]) for s in (1, -1)
                 if (v, s) in self.rng and self.rng[(v, s)] not in keep]
        vars_ = sorted(set(g[0]) | {v for i in keep for v in prem[i][0]})
        if not vars_ or not set(g[0]) <= set(vars_):
            return None
        P = len(keep)
        A_eq = np.zeros((len(vars_), P + 1))
        for r, v in enumerate(vars_):
            for col, i in enumerate(keep):
                A_eq[r, col] = prem[i][0].get(v, 0)
            A_eq[r, P] = -g[0].get(v, 0)
        A_ub = np.zeros((1, P + 1))
        for col, i in enumerate(keep):
            A_ub[0, col] = -prem[i][1]
        A_ub[0, P] = g[1]
        big = max([abs(prem[i][1]) for i in keep] + [abs(g[1]), 1])
        for margin in (max(1.0, 1e-6 * big), 0.0):
            res = linprog(np.r_[np.ones(P), 0.0], A_ub=A_ub, b_ub=[-margin], A_eq=A_eq,
                          b_eq=np.zeros(len(vars_)), bounds=[(0, None)] * P + [(1, None)], method="highs")
            if res.status != 0:
                continue
            for limit in (1, 100, 10 ** 4, 10 ** 6):
                fr = [Fraction(x).limit_denominator(limit) for x in res.x]
                D = math.lcm(*[f.denominator for f in fr])
                vals = [int(f * D) for f in fr]
                if vals[P] <= 0:
                    continue
                lam = {keep[col]: x for col, x in enumerate(vals[:P]) if x > 0}
                cert = self._dense(vals[P], lam)
                if entails(prem, g, cert):
                    return cert
            # rounding fails when multipliers are tiny (constants near 2^32): solve exactly
            # on the premises the solver used
            for tight in (True, False):
                cert = self._exact(g, [keep[col] for col in range(P) if res.x[col] > 1e-12], tight)
                if cert is not None:
                    return cert
        return None

    def _exact(self, g, S, tight):
        """Multipliers of the premises `S` with the goal's multiplier 1, by exact
        elimination (free multipliers 0; with `tight`, the constant of the combination is
        also required to be 0), scaled to integers; None if not a proof."""
        prem = self.prem
        vars_ = sorted(set(g[0]) | {v for i in S for v in prem[i][0]})
        rows = [[Fraction(prem[i][0].get(v, 0)) for i in S] + [Fraction(g[0].get(v, 0))] for v in vars_]
        if tight:
            rows.append([Fraction(prem[i][1]) for i in S] + [Fraction(g[1])])
        n, piv, r = len(S), [], 0
        for c in range(n):
            k = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
            if k is None:
                continue
            rows[r], rows[k] = rows[k], rows[r]
            p = rows[r][c]
            rows[r] = [x / p for x in rows[r]]
            for i in range(len(rows)):
                if i != r and rows[i][c] != 0:
                    f = rows[i][c]
                    rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
            piv.append(c)
            r += 1
        if any(all(x == 0 for x in row[:n]) and row[n] != 0 for row in rows):
            return None
        lamf = [Fraction(0)] * n
        for i, c in enumerate(piv):
            lamf[c] = rows[i][n]
        if any(x < 0 for x in lamf):
            return None
        D = math.lcm(*[x.denominator for x in lamf])
        lam = {S[c]: int(x * D) for c, x in enumerate(lamf) if x > 0}
        cert = self._dense(D, lam)
        return cert if entails(prem, g, cert) else None


# ----------------------------------------------------------------------------------------
# The analysis: zones on the registers, the ghosts and the tracked words of the frame
# (analysis variable 10 + j is the word j, certificate variable 20 + j; the last index is
# the zero node)

class Zones:
    def __init__(self, S):
        self.S = S
        self.n = 11 + S          # 0-7, 8-9, slots, zero
        self.Z = 10 + S

    def top(self):
        n, Z = self.n, self.Z
        M = [[INF] * n for _ in range(n)]
        for x in range(n):
            M[x][x] = 0
        for v in range(n - 1):
            M[v][Z] = U - 1
            M[Z][v] = 0
        return M

    def close(self, M):
        n = self.n
        for k in range(n):
            Mk = M[k]
            for i in range(n):
                mik = M[i][k]
                if mik >= INF:
                    continue
                Mi = M[i]
                for j in range(n):
                    if Mk[j] < INF and mik + Mk[j] < Mi[j]:
                        Mi[j] = mik + Mk[j]
        if any(M[x][x] < 0 for x in range(n)):
            return None
        return M

    def lohi(self, M, v):
        return -M[self.Z][v], M[v][self.Z]

    def add_edge(self, M, a, b, w):
        """The closure of the closed zone `M` with `x_a - x_b <= w` added, in O(n^2)
        (incremental closure: a shortest path uses the new edge at most once); None if
        empty. `M` is changed in place."""
        if w >= M[a][b]:
            return M
        n = self.n
        if w + M[b][a] < 0:
            return None
        col = [M[i][a] for i in range(n)]
        Mb = M[b][:]
        for i in range(n):
            ia = col[i]
            if ia >= INF:
                continue
            base = ia + w
            Mi = M[i]
            for j in range(n):
                bj = Mb[j]
                if bj < INF and base + bj < Mi[j]:
                    Mi[j] = base + bj
        return M

    def checked(self, fast, slow_input):
        """With CHECK_CLOSE: `fast` must equal the full closure of `slow_input`."""
        if CHECK_CLOSE:
            slow = self.close(copy(slow_input)) if slow_input is not None else None
            if slow != fast:
                raise AssertionError("zone closure shortcut differs from the full closure")
        return fast


def copy(M):
    return [row[:] for row in M]


def join(A, B):
    if A is None:
        return copy(B) if B is not None else None
    if B is None:
        return copy(A)
    return [[max(a, b) for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def leq(A, B):
    if A is None:
        return True
    if B is None:
        return False
    return all(a <= b for ra, rb in zip(A, B) for a, b in zip(ra, rb))


def widen(old, new, thresholds):
    if old is None:
        return new
    out = copy(new)
    for i in range(len(new)):
        for j in range(len(new)):
            if new[i][j] > old[i][j]:
                out[i][j] = next((t for t in thresholds if t >= new[i][j]), INF)
    return out


def forget_growing(old, new):
    """`new` (closed, above `old`) with, for every entry above `old`, the upper bounds of
    its first variable (row) and the lower bounds of its second (column) dropped: still
    closed, and each call that changes anything drops a finite entry of `old`, so
    widening followed by closure, which may creep up forever (a closure tightens the
    widened entries again), stops."""
    n = len(new)
    grow = [(i, j) for i in range(n) for j in range(n) if new[i][j] > old[i][j]]
    if not grow:
        return new
    out = copy(new)
    for i, j in grow:
        for k in range(n):
            if k != i:
                out[i][k] = INF
            if k != j:
                out[k][j] = INF
    return out


def guard(Zd, M, p, closed=False):
    """Adds the constraint `p` (over the ghosts 8, 9) to a zone (closed if `closed`):
    (zone or None if empty, whether it is closed)."""
    M0 = M
    M = copy(M)
    d, c = p
    Z = Zd.Z
    e = _diff_edge(p)
    if e is not None:
        b, a, w = e
        b = Z if b == ZERO else b
        a = Z if a == ZERO else a
        edges = [(a, b, w)]
    elif set(d) == {8, 9} and d[8] == d[9] and abs(d[8]) == 1:
        l8, h8 = Zd.lohi(M, 8)
        l9, h9 = Zd.lohi(M, 9)
        if d[8] == 1:
            edges = [(8, Z, -c - l9), (9, Z, -c - l8)]
        else:
            edges = [(Z, 8, h9 - c), (Z, 9, h8 - c)]
    else:
        return M, closed
    if not closed:
        for a, b, w in edges:
            M[a][b] = min(M[a][b], w)
        return Zd.close(M), True
    # both weights are computed on the zone before the first edge, as in the full closure
    for a, b, w in edges:
        M = Zd.add_edge(M, a, b, w)
        if M is None:
            break
    if M is not None and any(M[x][x] < 0 for x in range(Zd.n)):
        M = None
    if CHECK_CLOSE:
        slow = copy(M0)
        for a, b, w in edges:
            slow[a][b] = min(slow[a][b], w)
        if Zd.close(slow) != M:
            raise AssertionError("incremental closure differs from the full closure")
    return M, True


def post_exprs(ctx, a, M):
    """For each analysis variable, its value after the instruction at `a` as ("shift", w,
    c) (`w + c`, w an analysis variable or the zero node) or "any", from the zone `M`
    before it (a sum or difference only when no wrap is possible)."""
    Zd, eff, st = ctx.zones, ctx.aeff[a], ctx.st[a]
    Z = Zd.Z
    dst, fl = eff
    _sp, mem, load, _e = st
    delta = ctx.sp.get(a)
    out = {}
    first = {}
    for r, v in dst:
        first.setdefault(r, v)
    for r in range(8):
        v = first.get(r)
        if v is None:
            out[r] = ("shift", r, 0)
        elif v == "any":
            out[r] = "any"
        else:
            op, x, y = v
            if op == "shl":
                # a constant only when the register holds one and no overflow
                l, hh = Zd.lohi(M, x[1])
                val = l << y if l == hh else None
                out[r] = ("shift", Z, val) if val is not None and 0 <= val <= BIG else "any"
            elif x[0] == "imm" and y[0] == "imm":
                val = x[1] + y[1] if op == "add" else x[1] - y[1]
                # constants above BIG (addresses from the literal pool) are not tracked:
                # with them, HiGHS fails numerically on the linear programs (untrusted choice)
                out[r] = ("shift", Z, val) if 0 <= val <= BIG else "any"
            elif x[0] == "reg" and y[0] == "imm":
                k = y[1] if op == "add" else -y[1]
                l, h = Zd.lohi(M, x[1])
                out[r] = ("shift", x[1], k) if l + k >= 0 and h + k <= U - 1 else "any"
            elif x[0] == "imm" and y[0] == "reg" and op == "sub":
                # NEGS, MVNS: a constant only when the register holds one
                l, h = Zd.lohi(M, y[1])
                out[r] = ("shift", Z, (x[1] - l) % U) if l == h else "any"
            else:
                out[r] = "any"
    if load is not None and delta is not None:
        j = slot_idx(ctx.slots, -(delta + load[1]))
        if j is not None:
            out[load[0]] = ("shift", 10 + j, 0)
    for gv, idx in ((8, 1), (9, 2)):
        if fl == "keep":
            out[gv] = ("shift", gv, 0)
        elif fl == "any":
            out[gv] = "any"
        else:
            sv = fl[idx]
            out[gv] = ("shift", sv[1], 0) if sv[0] == "reg" else ("shift", Z, sv[1])
    for jj, k in enumerate(ctx.slots):
        x = 10 + jj
        if mem == "keep":
            out[x] = ("shift", x, 0)
        elif mem[0] == "store":
            if delta is None:
                out[x] = "any"
            else:
                out[x] = ("shift", mem[2], 0) if k == -(delta + mem[1]) else ("shift", x, 0)
        elif mem[0] == "push":
            out[x] = "any" if delta is None or delta - 4 * mem[1] <= -k < delta else ("shift", x, 0)
        else:
            out[x] = ("shift", x, 0) if (delta is not None and ctx.frame and k <= -delta) else "any"
    return out


def apply_post(Zd, M, ex, closed=False):
    """The zone after the instruction: the image of `M` by the post-expressions, closed.
    If `M` is closed and every expression stays in [0, 2^32) on it, the image of the
    variables that are not "any" is closed already (a closed zone renamed and shifted),
    and the closure only adds, for a variable `a` with any value, `a - y <= U - 1 + N[Z][y]`
    and `y - a <= N[y][Z]` (paths through the zero node); otherwise the full closure."""
    n, Z = Zd.n, Zd.Z
    N = Zd.top()
    ex = dict(ex)
    ex[Z] = ("shift", Z, 0)
    fast = closed and all(
        e == "any" or (M[e[1]][Z] + e[2] <= U - 1 and M[Z][e[1]] - e[2] <= 0)
        for x, e in ((x, ex.get(x, "any")) for x in range(n)) if x != Z)
    for x in range(n):
        ex_x = ex.get(x, "any")
        if ex_x == "any":
            continue
        _, wx, cx = ex_x
        for y in range(n):
            ex_y = ex.get(y, "any")
            if ex_y == "any" or x == y:
                continue
            _, wy, cy = ex_y
            b = M[wx][wy]
            if b < INF:
                N[x][y] = min(N[x][y], b + cx - cy)
    if not fast:
        return Zd.close(N)
    anyv = [x for x in range(n) if x != Z and ex.get(x, "any") == "any"]
    if anyv:
        NZ = N[Z]
        colZ = [N[y][Z] for y in range(n)]
        for a in anyv:
            Na = N[a]
            for y in range(n):
                if y != a:
                    if NZ[y] < INF and U - 1 + NZ[y] < Na[y]:
                        Na[y] = U - 1 + NZ[y]
                    if colZ[y] < INF and colZ[y] < N[y][a]:
                        N[y][a] = colZ[y]
    if CHECK_CLOSE and Zd.close(copy(N)) != N:
        raise AssertionError("image of a closed zone is not closed")
    return N


class Ctx:
    def __init__(self, an, name, abi, frame=False, lit_any=False):
        self.an, self.name, self.abi = an, name, abi
        mem = an.img.mem
        self.get = lambda a: (int.from_bytes(mem[a:a + 2], "little") if 0 <= a and a + 2 <= len(mem) else None)
        (self.entry, self.blocks, self.succ, self.back, self.loops, self.headers,
         self.bound) = structure(an, name)
        self.jumps = an.jumps.get(name, {})   # jumps through tables (jumptable.py)
        insns = sorted((i for il in self.blocks.values() for i in il), key=lambda i: i.addr)
        self.nodes = [i.addr for i in insns]
        self.insn = {i.addr: i for i in insns}
        top = ipet.code_top(an.img)
        # the checker sees only the code region of the certificate (literal loads beyond it: any)
        cget = lambda a: self.get(a) if a + 2 <= top else None  # noqa: E731
        self.eff = {a: effect(abi, cget, a) for a in self.nodes}
        # the effects used by the producer's own analysis (zones, congruences, linear
        # programs): with `lit_any`, literal loads and shifts give any value, as before
        # 2026-11-19
        self.aeff = dict(self.eff)
        if lit_any:
            for a in self.nodes:
                h = self.get(a)
                if h >> 11 == 0b01001:
                    self.aeff[a] = ([((h >> 8) % 8, "any")], "keep")
                elif any(v != "any" and v[0] == "shl" for _r, v in self.eff[a][0]):
                    self.aeff[a] = ([(r, "any" if v != "any" and v[0] == "shl" else v)
                                     for r, v in self.eff[a][0]], self.eff[a][1])
        self.st = {a: stack_effect(abi, self.get, a) for a in self.nodes}
        self.cc = {a: (self.get(a) >> 8) % 16 for a in self.nodes}
        self.out = {a: ipet.trans(self.insn[a], self.jumps) for a in self.nodes}
        self.frame = frame and all(frame_use_ok(self, a) for a in self.nodes)
        self.iloops = []
        for h in self.headers:
            body = sorted(i.addr for b in self.loops[h] for i in self.blocks[b])
            self.iloops.append((h, body, self.bound.get(h)))
        self.sp = sp_offsets(self)
        # tracked words: those accessed through SP inside a loop, at a known offset
        inloop = {a for _h, b, _n in self.iloops for a in b}
        slots = set()
        for a in inloop:
            d = self.sp.get(a)
            _sp, m, ld, _e = self.st[a]
            for imm in ([ld[1]] if ld else []) + ([m[1]] if m not in ("keep", "other") and m[0] == "store" else []):
                if d is not None:
                    k = -(d + imm)
                    if 0 < k < 1048576 and k % 4 == 0:
                        slots.add(k)
        self.slots = sorted(slots)
        self.zones = Zones(len(self.slots))
        self.cong = None
        imms = {0, 1, U - 1}
        for a in self.nodes:
            for _r, v in self.aeff[a][0]:
                if v != "any":
                    for x in val_srcs(v):
                        if x[0] == "imm":
                            imms |= {x[1], x[1] - 1, x[1] + 1}
            fl = self.eff[a][1]
            if fl not in ("keep", "any"):
                for x in fl[1:]:
                    if x[0] == "imm":
                        imms |= {x[1], x[1] - 1, x[1] + 1}
        # the wrap-around boundaries of the additions of a constant (x + k wraps from x = U - k):
        # loops that leave when such a sum wraps to zero need them for widening
        for a in self.nodes:
            w = wrap_op(self.aeff[a])
            if w is not None and w[2] > 0:
                imms |= {U - w[2] - 1, U - w[2], U - w[2] + 1}
        thr = {t for t in imms if 0 <= t < U} | {U - 1}
        self.thresholds = sorted(thr | {-t for t in thr})


def sp_offsets(ctx):
    """The offset of SP from its value at the entry, per instruction (None: unknown)."""
    sp = {ctx.entry: 0}
    known = dict(sp)
    work = [ctx.entry]
    bad = set()
    while work:
        a = work.pop()
        d = known.get(a)
        e = ctx.st[a][0]
        nd = None
        if d is not None and a not in bad:
            nd = d if e == "keep" else (d + e[1] if e != "any" else None)
        for n, _w, _c in ctx.out[a]:
            if n is None:
                continue
            if n not in known:
                known[n] = nd
                work.append(n)
            elif known[n] != nd and n not in bad:
                bad.add(n)
                known[n] = None
                work.append(n)
    return {a: (d if d is not None and a not in bad and -1048576 <= d <= 1048576 else None)
            for a, d in known.items()}


def kinds_of(ctx):
    kind = {ctx.entry: "none"}
    changed = True
    while changed:
        changed = False
        for a in ctx.nodes:
            if a not in kind:
                continue
            fl = ctx.eff[a][1]
            k = kind[a] if fl == "keep" else ("none" if fl == "any" else fl[0])
            for n, _w, _c in ctx.out[a]:
                if n is None:
                    continue
                new = k if n not in kind else (kind[n] if kind[n] == k else "none")
                if n not in kind or new != kind[n]:
                    kind[n] = new
                    changed = True
    return kind


def transfer(ctx, kind, a, M):
    """[(j, zone with the facts before the effect, post-expressions, zone after)]."""
    Zd = ctx.zones
    i = ctx.insn[a]
    res = []
    # every stored zone is closed except the first state of the entry (`top`)
    closed = a != ctx.entry
    for j, (nxt, _w, _cs) in enumerate(ctx.out[a]):
        facts = cond_facts(kind.get(a, "none"), ctx.cc[a], j == 0, cmod(ctx.cong, a)) if i.kind == "cond" else [[]]
        for D in facts:
            Mf, cl = M, closed
            for p in D:
                if Mf is not None:
                    Mf, cl = guard(Zd, Mf, p, closed=cl)
            if Mf is None:
                continue
            ex = post_exprs(ctx, a, Mf)
            if nxt is not None and kind.get(nxt, "none") == "none":
                ex[8] = ex[9] = "any"
            post = apply_post(Zd, Mf, ex, closed=cl)
            res.append((j, Mf, ex, post))
    return res


# ----------------------------------------------------------------------------------------
# Disjunctions at a wrap-around (trace partitioning, Mauborgne & Rival 2005, limited to a
# straight line): an addition or subtraction of a constant that may wrap splits the zone
# into the case without and the case with wrap-around; the two are carried separately to
# the next conditional branch and joined after it. The instructions of the window get
# disjunctive invariants in the certificate (`alt`, targets `pick`), checked by Lean.

def wrap_op(eff):
    """(register written, source register, signed constant) of `rd = rn ± imm`, else None."""
    o = op_of(eff)
    if o is None:
        return None
    r, v = o
    if v == "any" or v[0] not in ("add", "sub") or v[1][0] != "reg" or v[2][0] != "imm" or v[2][1] == 0:
        return None     # (a move, `rn + 0`, never wraps)
    return r, v[1][1], v[2][1] if v[0] == "add" else -v[2][1]


def windows_of(ctx):
    """{start: [instructions up to and including the next conditional branch]}: from an
    instruction `rd = rn ± imm` with one successor, the straight line of instructions with
    one predecessor each, none a loop header, ending at a conditional branch."""
    preds = {a: 0 for a in ctx.nodes}
    for a in ctx.nodes:
        for n, _w, _c in ctx.out[a]:
            if n in preds:
                preds[n] += 1
    heads = {h for h, _b, _n in ctx.iloops}
    W = {}
    for a in ctx.nodes:
        if (a == ctx.entry or ctx.insn[a].kind == "cond" or len(ctx.out[a]) != 1
                or wrap_op(ctx.aeff[a]) is None):
            continue
        chain, n = [], ctx.out[a][0][0]
        while n is not None and n in preds and preds[n] == 1 and n not in heads and len(chain) < 6:
            chain.append(n)
            if ctx.insn[n].kind == "cond":
                break
            if len(ctx.out[n]) != 1:
                break
            n = ctx.out[n][0][0]
        if chain and ctx.insn[chain[-1]].kind == "cond":
            W[a] = chain
    inner = {n for ch in W.values() for n in ch}
    return {a: ch for a, ch in W.items() if a not in inner}


def window_transfer(ctx, kind, a, M):
    """The zones of the window starting at `a` from the closed zone `M`: ({instruction:
    [(tag, zone)]}, {transition of the branch: joined zone}); tag 0: no wrap-around at
    `a`, tag 1: wrap-around."""
    Zd = ctx.zones
    Z = Zd.Z
    r, x, k = wrap_op(ctx.aeff[a])
    chain = ctx.windows[a]
    parts = []
    lo_ok = Zd.add_edge(copy(M), Z, x, k)               # x + k >= 0
    if lo_ok is not None:
        lo_ok = Zd.add_edge(lo_ok, x, Z, U - 1 - k)     # x + k <= U - 1
    parts.append((0, lo_ok, k))
    if k < 0:
        parts.append((1, Zd.add_edge(copy(M), x, Z, -k - 1), k + U))   # x + k < 0
    elif k > 0:
        parts.append((1, Zd.add_edge(copy(M), Z, x, k - U), k - U))    # x + k >= U
    nxt = ctx.out[a][0][0]
    cur = []
    for tag, Mi, shift in parts:
        if Mi is None:
            continue
        ex = post_exprs(ctx, a, Mi)
        ex[r] = ("shift", x, shift)
        if kind.get(nxt, "none") == "none":
            ex[8] = ex[9] = "any"
        post = apply_post(Zd, Mi, ex, closed=True)
        if post is not None:
            cur.append((tag, post))
    disj, outs = {}, {}
    for idx, n in enumerate(chain):
        disj[n] = cur
        nxt_cur = []
        for tag, Zn in cur:
            for j, _Mf, _ex, post in transfer(ctx, kind, n, Zn):
                if post is None:
                    continue
                if idx == len(chain) - 1:
                    outs[j] = join(outs.get(j), post)
                else:
                    nxt_cur.append((tag, post))
        cur = nxt_cur
    return disj, outs


def hull(parts):
    out = None
    for _tag, Zn in parts:
        out = join(out, Zn)
    return out


def analyse(ctx, kind):
    Zd = ctx.zones
    state = {a: None for a in ctx.nodes}
    state[ctx.entry] = Zd.top()
    heads = {h for h, _b, _n in ctx.iloops}
    order = {a: k for k, a in enumerate(ctx.nodes)}
    if getattr(ctx, "windows", None) is None:
        ctx.windows = windows_of(ctx) if DISJ else {}
    inner = {n for ch in ctx.windows.values() for n in ch}
    ctx.disj = {}

    def steps(a, M, into):
        """[(successor transition source, j, post)], the window's zones stored in `into`."""
        if a in ctx.windows:
            disj, outs = window_transfer(ctx, kind, a, M)
            for n, parts in disj.items():
                ctx.disj[n] = parts
                into[n] = hull(parts)
            b = ctx.windows[a][-1]
            return [(b, j, post) for j, post in outs.items()]
        return [(a, j, post) for j, _Mf, _ex, post in transfer(ctx, kind, a, M)]

    work = [ctx.entry]
    visits = {}
    while work:
        _tick()
        work.sort(key=lambda x: order[x])
        a = work.pop(0)
        M = state[a]
        if M is None or a in inner:
            continue
        for src, j, post in steps(a, M, state):
            n = ctx.out[src][j][0]
            if n is None or post is None:
                continue
            new = join(state[n], post)
            widened = False
            if n in heads:
                visits[n] = visits.get(n, 0) + 1
                if visits[n] > 2:
                    new = widen(state[n], new, ctx.thresholds)
                    widened = True
            if new is not None and (widened or n == ctx.entry):
                new = Zd.close(new)
                if widened and visits[n] > HARD_VISITS and new is not None and state[n] is not None:
                    new = forget_growing(state[n], new)
            elif new is not None:
                new = Zd.checked(new, new)   # a join of closed zones is closed
            if not leq(new, state[n]):
                state[n] = new
                if n not in work:
                    work.append(n)
    for _ in range(3):
        new = {a: None for a in ctx.nodes}
        new[ctx.entry] = Zd.top()
        ctx.disj = {}
        for a in ctx.nodes:
            if state[a] is None or a in inner:
                continue
            for src, j, post in steps(a, state[a], new):
                n = ctx.out[src][j][0]
                if n is not None and post is not None:
                    new[n] = join(new[n], post)
        state = {a: (None if m is None else Zd.close(m) if a == ctx.entry else Zd.checked(m, m))
                 for a, m in new.items()}
    return state


# ----------------------------------------------------------------------------------------
# Potentials (over analysis variables)

def bound_of(Zd, M, phi):
    """Upper bound of `Σ k·x_v` (k = ±1 on at most two variables) on a zone."""
    Z = Zd.Z
    items = list(phi.items())
    if len(items) == 1:
        v, k = items[0]
        return M[v][Z] if k == 1 else M[Z][v]
    (v1, k1), (v2, k2) = items
    if k1 == 1 and k2 == -1:
        return M[v1][v2]
    if k1 == -1 and k2 == 1:
        return M[v2][v1]
    return INF


def delta_phi(Zd, phi, ex, Mf):
    """Upper bound of φ(after) − φ(before) on the zone `Mf` before the instruction."""
    total = 0
    for v, k in phi.items():
        e = ex.get(v, "any")
        if e == "any":
            return INF
        _, w, c = e
        if w == v:
            total += k * c
        else:
            b = (Mf[w][v] + c) if k == 1 else (Mf[v][w] - c)
            if b >= INF // 2:
                return INF
            total += b
    return total


def synth(ctx, kind, state, h, body, cache):
    """The best potential of the loop at `h`: (N, [potentials], D) or None."""
    Zd = ctx.zones
    B = set(body)
    nv = 10 + len(ctx.slots)
    cands = []
    for r in list(range(8)) + list(range(10, nv)):
        cands += [{r: 1}, {r: -1}]
    for a in body:
        M = state[a]
        if M is None or ctx.insn[a].kind != "cond" or kind.get(a, "none") == "none":
            continue
        ra = [r for r in list(range(8)) + list(range(10, nv)) if M[8][r] == 0 and M[r][8] == 0]
        rb = [r for r in list(range(8)) + list(range(10, nv)) if M[9][r] == 0 and M[r][9] == 0]
        for r in ra:
            for q in rb:
                if r != q:
                    for phi in ({r: 1, q: -1}, {r: -1, q: 1}):
                        if phi not in cands:
                            cands.append(phi)
    best = None
    for phi in cands:
        for D in (1, 2, 4, 8):
            cmin = {a: -INF for a in body}
            edges = []
            entry_terms = []
            ok = True
            for a in ctx.nodes:
                if state[a] is None:
                    continue
                for j, Mf, ex, post in cache[a]:
                    n = ctx.out[a][j][0]
                    if a in B:
                        if n is not None and n in B:
                            dl = delta_phi(Zd, phi, ex, Mf)
                            if dl >= INF // 2:
                                ok = False
                                break
                            edges.append((a, n, (D if n == h else 0) + dl))
                        else:
                            mb = bound_of(Zd, Mf, {v: -k for v, k in phi.items()})
                            if mb >= INF // 2:
                                ok = False
                                break
                            cmin[a] = max(cmin[a], mb)
                    elif n == h:
                        if post is None:
                            continue
                        mb = bound_of(Zd, post, phi)
                        if mb >= INF // 2:
                            ok = False
                            break
                        entry_terms.append(mb)
                if not ok:
                    break
            if not ok:
                break
            c = dict(cmin)
            stable = False
            for _ in range(len(body) + 2):
                changed = False
                for a, n, w in edges:
                    if c[n] > -INF and c[n] + w > c[a]:
                        c[a] = c[n] + w
                        changed = True
                if not changed:
                    stable = True
                    break
            if not stable or any(c[a] <= -INF for a in body):
                continue
            if h == ctx.entry:
                entry_terms.append(bound_of(Zd, Zd.top(), phi))
            N = max(0, max([c[h] + t for t in entry_terms], default=0))
            if best is None or Fraction(N, D) < Fraction(best[0], best[2]):
                cphi = {(v if v < 10 else 20 + (v - 10)): k for v, k in phi.items()}
                best = (N, [padd((dict(cphi), 0), pconst(c[a])) for a in body], D)
    return best


def _cv(v):
    """Analysis variable -> variable of the certificate."""
    return v if v < 10 else 20 + (v - 10)


def _zone_range(Zd, M, d, c):
    """[min, max] of `Σ d·x + c` (certificate variables, coefficients ±1, at most two of
    them, a difference if two) on the zone `M`; None if not of that form."""
    Z = Zd.Z
    # only variables of the state before the instruction: r0-r7, ghosts, tracked words
    if any((10 <= v < 20 or v >= 10 + Z) and k for v, k in d.items()):
        return None
    av = {(v if v < 20 else 10 + (v - 20)): k for v, k in d.items() if k}
    if any(abs(k) != 1 for k in av.values()):
        return None
    if not av:
        return c, c
    if len(av) == 1:
        (v, k), = av.items()
        lo, hi = Zd.lohi(M, v)
        return (c + lo, c + hi) if k == 1 else (c - hi, c - lo)
    if len(av) == 2 and sorted(av.values()) == [-1, 1]:
        x = next(v for v, k in av.items() if k == 1)
        y = next(v for v, k in av.items() if k == -1)
        return c - M[y][x], c + M[x][y]
    return None


def _follow(ctx, state, a, v):
    """A variable `w` whose value after the instruction at `a` is the value of `v` before
    it plus a constant, in every disjunct of the zone at `a` and every possible wrap-around
    case (exact, on the checker's post-expressions); `v` itself if possible; None if none."""
    Zd = ctx.zones
    eff, st = ctx.eff[a], ctx.st[a]
    zones = [Zn for _t, Zn in ctx.disj[a]] if a in getattr(ctx, "disj", {}) else [state[a]]
    cases = []
    for Za in zones:
        for m in mcases(eff):
            prem = wrap_prem(eff, m)
            if any((r := _zone_range(Zd, Za, p[0], p[1])) is not None and r[0] > 0 for p in prem):
                continue
            cases.append((Za, m))
    nv = 10 + len(ctx.slots)
    for w in [v] + [u for u in range(nv) if u != v]:
        diff = None
        for Za, m in cases:
            e = post_s(eff, st, ctx.frame, ctx.sp.get(a), ctx.slots, m, _cv(w))
            d = dict(e[0])
            d[_cv(v)] = d.get(_cv(v), 0) - 1
            r = _zone_range(Zd, Za, d, e[1])
            if r is None or r[0] != r[1] or (diff is not None and r[0] != diff):
                break
            diff = r[0]
        else:
            if cases:
                return w
    return None


def transport(ctx, state, h, body, r):
    """Linear parts {instruction: analysis variable} that follow the variable `r` of the
    header through the loop's body (`_follow`), or None."""
    Bs = set(body)
    lin, order, k = {h: r}, [h], 0
    while k < len(order):
        a = order[k]
        k += 1
        if state[a] is None:
            return None
        w = None
        for n, _w, _c in ctx.out[a]:
            if n is None or n not in Bs or n == h:
                continue
            if w is None:
                w = _follow(ctx, state, a, lin[a])
                if w is None:
                    return None
            if n in lin:
                if lin[n] != w:
                    return None
                continue
            lin[n] = w
            order.append(n)
    return lin if len(lin) == len(Bs) else None


def synth_transport(ctx, kind, state, h, body, lin, sgn):
    """The constants of the potentials `sgn · lin[a] + c_a` by longest paths, as in `synth`,
    with the transitions of the instructions of a window taken from each of their disjuncts
    (the hull loses the relation between the counter and its copy): (N, [potentials], D)
    or None. Used when the linear program fails on the constants (they may be near 2^32)."""
    Zd = ctx.zones
    B = set(body)
    disj = getattr(ctx, "disj", {})

    def sup_diff(Mf, ex, w, v):
        e = ex.get(w, "any")
        if e == "any":
            return INF
        _, u, c = e
        b = (Mf[u][v] + c) if sgn == 1 else (Mf[v][u] - c)
        return INF if b >= INF // 2 else b

    steps = []
    for a in ctx.nodes:
        if state[a] is None:
            continue
        zones = [Zn for _t, Zn in disj[a]] if a in B and a in disj else [state[a]]
        for Za in zones:
            steps += [(a, j, Mf, ex, post) for j, Mf, ex, post in transfer(ctx, kind, a, Za)]
    best = None
    for D in (1, 2, 4, 8):
        cmin = {a: -INF for a in body}
        edges, entry_terms, ok = [], [], True
        for a, j, Mf, ex, post in steps:
            n = ctx.out[a][j][0]
            if a in B:
                if n is not None and n in B:
                    dl = sup_diff(Mf, ex, lin[n], lin[a])
                    if dl >= INF:
                        ok = False
                        break
                    edges.append((a, n, (D if n == h else 0) + dl))
                else:
                    mb = bound_of(Zd, Mf, {lin[a]: -sgn})
                    if mb >= INF // 2:
                        ok = False
                        break
                    cmin[a] = max(cmin[a], mb)
            elif n == h and post is not None:
                mb = bound_of(Zd, post, {lin[h]: sgn})
                if mb >= INF // 2:
                    ok = False
                    break
                entry_terms.append(mb)
        if not ok:
            return None
        c = dict(cmin)
        stable = False
        for _ in range(len(body) + 2):
            changed = False
            for a, n, w in edges:
                if c[n] > -INF and c[n] + w > c[a]:
                    c[a] = c[n] + w
                    changed = True
            if not changed:
                stable = True
                break
        if not stable or any(c[a] <= -INF for a in body):
            continue
        if h == ctx.entry:
            entry_terms.append(bound_of(Zd, Zd.top(), {lin[h]: sgn}))
        N = max(0, max([c[h] + t for t in entry_terms], default=0))
        if best is None or Fraction(N, D) < Fraction(best[0], best[2]):
            best = (N, [padd(({_cv(lin[a]): sgn}, 0), pconst(c[a])) for a in body], D)
    return best


def synth_lp(ctx, kind, inv, h, body, coarse=False, fixed=None):
    """A potential per instruction of the loop, each with its own linear part, found by one
    linear program over the checker's own obligations (the potentials and the Farkas
    multipliers are the unknowns: Colon & Sipma 2001, Podelski & Rybalchenko 2004, and
    per control point as in Alias, Darte, Feautrier & Gonnord 2010). Needed when the counter
    moves between a register and a word of the frame inside the loop. The potentials are rounded to rationals and proved again
    by `prove_all` (whatever this finds is checked). Returns candidates [(N, [potentials], D)]
    (the tightest bound first), [] if none.

    `coarse`: constants above `BIG` (addresses and other words from the literal pool) make
    HiGHS fail numerically; in this mode a register given such a constant is treated as
    written with any value, and the invariant constraints with such constants are left
    out. A potential found this way satisfies the exact obligations too (they have more
    premises, and the value written is one of the values allowed); `prove_all` checks it."""
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix
    B = set(body)
    S = len(ctx.slots)
    nv = nvars(S)
    rng = ranges_n(nv)
    V = list(range(10)) + [20 + j for j in range(S)]
    col = {}

    def var(key):
        if key not in col:
            col[key] = len(col)
        return col[key]

    NB = var("N")
    for a in body:
        for v in V:
            var(("p", a, v))
        var(("c", a))
    eq_rows, ub_rows = [], []    # rows: ({column: coefficient}, rhs)
    # the same constant rows with every constant split as q * 2^31 + r, |r| <= 2^30, and
    # the two parts required separately (stronger, well scaled: tried when HiGHS fails)
    split_rows = []

    def add_oblig(prem, gd, gc):
        # gd: {program variable: {column: coef}}, gc: ({column: coef}, constant)
        # exists lam >= 0: gd[u] = sum lam_i prem_i[u], gc - sum lam_i c_i <= 0
        used = set(gd)
        main = [p for p in prem[:len(prem) - len(rng)]]
        for p in main:
            used |= set(p[0])
        ps = main + [r for r in rng if set(r[0]) <= used]
        lam = [var(("l", len(col))) for _ in ps]
        for u in used:
            row = dict(gd.get(u, {}))
            for li, p in zip(lam, ps):
                k = p[0].get(u, 0)
                if k:
                    row[li] = row.get(li, 0) - k
            if row:
                eq_rows.append((row, 0.0))
        row = dict(gc[0])
        for li, p in zip(lam, ps):
            if p[1]:
                row[li] = row.get(li, 0) - p[1]
        ub_rows.append((row, -gc[1]))
        hi_row, lo_row = {}, dict(gc[0])
        for li, p in zip(lam, ps):
            q, r = divmod(p[1] + (1 << 30), 1 << 31)
            r -= 1 << 30
            if q:
                hi_row[li] = -q
            if r:
                lo_row[li] = lo_row.get(li, 0) - r
        if hi_row:
            split_rows.append((hi_row, 0.0))
        split_rows.append((lo_row, -gc[1]))

    for a in ctx.nodes:
        i, eff, st = ctx.insn[a], ctx.aeff[a], ctx.st[a]
        ka = kind.get(a, "none")
        for j, (nxt, _w, _cs) in enumerate(ipet.trans(i, ctx.jumps)):
            if a not in B and nxt not in B:
                continue
            facts = cond_facts(ka, ctx.cc[a], j == 0, cmod(ctx.cong, a)) if i.kind == "cond" else [[]]
            for m in mcases(eff):
                sig = {v: post_s(eff, st, ctx.frame, ctx.sp.get(a), ctx.slots, m, v) for v in V}
                ias, wp = disjuncts(inv, a), wrap_prem(eff, m)
                if coarse:
                    wp = [g for g in wp if g[0] or abs(g[1]) <= BIG]
                    sig = {v: (pv(10 + v) if v < 8 and not e[0] and abs(e[1]) > BIG else e) for v, e in sig.items()}
                    ias = [[g for g in ia if abs(g[1]) <= BIG] for ia in ias]
                for D, ia in ((D, ia) for D in facts for ia in ias):
                    prem = D + wp + ia + rng
                    if box_contradiction(prem):
                        continue        # a case that cannot happen: no constraint
                    gd, gcc, gk = {}, {}, 0
                    if nxt == h:
                        if a in B:
                            gk += 1
                        else:
                            gcc[NB] = gcc.get(NB, 0) - 1
                    if nxt in B:
                        for v in V:
                            pc = col[("p", nxt, v)]
                            dv, cv = sig[v]
                            for u, k in dv.items():
                                gd.setdefault(u, {})
                                gd[u][pc] = gd[u].get(pc, 0) + k
                            if cv:
                                gcc[pc] = gcc.get(pc, 0) + cv
                        cc_ = col[("c", nxt)]
                        gcc[cc_] = gcc.get(cc_, 0) + 1
                    if a in B:
                        for v in V:
                            pc = col[("p", a, v)]
                            gd.setdefault(v, {})
                            gd[v][pc] = gd[v].get(pc, 0) - 1
                        cc_ = col[("c", a)]
                        gcc[cc_] = gcc.get(cc_, 0) - 1
                    add_oblig(prem, gd, (gcc, gk))
    if ctx.entry == h:
        gd = {}
        for v in V:
            gd.setdefault(v, {})[col[("p", h, v)]] = 1
        add_oblig(list(rng), gd, ({col[("c", h)]: 1, NB: -1}, 0))
    n = len(col)

    def mat(rows):
        r, c, d = [], [], []
        for k, (row, _b) in enumerate(rows):
            for cc_, x in row.items():
                r.append(k)
                c.append(cc_)
                d.append(float(x))
        return coo_matrix((d, (r, c)), shape=(len(rows), n)).tocsr(), np.array([b for _r, b in rows])

    Aeq, beq = mat(eq_rows)
    Aub, bub = mat(ub_rows)
    Asp, bsp = mat(split_rows)
    bounds = [(None, None)] * n
    for key, k in col.items():
        if key == "N":
            bounds[k] = (0, None)
        elif key[0] == "p":
            # with `fixed` = (linear parts, sign): those, the constants only are unknowns
            bounds[k] = (-16, 16) if fixed is None else \
                ((fixed[1],) * 2 if _cv(fixed[0][key[1]]) == key[2] else (0, 0))
        elif key[0] == "c":
            bounds[k] = (None, None)
        else:
            bounds[k] = (0, None)
    cost = np.zeros(n)
    cost[NB] = 1.0
    sols = []
    # the constants reach 2^32: either method may fail; HiGHS's presolve, too, declares
    # feasible programs of this kind infeasible (the interior point without it is tried last)
    for meth, opts, split in (("highs-ds", {}, False), ("highs-ipm", {}, False),
                              ("highs-ipm", {"presolve": False}, False),
                              ("highs-ds", {}, True), ("highs-ipm", {}, True)):
        if (opts or split) and sols:
            break
        if split and not split_rows:
            continue
        A, b = (Asp, bsp) if split else (Aub, bub)
        try:
            res = linprog(cost, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=beq, bounds=bounds, method=meth,
                          options=dict({"time_limit": LP_SECONDS}, **opts))
        except ValueError:
            continue
        if res.status == 0:
            sols.append(res.x)
    out = []
    for x, limit in ((x, limit) for x in sols for limit in (1, 4, 16, 64)):
        fr = {key: Fraction(float(x[k])).limit_denominator(limit) for key, k in col.items()
              if key == "N" or key[0] in ("p", "c")}
        L = math.lcm(*[f.denominator for key, f in fr.items() if key != "N" and key[0] == "p"] + [1])
        pots = []
        for a in body:
            d = {v: int(fr[("p", a, v)] * L) for v in V if fr[("p", a, v)] != 0}
            pots.append((d, math.ceil(fr[("c", a)] * L)))
        N = math.ceil(Fraction(float(x[NB])) * L - Fraction(1, 10 ** 6))
        if (N, pots, L) not in out:
            out.append((N, pots, L))
    # the tightest bound first (a coarse rounding may be proved with a much larger bound)
    return sorted(out, key=lambda t: Fraction(t[0], t[2]))


# ----------------------------------------------------------------------------------------
# The certificate of a function

def zone_constraints(Zd, M, keep):
    """The constraints of a closed zone on the analysis variables `keep`, in the variables
    of the certificate, without those that the ranges imply."""
    Z = Zd.Z
    cv = lambda v: v if v < 10 else 20 + (v - 10)
    out = []
    vs = sorted(keep)
    for i in vs:
        if M[i][Z] < U - 1:
            out.append(lin([(1, cv(i))], -M[i][Z]))
        if M[Z][i] < 0:
            out.append(lin([(-1, cv(i))], -M[Z][i]))
        for j in vs:
            if i != j and M[i][j] < U - 1 and M[i][j] < M[i][Z] + M[Z][j]:
                out.append(lin([(1, cv(i)), (-1, cv(j))], -M[i][j]))
    return out


def relevant(ctx, loops):
    """Analysis variables that the potentials and the loop tests need, closed under the
    copies that define them."""
    R = set()
    for lc in loops:
        for p in lc.pot:
            R |= {v if v < 20 else 10 + (v - 20) for v in p[0]}
    for _h, body, _N in ctx.iloops:
        for a in body:
            fl = ctx.eff[a][1]
            if fl not in ("keep", "any"):
                R |= {x[1] for x in fl[1:] if x[0] == "reg"}
    R |= set(range(10, 10 + len(ctx.slots)))
    changed = True
    while changed:
        changed = False
        for a in ctx.nodes:
            for r, v in ctx.eff[a][0]:
                if r in R and v != "any":
                    for x in val_srcs(v):
                        if x[0] == "reg" and x[1] not in R:
                            R.add(x[1])
                            changed = True
            st = ctx.st[a]
            if st[2] is not None and st[2][0] not in R:
                pass
            if st[1] not in ("keep", "other") and st[1][0] == "store" and st[1][2] not in R:
                R.add(st[1][2])
                changed = True
    return {r for r in R if r < 10 + len(ctx.slots) and r not in (8, 9)}


def certify_loops(an, name, abi=False, prefer_source=True, frame=False):
    """The loop certificate of a function: (JSON fields, [(header, N/D rounded up, source
    N)] of the certified loops, [(header, reason)] of the others). If a loop is left
    uncertified, the function is analysed again with the literal loads and the shifts giving
    any value in the producer's own analysis (the constants of the literal pool can make the linear
    programs fail numerically); the certificate that certifies more loops is kept. The
    checker's obligations use the exact effects in both."""
    key = None
    if name.startswith("__aeabi_") and name in an.img.funcs:
        # the run-time routines are the same code in every binary: an empty result is
        # reused (keyed by the code, its alignment and the options; addresses relocated)
        start, size = an.img.funcs[name]
        key = (bytes(an.img.mem[start:start + size]), start % 4, abi, prefer_source, frame)
        if key in _RUNTIME_EMPTY:
            fields, why = _RUNTIME_EMPTY[key]
            return dict(fields), [], [(None if h is None else h + start, w) for h, w in why]
    global _DEADLINE
    deadline = time.process_time() + FUNC_SECONDS if FUNC_SECONDS > 0 else None
    _DEADLINE = deadline
    try:
        res = _certify_loops_budget(an, name, abi, prefer_source, frame, False, deadline)
        if res[2] and any(w == "no potential found" for _h, w in res[2]) and \
                (deadline is None or time.process_time() < deadline):
            alt = _certify_loops_budget(an, name, abi, prefer_source, frame, True, deadline)
            if len(alt[1]) > len(res[1]):
                res = alt
    finally:
        _DEADLINE = None
    if key is not None and set(res[0]) <= {"sp"} and not res[1]:
        _RUNTIME_EMPTY[key] = (res[0], [(None if h is None else h - start, w) for h, w in res[2]])
    return res


def _certify_loops_budget(an, name, abi, prefer_source, frame, lit_any, deadline):
    """`_certify_loops`; when the budget is spent during the analysis, no loop is certified
    (the offsets of SP are still given)."""
    try:
        return _certify_loops(an, name, abi, prefer_source, frame, lit_any, deadline)
    except BudgetSpent:
        global _DEADLINE
        saved, _DEADLINE = _DEADLINE, None
        try:
            ctx = Ctx(an, name, abi, frame, lit_any)
        except Exception as e:      # noqa: BLE001
            return {}, [], [(None, str(e))]
        finally:
            _DEADLINE = saved
        return ({"sp": [ctx.sp.get(a) for a in ctx.nodes]}, [],
                [(h, "no potential found (time budget of the function spent)") for h, _b, _n in ctx.iloops])


_RUNTIME_EMPTY = {}


def _certify_loops(an, name, abi, prefer_source, frame, lit_any, deadline=None):
    try:
        ctx = Ctx(an, name, abi, frame, lit_any)
    except Exception as e:      # noqa: BLE001 (the analysis refuses the function)
        return {}, [], [(None, str(e))]
    # the offsets of SP are given for every function, with loops or not: the checker uses them
    # to establish the calling convention on the code (Lean `convOk`)
    sp_only = {"sp": [ctx.sp.get(a) for a in ctx.nodes]}
    if not ctx.iloops:
        return sp_only, [], []
    kind = kinds_of(ctx)
    if CONG:        # the congruences do not depend on the zones: one analysis, with them
        ctx.cong = congruences(ctx)
    state = analyse(ctx, kind)
    cache = {a: (transfer(ctx, kind, a, state[a]) if state[a] is not None else []) for a in ctx.nodes}

    def invariants(R):
        inv = Invs()
        for a in ctx.nodes:
            if state[a] is None:
                inv[a] = [({}, 1)]
                continue
            keep = set(R) | ({8, 9} if kind.get(a, "none") != "none" else set())
            parts = ctx.disj.get(a, [])
            if len(parts) >= 2:
                zs = [zone_constraints(ctx.zones, Zn, keep) for _tag, Zn in parts]
                inv[a], inv.alt[a], inv.tags[a] = zs[0], zs[1:], [tag for tag, _Zn in parts]
            else:
                inv[a] = zone_constraints(ctx.zones, state[a], keep)
        return inv

    loops, info, why = [], [], []
    full = None             # invariants on every variable, for the linear programs
    for h, body, Nsrc in ctx.iloops:
        s = synth(ctx, kind, state, h, body, cache)
        eff_n = -(-s[0] // s[2]) if s is not None else None
        late = deadline is not None and time.process_time() >= deadline
        if LP and not late and (s is None or (Nsrc is not None and eff_n > Nsrc)):
            if full is None:
                full = invariants(set(range(10 + len(ctx.slots))) - {8, 9})
            def transported(h=h, body=body):
                # linear parts that follow a bounded variable of the header (`transport`),
                # the constants from the linear program (HiGHS fails on the full program)
                Mh = state[h]
                for r in range(10 + len(ctx.slots)):
                    if r in (8, 9) or Mh is None or ctx.zones.lohi(Mh, r) == (0, U - 1):
                        continue
                    lin = transport(ctx, state, h, body, r)
                    if lin is not None:
                        for sgn in (1, -1):
                            # longest paths first: they also choose the scale D
                            st_ = synth_transport(ctx, kind, state, h, body, lin, sgn)
                            if st_ is not None:
                                yield st_
                            yield from synth_lp(ctx, kind, full, h, body, False, fixed=(lin, sgn))
            cands = itertools.chain(
                (c for coarse in (False, True) for c in synth_lp(ctx, kind, full, h, body, coarse)),
                transported())
            for N, pots, D in cands:
                if deadline is not None and time.process_time() >= deadline:
                    late = True
                    break
                if s is not None and Fraction(N, D) >= Fraction(s[0], s[2]):
                    continue
                if prove_all(ctx, kind, full, [Loop(h, body, D, N, pots)])[0]:
                    s, eff_n = (N, pots, D), -(-N // D)
                    if Nsrc is None or eff_n <= Nsrc:
                        break       # else look on for a bound within the source bound
        if s is None:
            why.append((h, "no potential found" + (" (time budget of the function spent)" if late else "")))
            continue
        N, pots, D = s
        if prefer_source and Nsrc is not None and eff_n > Nsrc:
            why.append((h, f"certified bound {eff_n} above the source bound {Nsrc}"))
            continue
        loops.append(Loop(h, body, D, N, pots))
        info.append((h, eff_n, Nsrc))
    if not loops:
        return sp_only, [], why
    inv = full if full is not None else invariants(relevant(ctx, loops))
    loops, inv, proofs, dropped = prove_all(ctx, kind, inv, loops)
    for li, h in dropped:
        why.append((h, "an obligation of its potential could not be proved"))
    info = [x for x in info if any(lc.header == x[0] for lc in loops)]
    if not loops:
        return sp_only, [], why
    fields = dict(
        kinds=[kind.get(a, "none") for a in ctx.nodes],
        inv=[[js_lin(g) for g in inv.get(a, [])] for a in ctx.nodes],
        loops=[dict(header=lc.header, body=lc.body, scale=lc.scale, bound=lc.bound,
                    pot=[js_lin(p) for p in lc.pot]) for lc in loops],
        sp=[ctx.sp.get(a) for a in ctx.nodes],
        slots=ctx.slots,
        frame=ctx.frame,
        cong=[[[v, e, r] for v, (e, r) in sorted((ctx.cong or {}).get(a, {}).items())] for a in ctx.nodes],
        proofs=proofs)
    if any(inv.alt.get(a) for a in ctx.nodes):
        fields["alt"] = [[[js_lin(g) for g in d] for d in inv.alt.get(a, [])] for a in ctx.nodes]
        fields["pick"] = picks_of(ctx, inv, kind)
    return fields, info, why


def js_lin(g):
    return dict(sv=[[v, k] for v, k in sorted(g[0].items())], c=g[1])


def js_proof(cert):
    mu, lam = cert
    return [mu, [[i, x] for i, x in enumerate(lam) if x]]


def prove_all(ctx, kind, inv, loops):
    """Proves every obligation, dropping what fails; returns (loops, inv, proofs in the
    checker's order, [(index, header)] of the dropped loops)."""
    inv = inv.copy() if isinstance(inv, Invs) else Invs({a: list(v) for a, v in inv.items()})
    alive = list(range(len(loops)))
    dropped = []
    nv = nvars(len(ctx.slots))
    rng = ranges_n(nv)
    while True:
        cur = [loops[i] for i in alive]
        failed_inv, failed_loop = set(), set()
        proofs = []
        entry_goals = list(inv.get(ctx.entry, [])) + [
            goal_lin(-row_rhs(ctx.entry, lc), lc.pot_at(ctx.entry), pconst(0)) for lc in cur]
        pr = Prover(rng, nv, entry_goals)
        for k, g in enumerate(inv.get(ctx.entry, [])):
            cert = pr.prove(g)
            if cert is None:
                failed_inv.add((ctx.entry, 0, k))
            proofs.append(cert)
        for li, lc in enumerate(cur):
            cert = pr.prove(goal_lin(-row_rhs(ctx.entry, lc), lc.pot_at(ctx.entry), pconst(0)))
            if cert is None:
                failed_loop.add(li)
            proofs.append(cert)
        for a in ctx.nodes:
            for prem, goals in obligations_of(ctx, a, inv, kind, cur):
                pr = Prover(prem, nv, [g for g, _t in goals])
                for g, tag in goals:
                    cert = pr.prove(g)
                    if cert is None:
                        if tag[0] == "inv":
                            failed_inv.add((tag[1], tag[2], tag[3]))
                        else:
                            failed_loop.add(tag[1])
                    proofs.append(cert)
        if not failed_inv and not failed_loop:
            return cur, inv, [js_proof(c) for c in proofs], dropped
        for n, t, k in sorted(failed_inv, reverse=True):
            if t == 0:
                del inv[n][k]
            else:
                del inv.alt[n][t - 1][k]
        for li in sorted(failed_loop, reverse=True):
            dropped.append((alive[li], loops[alive[li]].header))
            del alive[li]
