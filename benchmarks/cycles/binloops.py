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
import math
from fractions import Fraction

import m0
import ipet
import wcet


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
NV = 20          # variables: 0-7 registers, 8-9 ghosts, 10-17 written registers, 18-19 fresh ghosts
Z = 10           # the zero node of the difference graphs (analysis)
INF = 1 << 62


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
        return [(i, "any") for i in [(h >> 8) % 8] + lowlist(h)], "keep"
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


def cond_facts(kind, cc, taken):
    c = cc if taken else cc ^ 1
    if kind == "none":
        return [[]]
    return sub_facts(c) if kind == "sub" else add_facts(c)


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


def val_e(v, m, i):
    if v == "any":
        return pv(10 + i)
    op, a, b = v
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
    x = val_e(o[1], m, o[0])
    return [psmul(-1, x), padd(x, pconst(-(U - 1)))]


def mcases(eff):
    return [0, 1, -1] if op_of(eff) is not None else [0]


RANGES = [c for v in range(NV) for c in (lin([(-1, v)], 0), lin([(1, v)], 1 - U))]


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


def obligations_of(ctx, a, inv, kinds, loops):
    """The obligations of the instruction at `a`, grouped by premises:
    [(premises, [(goal, tag)])], tag = ("inv", successor, index) | ("loop", index)."""
    i, eff = ctx.insn[a], ctx.eff[a]
    ka = kinds.get(a, "none")
    out = []
    for j, (nxt, _w, _cs) in enumerate(ipet.trans(i)):
        facts = cond_facts(ka, ctx.cc[a], j == 0) if i.kind == "cond" else [[]]
        for m in mcases(eff):
            for D in facts:
                prem = D + wrap_prem(eff, m) + inv.get(a, []) + RANGES
                sigma = (lambda m: lambda v: post_e(eff, m, v))(m)
                goals = []
                if nxt is not None:
                    goals += [(subst(g, sigma), ("inv", nxt, k)) for k, g in enumerate(inv.get(nxt, []))]
                goals += [(goal_lin(lc.coef(a, nxt), subst(lc.pot_at(nxt), sigma), lc.pot_at(a)), ("loop", li))
                          for li, lc in enumerate(loops)]
                out.append((prem, goals))
    return out


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
    """A premise `x_a − x_b ≤ w` as an edge (b, a, w) of the difference graph (node Z = 0)."""
    d, c = p
    items = list(d.items())
    if len(items) == 1:
        v, k = items[0]
        if k == 1:
            return (Z, v, -c)
        if k == -1:
            return (v, Z, -c)
    elif len(items) == 2:
        (v1, k1), (v2, k2) = items
        if k1 == 1 and k2 == -1:
            return (v2, v1, -c)
        if k1 == -1 and k2 == 1:
            return (v1, v2, -c)
    return None


class Prover:
    """Farkas certificates for one set of premises: shortest paths in the graph of its
    difference constraints, a linear program otherwise."""

    def __init__(self, prem):
        self.prem = prem
        n = NV + 1
        self.zn = NV                      # the zero node
        dist = [[INF] * n for _ in range(n)]
        via = [[None] * n for _ in range(n)]   # (premise index) of a direct edge, or k
        for x in range(n):
            dist[x][x] = 0
        for idx, p in enumerate(prem):
            e = _diff_edge(p)
            if e is None:
                continue
            b, a, w = e
            b = self.zn if b == Z else b
            a = self.zn if a == Z else a
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
        self.neg = next((x for x in range(n) if dist[x][x] < 0), None)
        self.rng = {}
        for idx, p in enumerate(prem):
            if idx >= len(prem) - len(RANGES):
                v, k = next(iter(p[0].items()))
                self.rng[(v, k)] = idx

    def _path(self, i, j, out, depth=0):
        if i == j or depth > 64:
            return
        w = self.via[i][j]
        if w[0] == "e":
            out[w[1]] = out.get(w[1], 0) + 1
        else:
            self._path(i, w[1], out, depth + 1)
            self._path(w[1], j, out, depth + 1)

    def _cycle(self, x, out):
        """A negative cycle of the difference graph (Bellman-Ford on the premises' edges);
        `x` unused."""
        n = NV + 1
        edges = []
        for idx, p in enumerate(self.prem):
            e = _diff_edge(p)
            if e is not None:
                b, a, w = e
                edges.append((self.zn if b == Z else b, self.zn if a == Z else a, w, idx))
        dist = [0] * n
        pred = [None] * n
        last = None
        for _ in range(n):
            last = None
            for b, a, w, idx in edges:
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
            if not p[0] and p[1] > 0:       # a premise `c ≤ 0` with c > 0
                cert = self._from_cycle(g, {idx: 1})
                if cert:
                    return cert
        if self.neg is not None:
            cyc = {}
            if self._cycle(self.neg, cyc):
                cert = self._from_cycle(g, cyc)
                if cert:
                    return cert
        e = _diff_edge(g)
        if e is not None:
            b, a, w = e
            b = self.zn if b == Z else b
            a = self.zn if a == Z else a
            if self.dist[b][a] <= w:
                out = {}
                self._path(b, a, out)
                cert = self._dense(1, out)
                if entails(self.prem, g, cert):
                    return cert
        return self._lp(g)

    def _from_cycle(self, g, cyc):
        lam = dict(cyc)
        const = sum(n * self.prem[i][1] for i, n in lam.items())   # the cycle: const ≤ 0, const > 0
        if const <= 0:
            return None
        rest = 0
        for v, k in g[0].items():
            if k > 0:
                idx = self.rng.get((v, 1))
                lam[idx] = lam.get(idx, 0) + k
                rest += k * self.prem[idx][1]
            else:
                idx = self.rng.get((v, -1))
                lam[idx] = lam.get(idx, 0) - k
                rest += -k * self.prem[idx][1]
        # g − (ranges) − K·cycle: constant g.c − rest − K·const ≤ 0
        need = g[1] - rest
        K = max(1, -(-need // const)) if need > 0 else 1
        for i, n in cyc.items():
            lam[i] = lam.get(i, 0) + (K - 1) * n
        cert = self._dense(1, lam)
        return cert if entails(self.prem, g, cert) else None

    def _dense(self, mu, lam):
        n = max(lam) + 1 if lam else 0
        return (mu, [lam.get(i, 0) for i in range(n)])

    def _lp(self, g):
        import numpy as np
        from scipy.optimize import linprog
        prem = self.prem
        vars_ = sorted(set(g[0]) | {v for p in prem for v in p[0]})
        if not vars_:
            return None
        P = len(prem)
        # unknowns: lam_0..lam_{P-1}, mu
        A_eq = np.zeros((len(vars_), P + 1))
        for r, v in enumerate(vars_):
            for i, p in enumerate(prem):
                A_eq[r, i] = p[0].get(v, 0)
            A_eq[r, P] = -g[0].get(v, 0)
        A_ub = np.zeros((1, P + 1))
        for i, p in enumerate(prem):
            A_ub[0, i] = -p[1]
        A_ub[0, P] = g[1]
        big = max([abs(p[1]) for p in prem] + [abs(g[1]), 1])
        for margin in (max(1.0, 1e-6 * big), 0.0):
            res = linprog(np.r_[np.ones(P), 0.0], A_ub=A_ub, b_ub=[-margin], A_eq=A_eq,
                          b_eq=np.zeros(len(vars_)), bounds=[(0, None)] * P + [(1, None)], method="highs")
            if res.status != 0:
                continue
            cert = self._round(res.x, P, g)
            if cert:
                return cert
        return None

    def _round(self, x, P, g):
        prem = self.prem
        res = type("R", (), {"x": x})
        for limit in (1, 100, 10 ** 4, 10 ** 6):
            fr = [Fraction(x).limit_denominator(limit) for x in res.x]
            D = math.lcm(*[f.denominator for f in fr])
            vals = [int(f * D) for f in fr]
            if vals[P] <= 0:
                continue
            lam = {i: x for i, x in enumerate(vals[:P]) if x > 0}
            cert = self._dense(vals[P], lam)
            if entails(prem, g, cert):
                return cert
        return None


# ----------------------------------------------------------------------------------------
# The analysis: zones (differences of registers and ghosts)

def top():
    M = [[INF] * 11 for _ in range(11)]
    for x in range(11):
        M[x][x] = 0
    for v in range(10):
        M[v][Z] = U - 1
        M[Z][v] = 0
    return M


def close(M):
    n = 11
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
    for i in range(11):
        for j in range(11):
            if new[i][j] > old[i][j]:
                t = next((t for t in thresholds if t >= new[i][j]), INF)
                out[i][j] = t
    return out


def havoc(M, d):
    for x in range(11):
        M[d][x] = INF
        M[x][d] = INF
    M[d][d] = 0
    M[d][Z] = U - 1
    M[Z][d] = 0


def lohi(M, v):
    return -M[Z][v], M[v][Z]


def assign_shift(M, d, s, k):
    """x_d := x_s + k (exact)."""
    if d == s:
        for x in range(11):
            if x != d:
                if M[d][x] < INF:
                    M[d][x] += k
                if M[x][d] < INF:
                    M[x][d] -= k
        return
    havoc(M, d)
    M[d][s] = min(M[d][s], k)
    M[s][d] = min(M[s][d], -k)


def assign_const(M, d, k):
    havoc(M, d)
    M[d][Z] = k
    M[Z][d] = -k


def guard(M, p):
    """Adds the constraint `p` (over the ghosts) to a closed zone; None if empty."""
    M = copy(M)
    d, c = p
    e = _diff_edge(p)
    if e is not None:
        b, a, w = e
        M[a][b] = min(M[a][b], w)
    elif set(d) == {8, 9} and d[8] == d[9] and abs(d[8]) == 1:
        s = d[8]
        l8, h8 = lohi(M, 8)
        l9, h9 = lohi(M, 9)
        if s == 1:       # x8 + x9 ≤ −c
            M[8][Z] = min(M[8][Z], -c - l9)
            M[9][Z] = min(M[9][Z], -c - l8)
        else:            # x8 + x9 ≥ c
            M[Z][8] = min(M[Z][8], h9 - c)
            M[Z][9] = min(M[Z][9], h8 - c)
    else:
        return M
    return close(M)


def apply_effect(M, eff):
    """The zone after an instruction, from the zone before (closed); exact writes only
    when no wrap is possible."""
    dst, fl = eff
    M = copy(M)
    pre = copy(M)
    # ghosts first (they read the registers before the instruction)
    if fl == "any":
        havoc(M, 8)
        havoc(M, 9)
    elif fl != "keep":
        for gv, s in ((8, fl[1]), (9, fl[2])):
            if s[0] == "reg":
                assign_shift(M, gv, s[1], 0)
            else:
                assign_const(M, gv, s[1])
        M = close(M)
    seen = set()
    for r, v in dst:
        if r in seen:
            continue
        seen.add(r)
        if v == "any":
            havoc(M, r)
            continue
        op, a, b = v
        if a[0] == "imm" and b[0] == "imm":
            val = a[1] + b[1] if op == "add" else a[1] - b[1]
            if 0 <= val < U:
                assign_const(M, r, val)
            else:
                havoc(M, r)
        elif a[0] == "reg" and b[0] == "imm":
            k = b[1] if op == "add" else -b[1]
            l, h = lohi(pre, a[1])
            if l + k >= 0 and h + k <= U - 1:
                assign_shift(M, r, a[1], k)
            else:
                havoc(M, r)
        else:
            havoc(M, r)
    return close(M)


class Ctx:
    def __init__(self, an, name, abi, base=0):
        self.an, self.name, self.abi = an, name, abi
        mem = an.img.mem
        self.get = lambda a: (int.from_bytes(mem[a:a + 2], "little") if 0 <= a and a + 2 <= len(mem) else None)
        (self.entry, self.blocks, self.succ, self.back, self.loops, self.headers,
         self.bound) = structure(an, name)
        insns = sorted((i for il in self.blocks.values() for i in il), key=lambda i: i.addr)
        self.nodes = [i.addr for i in insns]
        self.insn = {i.addr: i for i in insns}
        self.eff = {a: effect(abi, self.get, a) for a in self.nodes}
        self.cc = {a: (self.get(a) >> 8) % 16 for a in self.nodes}
        self.out = {a: ipet.trans(self.insn[a]) for a in self.nodes}
        self.pred = {a: [] for a in self.nodes}
        for a in self.nodes:
            for n, _w, _c in self.out[a]:
                if n is not None:
                    self.pred[n].append(a)
        imms = {0, 1, U - 1}
        for a in self.nodes:
            for _r, v in self.eff[a][0]:
                if v != "any":
                    for s in v[1:]:
                        if s[0] == "imm":
                            imms |= {s[1], s[1] - 1, s[1] + 1}
            fl = self.eff[a][1]
            if fl not in ("keep", "any"):
                for s in fl[1:]:
                    if s[0] == "imm":
                        imms |= {s[1], s[1] - 1, s[1] + 1}
        self.thresholds = sorted(t for t in imms if 0 <= t < U) + [U - 1]
        thr = set(self.thresholds)
        self.thresholds = sorted(thr | {-t for t in thr})
        # loops at the level of instructions: header address, body addresses
        self.iloops = []
        for h in self.headers:
            body = sorted(i.addr for b in self.loops[h] for i in self.blocks[b])
            self.iloops.append((h, body, self.bound.get(h)))


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
    """[(j, D index, zone with the facts before the effect, zone after)] of the
    transitions of `a`."""
    i, eff = ctx.insn[a], ctx.eff[a]
    res = []
    for j, (nxt, _w, _cs) in enumerate(ctx.out[a]):
        facts = cond_facts(kind.get(a, "none"), ctx.cc[a], j == 0) if i.kind == "cond" else [[]]
        for di, D in enumerate(facts):
            Mf = M
            for p in D:
                Mf = guard(Mf, p) if Mf is not None else None
            if Mf is None:
                continue
            post = apply_effect(Mf, eff)
            if post is not None and nxt is not None and kind.get(nxt, "none") == "none":
                post = copy(post)
                havoc(post, 8)
                havoc(post, 9)
            res.append((j, di, Mf, post))
    return res


def analyse(ctx, kind):
    state = {a: None for a in ctx.nodes}
    state[ctx.entry] = top()
    heads = {h for h, _b, _n in ctx.iloops}
    order = {a: k for k, a in enumerate(ctx.nodes)}
    work = [ctx.entry]
    visits = {}
    while work:
        work.sort(key=lambda x: order[x])
        a = work.pop(0)
        M = state[a]
        if M is None:
            continue
        for j, _di, _Mf, post in transfer(ctx, kind, a, M):
            n = ctx.out[a][j][0]
            if n is None or post is None:
                continue
            new = join(state[n], post)
            if n in heads:
                visits[n] = visits.get(n, 0) + 1
                if visits[n] > 2:
                    new = widen(state[n], new, ctx.thresholds)
            new = close(new) if new is not None else None
            if not leq(new, state[n]):
                state[n] = new
                if n not in work:
                    work.append(n)
    for _ in range(3):      # descending iterations (from a post-fixpoint: still inductive)
        new = {a: None for a in ctx.nodes}
        new[ctx.entry] = top()
        for a in ctx.nodes:
            if state[a] is None:
                continue
            for j, _di, _Mf, post in transfer(ctx, kind, a, state[a]):
                n = ctx.out[a][j][0]
                if n is not None and post is not None:
                    new[n] = join(new[n], post)
        state = {a: (close(m) if m is not None else None) for a, m in new.items()}
    return state


# ----------------------------------------------------------------------------------------
# Potentials

def bound_of(M, phi):
    """Upper bound of `Σ k·x_v` (k = ±1 on at most two variables) on a zone."""
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


def delta(eff, phi, Mf):
    """Upper bound of φ(after) − φ(before) on the zone `Mf` (before the effect)."""
    change = {}
    dst = {}
    for r, v in eff[0]:
        dst.setdefault(r, v)
    total = 0
    for v, k in phi.items():
        if v not in dst:
            continue
        w = dst[v]
        if w == "any":
            return INF
        op, a, b = w
        if a[0] == "reg" and a[1] == v and b[0] == "imm":
            sh = b[1] if op == "add" else -b[1]
            l, h = lohi(Mf, v)
            if not (l + sh >= 0 and h + sh <= U - 1):
                return INF
            total += k * sh
        elif a[0] == "imm" and b[0] == "imm":
            val = a[1] + b[1] if op == "add" else a[1] - b[1]
            l, h = lohi(Mf, v)
            total += k * val - (k * l if k > 0 else k * h)
        else:
            return INF
        change[v] = True
    return total


def synth(ctx, kind, state, h, body, prems_cache):
    """The best potential of the loop at `h`: (bound N, [potentials of the body]) or None."""
    B = set(body)
    cands = []
    for r in range(8):
        cands += [{r: 1}, {r: -1}]
    # differences of the registers compared at the exits of the loop
    for a in body:
        M = state[a]
        if M is None or ctx.insn[a].kind != "cond" or kind.get(a, "none") == "none":
            continue
        ra = [r for r in range(8) if M[8][r] == 0 and M[r][8] == 0]
        rb = [r for r in range(8) if M[9][r] == 0 and M[r][9] == 0]
        for r in ra:
            for q in rb:
                if r != q:
                    for phi in ({r: 1, q: -1}, {r: -1, q: 1}):
                        if phi not in cands:
                            cands.append(phi)
    best = None
    for phi, D in [(phi, D) for phi in cands for D in (1, 2, 4, 8)]:
        cmin = {a: -INF for a in body}
        edges = []         # (a, n, w): c_a ≥ c_n + w
        entry_terms = []   # (zone after, at the header)
        ok = True
        for a in ctx.nodes:
            if state[a] is None:
                continue
            for j, _di, Mf, post in prems_cache[a]:
                n = ctx.out[a][j][0]
                if a in B:
                    if n is not None and n in B:
                        dl = delta(ctx.eff[a], phi, Mf)
                        if dl >= INF:
                            ok = False
                            break
                        edges.append((a, n, (D if n == h else 0) + dl))
                    else:
                        # leaving the loop: Φ_a ≥ 0, i.e. c_a ≥ max(−φ) on Mf
                        mb = bound_of(Mf, {v: -k for v, k in phi.items()})
                        if mb >= INF:
                            ok = False
                            break
                        cmin[a] = max(cmin[a], mb)
                elif n == h:
                    if post is None:
                        continue
                    mb = bound_of(post, phi)
                    if mb >= INF:
                        ok = False
                        break
                    entry_terms.append(mb)
            if not ok:
                break
        if not ok:
            continue
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
            mb = bound_of(top(), phi)
            entry_terms.append(mb)
        N = max([c[h] + t for t in entry_terms], default=0)
        N = max(N, 0)
        if best is None or Fraction(N, D) < Fraction(best[0], best[2]):
            best = (N, [padd(({v: k for v, k in phi.items()}, 0), pconst(c[a])) for a in body], D)
    return best


# ----------------------------------------------------------------------------------------
# The certificate of a function

def zone_constraints(M, keep):
    """The constraints of a closed zone on the variables `keep` (and the zero node),
    without those that the ranges imply."""
    out = []
    vs = sorted(keep)
    for i in vs:
        if M[i][Z] < U - 1:
            out.append(lin([(1, i)], -M[i][Z]))
        if M[Z][i] < 0:
            out.append(lin([(-1, i)], -M[Z][i]))
        for j in vs:
            if i != j and M[i][j] < U - 1 and M[i][j] < M[i][Z] + M[Z][j]:
                out.append(lin([(1, i), (-1, j)], -M[i][j]))
    return out


def relevant(ctx, loops):
    R = set()
    for lc in loops:
        for p in lc.pot:
            R |= set(p[0])
    for h, body, _N in ctx.iloops:
        for a in body:
            fl = ctx.eff[a][1]
            if fl not in ("keep", "any"):
                R |= {s[1] for s in fl[1:] if s[0] == "reg"}
    changed = True
    while changed:
        changed = False
        for a in ctx.nodes:
            for r, v in ctx.eff[a][0]:
                if r in R and v != "any":
                    for s in v[1:]:
                        if s[0] == "reg" and s[1] not in R:
                            R.add(s[1])
                            changed = True
    return {r for r in R if r < 8}


def certify_loops(an, name, abi=False, prefer_source=True):
    """The loop certificate of a function: (dict of JSON fields, [(header, N, source N)]
    of the certified loops, [(header, reason)] of the others). Raises nothing: a function
    without certified loops gets no fields."""
    try:
        ctx = Ctx(an, name, abi)
    except Exception as e:      # noqa: BLE001 (the analysis refuses the function)
        return {}, [], [(None, str(e))]
    if not ctx.iloops:
        return {}, [], []
    kind = kinds_of(ctx)
    state = analyse(ctx, kind)
    cache = {a: (transfer(ctx, kind, a, state[a]) if state[a] is not None else []) for a in ctx.nodes}
    loops, info, why = [], [], []
    for h, body, Nsrc in ctx.iloops:
        s = synth(ctx, kind, state, h, body, cache)
        if s is None:
            why.append((h, "no potential found"))
            continue
        N, pots, D = s
        eff_n = -(-N // D)
        if prefer_source and Nsrc is not None and eff_n > Nsrc:
            why.append((h, f"certified bound {eff_n} above the source bound {Nsrc}"))
            continue
        loops.append(Loop(h, body, D, N, pots))
        info.append((h, eff_n, Nsrc))
    if not loops:
        return {}, [], why
    R = relevant(ctx, loops)
    inv = {}
    for a in ctx.nodes:
        if state[a] is None:
            inv[a] = [({}, 1)]          # unreachable: 1 ≤ 0
            continue
        keep = set(R) | ({8, 9} if kind.get(a, "none") != "none" else set())
        inv[a] = zone_constraints(state[a], keep)
    loops, inv, proofs, dropped = prove_all(ctx, kind, inv, loops)
    for li, h in dropped:
        why.append((h, "an obligation of its potential could not be proved"))
    info = [x for x in info if any(lc.header == x[0] for lc in loops)]
    if not loops:
        return {}, [], why
    fields = dict(
        kinds=[kind.get(a, "none") for a in ctx.nodes],
        inv=[[js_lin(g) for g in inv.get(a, [])] for a in ctx.nodes],
        loops=[dict(header=lc.header, body=lc.body, scale=lc.scale, bound=lc.bound,
                    pot=[js_lin(p) for p in lc.pot]) for lc in loops],
        proofs=proofs)
    return fields, info, why


def js_lin(g):
    return dict(sv=[[v, k] for v, k in sorted(g[0].items())], c=g[1])


def js_proof(cert):
    mu, lam = cert
    return [mu, [[i, x] for i, x in enumerate(lam) if x]]


def prove_all(ctx, kind, inv, loops):
    """Proves every obligation, dropping what fails; returns (loops, inv, proofs in the
    checker's order, [(index, header)] of the dropped loops)."""
    inv = {a: list(v) for a, v in inv.items()}
    alive = list(range(len(loops)))
    dropped = []
    while True:
        cur = [loops[i] for i in alive]
        failed_inv, failed_loop = set(), set()
        proofs = []
        # entry obligations
        pr = Prover(RANGES)
        for k, g in enumerate(inv.get(ctx.entry, [])):
            cert = pr.prove(g)
            if cert is None:
                failed_inv.add((ctx.entry, k))
            proofs.append(cert)
        for li, lc in enumerate(cur):
            cert = pr.prove(goal_lin(-row_rhs(ctx.entry, lc), lc.pot_at(ctx.entry), pconst(0)))
            if cert is None:
                failed_loop.add(li)
            proofs.append(cert)
        for a in ctx.nodes:
            for prem, goals in obligations_of(ctx, a, inv, kind, cur):
                pr = Prover(prem)
                for g, tag in goals:
                    cert = pr.prove(g)
                    if cert is None:
                        if tag[0] == "inv":
                            failed_inv.add((tag[1], tag[2]))
                        else:
                            failed_loop.add(tag[1])
                    proofs.append(cert)
        if not failed_inv and not failed_loop:
            return cur, inv, [js_proof(c) for c in proofs], dropped
        for n, k in sorted(failed_inv, reverse=True):
            del inv[n][k]
        for li in sorted(failed_loop, reverse=True):
            dropped.append((alive[li], loops[alive[li]].header))
            del alive[li]
