# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Cycle certificates of Cortex-M0 machine code, checked by the verified checker.

The certificate holds the machine code itself (the halfwords of the code region) and, for
each function, its entry, the addresses of its instructions (those of
`wcet.Analysis.cfg`), its loop rows on pairs of addresses and the certificate proper. The
checker decodes the code with its own decoder and timing table (Lean `Thumb.decode`, the
same table as `m0.py`, compared by `test_thumb.py`) and builds the graph itself: one node
per instruction, one edge per successor, with its cycles (a conditional branch: 3 taken,
1 not taken) and callees. Each natural loop matched with a source loop of bound `N`
(`wcet.Analysis.loop_structure`) gives a row `Σ back edges − N·Σ entry edges ≤ 0`
(`≤ N` if the loop header is the function's entry), on the transitions from the last
instruction of a block to the header.

The bound is that of the implicit path enumeration technique (IPET, Li and Malik): the
largest cost of edge counts satisfying flow conservation and the rows. A linear program
solver (scipy's HiGHS, untrusted) gives the multipliers of the rows; they are made
rational, scaled to integers, and the potentials are computed exactly as longest paths to
the exit; the bound is the smallest integer the certificate supports. The certificate
(`"format": "crosscheck-binary-cycles"`, docs/certificate-format.md) is checked by
`crosscheck-check`, whose acceptance means theorem `Thumb.binary_sound`: every run of the
machine code of the function, in the semantics of Lean `Thumb` (decoder, timing table,
both successors of a conditional branch possible), on which the rows hold, costs at most
the bound. Trusted: that semantics, that the code is the binary's, and the rows.
"""
import math
import struct
from fractions import Fraction

import m0
import wcet


class NoCertificate(Exception):
    pass


def lp_multipliers(nodes, edges, rows, entry, exit_, weights):
    """Multipliers of the rows from the IPET linear program (floats; None if unbounded)."""
    import numpy as np
    from scipy.optimize import linprog
    n, m = len(nodes), len(edges)
    idx = {v: k for k, v in enumerate(nodes)}
    A_eq = np.zeros((n, m))
    b_eq = np.zeros(n)
    for k, (u, v, _w, _c) in enumerate(edges):
        A_eq[idx[v], k] += 1
        A_eq[idx[u], k] -= 1
    b_eq[idx[entry]] -= 1
    b_eq[idx[exit_]] += 1
    if not rows:
        A_ub, b_ub = None, None
    else:
        A_ub = np.zeros((len(rows), m))
        b_ub = np.zeros(len(rows))
        for r, (coef, rhs) in enumerate(rows):
            for e, a in coef:
                A_ub[r, e] += a
            b_ub[r] = rhs
    res = linprog(-np.array(weights, dtype=float), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=(0, None), method="highs")
    if res.status != 0:
        raise NoCertificate(f"linear program: {res.message}")
    return [] if not rows else [max(0.0, -x) for x in res.ineqlin.marginals]


def potentials(nodes, edges, exit_, slack):
    """Longest paths to the exit with edge weights `slack[e]` (Bellman-Ford); None if a
    cycle has positive weight or a node cannot reach the exit."""
    pot = {v: None for v in nodes}
    pot[exit_] = 0
    for _ in range(len(nodes) + 1):
        changed = False
        for k, (u, v, _w, _c) in enumerate(edges):
            if pot[v] is not None:
                cand = pot[v] + slack[k]
                if pot[u] is None or cand > pot[u]:
                    pot[u] = cand
                    changed = True
        if not changed:
            break
    else:
        return None
    if any(p is None for p in pot.values()):
        return None
    return pot


def trans(i):
    """The successors of an instruction, as Lean `Thumb.trans`: (next or None, cycles, callees)."""
    nxt = i.addr + i.size
    if i.kind == "seq":
        return [(nxt, m0.cycles(i, True), [])]
    if i.kind == "cond":
        return [(i.target, m0.cycles(i, True), []), (nxt, m0.cycles(i, False), [])]
    if i.kind == "jump":
        return [(i.target, m0.cycles(i, True), [])]
    if i.kind == "call":
        return [(nxt, m0.cycles(i, True), [i.target])]
    if i.kind == "ret":
        return [(None, m0.cycles(i, True), [])]
    raise NoCertificate(f"{i.op} at {i.addr:#x}: no successor in the semantics")


def certify_function(an, name, bound_of, base=0, cert_loops=()):
    """(JSON of the function, bound); `bound_of`: certified bounds by function address;
    `cert_loops`: [(header, body, scale, bound)] of the loops certified on the machine code
    (`binloops.py`), whose rows the checker generates (after the trusted ones, in this
    order: `Thumb.loopRow`)."""
    try:
        if cert_loops:
            import binloops
            entry, blocks, succ, back, loops, _headers, bound = binloops.structure(an, name)
        else:
            entry, blocks, succ = an.cfg(name)
            _pred, back, loops, _headers, _parent, bound = an.loop_structure(name, entry, blocks, succ)
    except wcet.Unbounded as e:
        raise NoCertificate(str(e))
    done = {h for h, *_ in cert_loops}
    for h in loops:
        if h not in done and bound.get(h) is None:
            raise NoCertificate(f"binary loop at {h:#x} has no bound (neither from the source nor certified)")
    insns = sorted((i for il in blocks.values() for i in il), key=lambda i: i.addr)
    nodes = [i.addr for i in insns]
    idx = {a: k for k, a in enumerate(nodes)}
    exit_ = len(nodes)
    edges = []   # (src, dst, cycles, callee addresses), in node indices
    pairs = []   # (src address, dst address or None)
    for i in insns:
        for n, w, cs in trans(i):
            if n is not None and n not in idx:
                raise NoCertificate(f"successor {n:#x} of {i.addr:#x} outside the function's instructions")
            edges.append((idx[i.addr], exit_ if n is None else idx[n], w, cs))
            pairs.append((i.addr, n))
    for _, _, _, cs in edges:
        for t in cs:
            if bound_of.get(t) is None:
                g = an.img.undefined.get(t) or next((n for n, (a, _) in an.img.funcs.items() if a == t), hex(t))
                raise NoCertificate(f"call to {g}, which has no certificate")
    rows, mrows = [], []
    certified = {h for h, *_ in cert_loops}
    for h, body in loops.items():
        if h in certified:
            continue
        N = bound[h]
        coef = {}
        for u, hh in back:
            if hh == h:
                coef[(blocks[u][-1].addr, h)] = 1
        for v in an_preds(blocks, succ, h):
            if v not in body:
                coef[(blocks[v][-1].addr, h)] = -N
        rhs = N if h == entry else 0
        rows.append(([[k, coef[p]] for k, p in enumerate(pairs) if p in coef], rhs))
        mrows.append(dict(coef=[[s + base, t + base, a] for (s, t), a in sorted(coef.items())], rhs=rhs,
                          note=f"loop at {h + base:#x}: at most {N} back edges per entry"))
    for h, body, D, N in cert_loops:
        B = set(body)
        coef = [[k, D if s in B else -N] for k, (s, t) in enumerate(pairs) if t == h]
        rows.append((coef, N if entry in B else 0))
    weights = [w + sum(bound_of[t] for t in cs) for (_u, _v, w, cs) in edges]
    allnodes = list(range(exit_ + 1))
    lam = lp_multipliers(allnodes, edges, rows, idx[entry], exit_, weights)
    # Candidate multipliers: the LP's rounded up to integers, and its fractions (scale D =
    # their common denominator). Rows of loops certified with a scale above 1 have
    # fractional multipliers, which rounding up makes loose: the smallest feasible bound is
    # kept (any feasible choice is sound: the checker decides).
    best = None
    for limit in (1, 10**3, 10**6):
        fr = [Fraction(x).limit_denominator(limit) for x in lam]
        D = math.lcm(*[f.denominator for f in fr]) if fr else 1
        mult = [math.ceil(x - 1e-6) for x in lam] if limit == 1 else [int(f * D) for f in fr]
        if limit > 1 and any(m < 0 for m in mult):
            continue
        L = [0] * len(edges)
        for r, (coef, _rhs) in enumerate(rows):
            for e, a in coef:
                L[e] += mult[r] * a
        pot = potentials(allnodes, edges, exit_, [D * weights[k] - L[k] for k in range(len(edges))])
        if pot is None:
            continue
        total = pot[idx[entry]] - pot[exit_] + sum(mult[r] * rows[r][1] for r in range(len(rows)))
        B = max(0, -(-total // D))
        if best is None or B < best[0]:
            best = (B, D, mult, pot)
    if best is None:
        raise NoCertificate("no feasible integer multipliers (a cycle without a loop bound?)")
    B, D, mult, pot = best
    fn = dict(name=name, entry=entry + base, nodes=[a + base for a in nodes], rows=mrows,
              certificate=dict(scale=D, pot=[pot[v] for v in allnodes], mult=mult, bound=B))
    return fn, B


def an_preds(blocks, succ, h):
    return [b for b in blocks if h in succ[b]]


def code_top(img):
    """The end of the code region of a certificate: up to the end of the last function
    (the RAM of the image is not code)."""
    top = max((a + s for a, s in img.funcs.values()), default=0) + 4
    return min(top + (top % 2), len(img.mem) - (len(img.mem) % 2))


def certify(an, roots, mul=None, loops=False, abi=False, stats=None, frame=False):
    """A certificate on the machine code for the functions reachable from `roots` (callees
    first); returns (JSON, {function: bound}, {function: reason}). With `loops`, the loop
    bounds are also certified on the machine code where `binloops.py` finds a certificate
    (format version 2; `abi`: callees assumed to preserve r4-r7 and SP; `frame`: for the
    functions that take no address of their frame, stores through other registers and calls
    assumed not to write it); `stats` (a dict) then
    receives per function the certified loops and the reasons for the others."""
    img = an.img
    base = getattr(img, "base", 0)
    addr_of = {n: a for n, (a, _) in img.funcs.items()}
    names = {a: n for n, a in addr_of.items()}
    funcs, bounds, why, active = [], {}, {}, set()

    def visit(name):
        if name in bounds or name in why:
            return
        if name in active:
            why[name] = "recursion"
            return
        active.add(name)
        try:
            _entry, blocks, _ = an.cfg(name)
            for il in blocks.values():
                for i in il:
                    if i.kind == "call" and i.target in names:
                        visit(names[i.target])
            fields, cl = {}, ()
            if loops:
                import binloops
                fields, info, lwhy = binloops.certify_loops(an, name, abi, frame=frame)
                cl = [(l["header"], l["body"], l["scale"], l["bound"]) for l in fields.get("loops", [])]
                if stats is not None:
                    stats[name] = dict(certified=info, other=lwhy)
            fn, B = certify_function(an, name, {addr_of[n]: b for n, b in bounds.items()}, base, cl)
            fn.update(fields)
            funcs.append(fn)
            bounds[name] = B
        except (wcet.Unbounded, NoCertificate) as e:
            why[name] = str(e)
        finally:
            active.discard(name)

    for r in roots:
        visit(r)
    top = code_top(img)
    halfwords = list(struct.unpack_from(f"<{top // 2}H", img.mem, 0)) if top else []
    doc = {"format": "crosscheck-binary-cycles", "version": 2 if loops else 1,
           "mul_cycles": m0.MUL_CYCLES if mul is None else mul,
           "note": "Cortex-M0 machine code; the checker decodes it (Lean Thumb.decode) and builds the graphs",
           "code": dict(base=base, halfwords=halfwords),
           "programs": [dict(name="program", functions=funcs)] if funcs else []}
    if loops:
        doc["abi"] = abi
    return doc, bounds, why
