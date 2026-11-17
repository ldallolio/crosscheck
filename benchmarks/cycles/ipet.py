# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Cycle certificates of Cortex-M0 functions, checked by the verified checker.

For each function, the control-flow graph of `wcet.Analysis.cfg` becomes a graph with a
single exit node whose edges carry their cycles (the block's instructions by the timing
table of `m0.py`, the last one taken or not: a conditional branch costs 3 cycles taken, 1
not taken) and the functions called in the block. Each natural loop matched with a source
loop of bound `N` (`wcet.Analysis.loop_structure`) gives a row
`Σ back edges − N·Σ entry edges ≤ 0` (`≤ N` if the loop header is the function's entry).

The bound is that of the implicit path enumeration technique (IPET, Li and Malik): the
largest cost of edge counts satisfying flow conservation and the rows. A linear program
solver (scipy's HiGHS, untrusted) gives the multipliers of the rows; they are made
rational, scaled to integers, and the potentials are computed exactly as longest paths to
the exit; the bound is the smallest integer the certificate supports. The certificate
(`"format": "crosscheck-cycles"`, docs/certificate-format.md) is checked by
`crosscheck-check`, whose acceptance means theorem `Cycles.program_sound`: every completed
run of the function on which the rows hold costs at most the bound, if the graph and
weights describe the machine code and its timing (trusted, as for wcet.py).
"""
import math
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


def certify_function(an, name, bound_of):
    """(JSON of the function, bound): `bound_of` gives the certified bounds of callees."""
    try:
        entry, blocks, succ = an.cfg(name)
        _pred, back, loops, _headers, _parent, bound = an.loop_structure(name, entry, blocks, succ)
    except wcet.Unbounded as e:
        raise NoCertificate(str(e))
    order = sorted(blocks)
    num = {b: k for k, b in enumerate(order)}
    exit_ = len(order)
    names = {a: n for n, (a, _) in an.img.funcs.items()}
    edges = []   # (src, dst, cycles, [callees])
    for b in order:
        il = blocks[b]
        body = 0
        calls = []
        for i in il[:-1]:
            body += m0.cycles(i, True)
        for i in il:
            if i.kind == "call":
                if i.target not in names:
                    raise NoCertificate(f"call to {an.img.undefined.get(i.target, hex(i.target))} (no code)")
                calls.append(names[i.target])
        last = il[-1]
        if last.kind == "call":
            body += m0.cycles(last, True)
        if last.kind == "cond":
            outs = [(last.target, m0.cycles(last, True)), (last.addr + last.size, m0.cycles(last, False))]
        elif last.kind == "jump":
            outs = [(last.target, m0.cycles(last, True))]
        elif last.kind in ("seq", "call"):
            outs = [(last.addr + last.size, 0 if last.kind == "call" else m0.cycles(last, True))]
        else:   # ret
            outs = [(None, m0.cycles(last, True))]
        outs = [(t, c) for t, c in outs if t is None or t in blocks]
        if not outs:
            outs = [(None, 0)]
        for t, c in outs:
            edges.append((num[b], exit_ if t is None else num[t], body + c, calls))
    for g in {g for e in edges for g in e[3]}:
        if bound_of.get(g) is None:
            raise NoCertificate(f"call to {g}, which has no certificate")
    rows, notes = [], []
    for h, body in loops.items():
        N = bound[h]
        coef = []
        for k, (u, v, _w, _c) in enumerate(edges):
            if v == num[h] and order[u] in body and (order[u], h) in back:
                coef.append([k, 1])
            elif v == num[h] and order[u] not in body:
                coef.append([k, -N])
        rows.append((coef, N if h == entry else 0))
        notes.append(f"loop at {h:#x}: at most {N} back edges per entry")
    weights = [w + sum(bound_of[g] for g in c) for (_u, _v, w, c) in edges]
    nodes = list(range(exit_ + 1))
    lam = lp_multipliers(nodes, edges, rows, num[entry], exit_, weights)
    for limit in (1, 10**3, 10**6):
        fr = [Fraction(x).limit_denominator(limit) for x in lam]
        D = math.lcm(*[f.denominator for f in fr]) if fr else 1
        mult = [int(f * D) for f in fr]
        if limit == 1:
            mult = [math.ceil(x - 1e-6) for x in lam]
        L = [0] * len(edges)
        for r, (coef, _rhs) in enumerate(rows):
            for e, a in coef:
                L[e] += mult[r] * a
        slack = [D * weights[k] - L[k] for k in range(len(edges))]
        pot = potentials(nodes, edges, exit_, slack)
        if pot is not None:
            break
    else:
        raise NoCertificate("no feasible integer multipliers (a cycle without a loop bound?)")
    total = pot[num[entry]] - pot[exit_] + sum(mult[r] * rows[r][1] for r in range(len(rows)))
    B = max(0, -(-total // D))
    fn = dict(name=name, entry=num[entry], exit=exit_,
              edges=[dict(src=u, dst=v, w=w, **({"calls": c} if c else {})) for (u, v, w, c) in edges],
              rows=[dict(coef=coef, rhs=rhs, note=note) for (coef, rhs), note in zip(rows, notes)],
              blocks=[hex(b) for b in order],
              certificate=dict(scale=D, pot=[pot[v] for v in nodes], mult=mult, bound=B))
    return fn, B


def certify(an, roots):
    """A program certificate for the functions reachable from `roots` (callees first);
    returns (JSON, {function: bound}, {function: reason}) for those with a certificate."""
    funcs, bounds, why, active = [], {}, {}, set()

    def visit(name):
        if name in bounds or name in why:
            return
        if name in active:
            why[name] = "recursion"
            return
        active.add(name)
        try:
            entry, blocks, _ = an.cfg(name)
            names = {a: n for n, (a, _) in an.img.funcs.items()}
            for il in blocks.values():
                for i in il:
                    if i.kind == "call" and i.target in names:
                        visit(names[i.target])
            fn, B = certify_function(an, name, bounds)
            funcs.append(fn)
            bounds[name] = B
        except (wcet.Unbounded, NoCertificate) as e:
            why[name] = str(e)
        finally:
            active.discard(name)

    for r in roots:
        visit(r)
    doc = dict(format="crosscheck-cycles", version=1,
               note="Cortex-M0 cycles (timing table of benchmarks/cycles/m0.py); trusted: the graphs, weights and rows",
               programs=[dict(name="program", functions=funcs)] if funcs else [])
    return doc, bounds, why
