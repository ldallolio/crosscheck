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

import jumptable
import m0
import wcet


class NoCertificate(Exception):
    pass


def memo_highs_options():
    """scipy's `linprog(method="highs")` validates each option of every call with a new
    `HighsOptionsManager` (a large share of the time of the small programs solved here);
    the answer depends only on the option and its value, so a successful check is
    remembered. What HiGHS receives is unchanged. Idempotent; does nothing if scipy's
    internals differ."""
    try:
        from scipy.optimize._highspy import _highs_wrapper as hw
    except ImportError:
        return
    orig = getattr(hw, "check_option", None)
    if orig is None or getattr(orig, "memo", None) is not None:
        return
    memo = {}

    def check_option(inst, option, value):
        try:
            key = (option, type(value), value)
            hit = memo.get(key)
        except TypeError:   # an unhashable value: not remembered
            return orig(inst, option, value)
        if hit is None:
            hit = orig(inst, option, value)
            if hit[0] == 0:
                memo[key] = hit
        return hit

    check_option.memo = memo
    hw.check_option = check_option


def lp_multipliers(nodes, edges, rows, entry, exit_, weights):
    """Multipliers of the rows from the IPET linear program (floats; None if unbounded)."""
    import numpy as np
    from scipy.optimize import linprog
    memo_highs_options()
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


def trans(i, jumps=None):
    """The successors of an instruction, as Lean `Thumb.transJ`: (next or None, cycles,
    callees); `jumps`: the function's jumps through tables, {address: (start, targets)}."""
    nxt = i.addr + i.size
    if i.kind == "indirect" and jumps and i.addr in jumps:
        return [(t, 3, []) for t in jumps[i.addr][1]]
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
    `cert_loops`: [(header, body, scale, bound[, outer])] of the loops certified on the machine code
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
    jumps = an.jumps.get(name, {})
    for i in insns:
        for n, w, cs in trans(i, jumps):
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
    certified = {h for h, _b, _d, _n, *rest in cert_loops if not rest or rest[0] is None}
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
    for h, body, D, N, *rest in cert_loops:
        outer = rest[0] if rest else None
        B = set(body)
        if outer is None:
            coef = [[k, D if s in B else -N] for k, (s, t) in enumerate(pairs) if t == h]
            rows.append((coef, N if entry in B else 0))
        else:
            # amortised (`Thumb.loopRow` with `outer`): D on the back edges of the loop, -N on
            # the entries of the enclosing loop, per entry of which the row bounds them
            oh, R = outer[0], set(outer[1])
            coef = [[k, D] for k, (s, t) in enumerate(pairs) if t == h and s in B] + \
                   [[k, -N] for k, (s, t) in enumerate(pairs) if t == oh and s not in R]
            rows.append((coef, N if entry in R else 0))
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
    if jumps:
        fn["jumps"] = []
        for p, jt in sorted(jumps.items()):
            st, ts, ix = jt[0], jt[1], jt[2]
            vr = jt[3] if len(jt) > 3 else None
            if ix is not None and not jumptable.interior_ok_r(st, p, entry, pairs):
                raise NoCertificate(f"a branch into the window of the jump at {p:#x}")
            j = dict(start=st + base, pos=p + base, targets=[t + base for t in ts])
            if ix is not None:
                j["index"] = ix + base
            if vr is not None:
                j["bound"] = list(vr)
            fn["jumps"].append(j)
    return fn, B


def an_preds(blocks, succ, h):
    return [b for b in blocks if h in succ[b]]


def code_top(img):
    """The end of the code region of a certificate: up to the end of the last function and
    of the read-only data that follow the code (`m0.load`: constant tables, read by jumps
    through tables; assumed, like the code, not written during a run); the RAM of the image
    is not code."""
    top = max(max((a + s for a, s in img.funcs.values()), default=0) + 4, getattr(img, "ro_top", None) or 0)
    return min(top + (top % 2), len(img.mem) - (len(img.mem) % 2))


_LOOP_AN = None  # the analysis inherited by the workers of `loop_certificates`


def _loop_job(name, abi, frame, pre=None, need_inv=False):
    import time
    import binloops
    before = set(binloops._RUNTIME_EMPTY)
    t0 = time.process_time()
    try:
        res = ("ok", binloops.certify_loops(_LOOP_AN, name, abi, frame=frame, pre=pre, need_inv=need_inv))
    except Exception as e:  # noqa: BLE001  re-raised by the caller, as in a serial run
        res = ("raise", e)
    new = {k: v for k, v in binloops._RUNTIME_EMPTY.items() if k not in before}
    return name, res + (time.process_time() - t0, dict(binloops.METER)), new


def loop_certificates(an, names, abi, frame, jobs, args=None):
    """`binloops.certify_loops` of every function of `names`, computed by `jobs` forked
    processes (`args`: {name: (precondition, need_inv)}). Each result depends only on the
    function, its arguments and `an` (the budgets are counted in
    work units per function, `binloops.FUNC_WORK`, `LP_WORK`), so the certificate is the one
    of a serial run. An exception is returned, to be raised where the serial run would
    raise it."""
    import binloops
    import concurrent.futures
    import multiprocessing
    global _LOOP_AN
    args = args or {}
    if jobs <= 1:
        global_an = _LOOP_AN
        _LOOP_AN = an
        try:
            return {n: _loop_job(n, abi, frame, *args.get(n, (None, False)))[1] for n in names}
        finally:
            _LOOP_AN = global_an
    _LOOP_AN = an
    out = {}
    try:
        ctx = multiprocessing.get_context("fork")
        with concurrent.futures.ProcessPoolExecutor(jobs, mp_context=ctx) as pool:
            futs = [pool.submit(_loop_job, n, abi, frame, *args.get(n, (None, False))) for n in names]
            for f in concurrent.futures.as_completed(futs):
                name, res, new = f.result()
                out[name] = res
                binloops._RUNTIME_EMPTY.update(new)
    finally:
        _LOOP_AN = None
    return out


def _call_graph(an, roots, names):
    """The functions reached from `roots` whose graph is built, and their callees."""
    seen, todo, names_ok, graph = set(roots), list(roots), [], {}
    while todo:
        n = todo.pop()
        try:
            _e, blocks, _ = an.cfg(n)
        except wcet.Unbounded:
            continue
        names_ok.append(n)
        graph[n] = []
        for il in blocks.values():
            for i in il:
                if i.kind == "call" and i.target in names:
                    g = names[i.target]
                    if g not in graph[n]:
                        graph[n].append(g)
                    if g not in seen:
                        seen.add(g)
                        todo.append(g)
    return names_ok, graph


def _from_js(g):
    return ({v: k for v, k in g["sv"]}, g["c"])


def _site_disjuncts(fields, a):
    """The disjuncts of the invariant at `a` (`ThumbDataCore.invsAt`), from the fields."""
    k = fields["_nodes"].index(a)
    alt = fields.get("alt") or []
    return [fields["inv"][k]] + (alt[k] if k < len(alt) else [])


def _site_proofs(fields, a, facts):
    """Farkas proofs of `facts` from each disjunct of the invariant at the call at `a` with
    the ranges (`ThumbDataCore.callObs`), in the checker's order; None if one fails."""
    import binloops
    nv = binloops.nvars(len(fields.get("slots", [])))
    rng = binloops.ranges_n(nv)
    out = []
    for I in _site_disjuncts(fields, a):
        prem = [_from_js(g) for g in I] + rng
        pr = binloops.Prover(prem, nv, facts)
        for p in facts:
            cert = pr.prove(p)
            if cert is None:
                return None
            out.append(binloops.js_proof(cert))
    return out


def context_certificates(an, names, graph, abi, frame, jobs, addr_of):
    """The loop certificates of `names`, callers first, each function that has loops given
    a precondition: the hull of the ranges of `r0`-`r3` at its calls, each fact kept only if
    the invariant of every caller proves it at every call (`_site_proofs`). The levels of the
    call graph are computed one after the other, the functions of a level in parallel. A
    function on a cycle of calls, a run-time routine or a function with a caller that gives
    no invariant gets none. Returns ({name: result of `_loop_job`}, {name: precondition})."""
    import binloops
    callers = {g: [f for f in names if g in graph.get(f, [])] for g in names}
    loopy = {}
    for g in names:
        try:
            loopy[g] = bool(binloops.structure(an, g)[5])
        except Exception:  # noqa: BLE001
            loopy[g] = False
    cand = {g for g in names if loopy[g] and callers[g] and not g.startswith("__aeabi")}
    need = {f for f in names if any(g in cand for g in graph.get(f, []))}
    # levels: a function after all its callers (Kahn); those on cycles of calls last, without
    # precondition
    indeg = {g: len([f for f in callers[g] if f != g]) for g in names}
    level = [g for g in names if indeg[g] == 0]
    done, levels = set(), []
    while level:
        levels.append(sorted(level))
        done |= set(level)
        nxt = []
        for f in level:
            for g in graph.get(f, []):
                if g in indeg and g not in done:
                    indeg[g] -= 1
                    if indeg[g] == 0 and g not in nxt:
                        nxt.append(g)
        level = nxt
    rest = sorted(set(names) - done)
    if rest:
        levels.append(rest)
    cand -= set(rest)
    results, pres = {}, {}
    for lv in levels:
        args = {}
        for g in lv:
            pre = None
            if g in cand:
                pre = _precondition(g, callers[g], results, addr_of)
            pres[g] = pre
            args[g] = (pre, g in need)
        results.update(loop_certificates(an, lv, abi, frame, jobs, args))
    return results, pres


def _precondition(g, callers, results, addr_of):
    """The precondition of `g` from the results of its callers (see `context_certificates`)."""
    import binloops
    U = binloops.U
    ga = addr_of[g]
    sites = []
    for f in callers:
        res = results.get(f)
        if res is None or res[0] != "ok":
            return None
        fields = res[1][0]
        if "inv" not in fields or "_calls" not in fields:
            return None
        sites += [(fields, a, rng) for a, t, rng in fields["_calls"] if t == ga]
    reach = [rng for _f, _a, rng in sites if rng is not None]
    if not reach:
        return None
    pre = {}
    for r in range(4):
        lo = max(0, min(rng[r][0] for rng in reach))
        hi = min(U - 1, max(rng[r][1] for rng in reach))
        # each fact kept only if every call proves it from the invariant there
        proved = lambda bnd: all(_site_proofs(fields, a, binloops.pre_lins({r: bnd})) is not None  # noqa: E731
                                 for fields, a, _rng in sites)
        lo = lo if lo > 0 and proved((lo, U - 1)) else 0
        hi = hi if hi < U - 1 and proved((0, hi)) else U - 1
        if lo > 0 or hi < U - 1:
            pre[r] = (lo, hi)
    return pre or None


def call_proofs(fields, in_cert, pre_of, names):
    """The proofs of the obligations of the calls of a function (`ThumbDataCore.callObs`, in
    its order): at each call (address order) of a function of the certificate with a
    precondition, each disjunct of the invariant, each fact."""
    import binloops
    out = []
    for a, t, _rng in fields.get("_calls", []):
        g = names.get(t)
        if g is None or g not in in_cert or not pre_of.get(g):
            continue
        ps = _site_proofs(fields, a, binloops.pre_lins(pre_of[g]))
        if ps is None:
            raise NoCertificate(f"the precondition of {g} is not proved at the call at {a:#x}")
        out += ps
    return out


def certify(an, roots, mul=None, loops=False, abi=False, stats=None, frame=False, jobs=1,
            contexts=False):
    """A certificate on the machine code for the functions reachable from `roots` (callees
    first); returns (JSON, {function: bound}, {function: reason}). With `loops`, the loop
    bounds are also certified on the machine code where `binloops.py` finds a certificate
    (format version 2; `abi`: callees assumed to preserve r4-r7 and SP; `frame`: for the
    functions that take no address of their frame, stores through other registers and calls
    assumed not to write it); `stats` (a dict) then
    receives per function the certified loops, the reasons for the others and the CPU
    seconds of their analysis. `jobs` > 1:
    the loop certificates of the functions are computed in parallel (`loop_certificates`).
    `contexts` (with `loops`): functions with loops get a precondition on their arguments
    from their calls (`context_certificates`), proved at every call by the checker; their
    bounds then hold for the calls of the program."""
    img = an.img
    base = getattr(img, "base", 0)
    addr_of = {n: a for n, (a, _) in img.funcs.items()}
    names = {a: n for n, a in addr_of.items()}
    funcs, bounds, why, active = [], {}, {}, set()
    pre = {}
    pre_of = {}
    if loops and (jobs > 1 or contexts):
        # the functions whose loops a serial run certifies: those reached from `roots`
        # whose graph is built
        names_ok, graph = _call_graph(an, roots, names)
        if contexts:
            pre, pre_of = context_certificates(an, names_ok, graph, abi, frame, jobs, addr_of)
        else:
            pre = loop_certificates(an, names_ok, abi, frame, jobs)
    cert_fields = {}

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
                if name in pre:
                    kind, res, secs, meter = pre.pop(name)
                    if kind == "raise":
                        raise res
                    fields, info, lwhy = res
                else:
                    import time
                    t0 = time.process_time()
                    fields, info, lwhy = binloops.certify_loops(an, name, abi, frame=frame)
                    secs = time.process_time() - t0
                    meter = dict(binloops.METER)
                if fields.get("unproved_jumps"):
                    raise NoCertificate("the invariants of the certificate do not bound the index of the "
                                        f"jump at {min(fields['unproved_jumps']):#x}")
                cl = [(l["header"], l["body"], l["scale"], l["bound"],
                       (l["outer"]["header"], l["outer"]["body"]) if "outer" in l else None)
                      for l in fields.get("loops", [])]
                if stats is not None:
                    stats[name] = dict(certified=info, other=lwhy, seconds=secs, meter=meter)
            fn, B = certify_function(an, name, {addr_of[n]: b for n, b in bounds.items()}, base, cl)
            private = {k: v for k, v in fields.items() if k.startswith("_")}
            fn.update({k: v for k, v in fields.items() if not k.startswith("_")})
            funcs.append(fn)
            cert_fields[name] = (fn, dict(fields, **private))
            bounds[name] = B
        except (wcet.Unbounded, NoCertificate) as e:
            why[name] = str(e)
        finally:
            active.discard(name)

    for r in roots:
        visit(r)
    if pre_of:
        # the proofs of the callees' preconditions at the calls, once the functions of the
        # certificate are known (a callee without a certificate has no obligation)
        in_cert = set(cert_fields)
        for name, (fn, fields) in cert_fields.items():
            if "_calls" in fields:
                cps = call_proofs(fields, in_cert, pre_of, names)
                if cps:
                    fn["call_proofs"] = cps
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
