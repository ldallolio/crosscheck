#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""An interpreter of certificate programs, independent of the Lean checker.

It runs the program of a certificate (docs/certificate-format.md, version 2) on states
that satisfy the precondition, with the cost semantics of `ACmd.toCmd`
(formalization/ImperativeOptimization/Checker.lean): an atom costs its weight, a test its
weight, a call its weight plus the callee. Unknown values are drawn at random, with a
preference for extreme values. A run is stopped as soon as its cost exceeds the claimed
bound: that is a *violation* of the claim "every execution from the precondition costs at
most the bound". It is used to test the checker program as a whole (its unverified JSON
reader included): no certificate that `crosscheck-check` accepts may have a violation
(see mutate_certificates.py). The annotations (invariants, potentials, Farkas
certificates) are ignored: only the program, the precondition, the bound and the
postcondition are read.

An assumed contract (a function without a body) costs its bound and gives its `mods`
arbitrary values that satisfy its postcondition.
"""
import sys
import time

sys.setrecursionlimit(100000)

EXTREMES = [0, 1, -1, 2, 3, 7, 10, 64, 100, 1000, 4096, 65536, -1000, 2**31 - 1, -(2**31)]


class Exceeded(Exception):
    pass


class OutOfTime(Exception):
    pass


class Blocked(Exception):
    """No value satisfies the constraints of a `havocC`: the execution has no continuation."""


def dot(v, s):
    return sum(c * s.get(i, 0) for i, c in enumerate(v) if c)


def pexp(e, s):
    return dot(e.get("sv", []), s) + e.get("c", 0)


def lin(e, rho, s):
    return dot(e.get("sv", []), s) + dot(e.get("lv", []), rho) + e.get("c", 0)


def sb(b, rho):
    if isinstance(b, int):
        return b
    return (b.get("c", 0) + sum(c * max(0, rho.get(j, 0)) for j, c in enumerate(b.get("co", [])) if c)
            + sum(a * max(0, rho.get(i, 0)) * max(0, rho.get(j, 0)) for a, i, j in b.get("q", [])))


def interval(constraints, x, s, rho=None):
    """Bounds of variable x under affine constraints (each `<= 0`), the others fixed."""
    lo, hi = None, None
    for g in constraints:
        sv = g.get("sv", [])
        a = sv[x] if x < len(sv) else 0
        rest = sum(c * s.get(i, 0) for i, c in enumerate(sv) if c and i != x) + g.get("c", 0)
        if rho is not None:
            rest += dot(g.get("lv", []), rho)
        if a == 0:
            if rest > 0:
                return 1, 0  # empty
            continue
        # a*x + rest <= 0
        if a > 0:
            b = (-rest) // a
            hi = b if hi is None else min(hi, b)
        else:
            b = -((-rest) // (-a))  # x >= rest / (-a), rounded up
            lo = b if lo is None else max(lo, b)
    return lo, hi


def draw(rng, lo, hi):
    if lo is not None and hi is not None:
        if lo > hi:
            raise Blocked()
        r = rng.random()
        if r < 0.3:
            return hi
        if r < 0.6:
            return lo
        return rng.randint(lo, hi)
    cands = [v for v in EXTREMES if (lo is None or v >= lo) and (hi is None or v <= hi)]
    if lo is not None:
        cands += [lo, lo + 1]
    if hi is not None:
        cands += [hi, hi - 1]
    return rng.choice(cands)


class Run:
    def __init__(self, program, rng, limit, deadline=None):
        self.fns = program["functions"]
        self.rng = rng
        self.limit = limit
        self.cost = 0
        self.deadline = deadline
        self.ticks = 0

    def pay(self, w):
        self.cost += w
        if self.cost > self.limit:
            raise Exceeded()

    def exec(self, n, s):
        k = n["node"]
        if k == "skip":
            return
        if k == "assign":
            self.pay(n["w"])
            s[n["x"]] = pexp(n["a"], s)
        elif k == "havoc":
            self.pay(n["w"])
            s[n["x"]] = draw(self.rng, None, None)
        elif k == "havocC":
            self.pay(n["w"])
            lo, hi = interval(n["cs"], n["x"], s)
            s[n["x"]] = draw(self.rng, lo, hi)
        elif k == "assume":
            self.pay(n["w"])
            if not all(pexp(g, s) <= 0 for g in n["cs"]):
                raise Blocked()
        elif k == "seq":
            self.exec(n["c1"], s)
            self.exec(n["c2"], s)
        elif k == "ite":
            self.pay(n["w"])
            self.exec(n["c1"] if pexp(n["g"], s) <= 0 else n["c2"], s)
        elif k in ("while", "whileAnd", "whileLog", "whileGrow", "whileUp", "whileSz"):
            gs = [n["g"]] if k == "while" else n["gs"]
            while True:
                self.ticks += 1
                if self.deadline and self.ticks % 512 == 0 and time.monotonic() > self.deadline:
                    raise OutOfTime()
                self.pay(n["w"])
                if not all(pexp(g, s) <= 0 for g in gs):
                    break
                self.exec(n["body"], s)
        elif k == "weaken" or k == "dead":
            self.exec(n["c"], s)
        elif k == "call":
            self.pay(n["w"])
            f = self.fns[n["f"]]
            if f.get("body") is not None:
                self.exec(f["body"], s)
            else:
                rho = {j: pexp(e, s) for j, e in enumerate(n.get("inst", []))}
                self.pay(sb(f["bound"], rho))
                for _ in range(50):
                    t = dict(s)
                    for x in f.get("mods", []):
                        t[x] = draw(self.rng, None, None)
                    for x in f.get("mods", []):  # then pull each into its interval
                        lo, hi = interval(f.get("post", []), x, t, rho)
                        try:
                            t[x] = draw(self.rng, lo, hi)
                        except Blocked:
                            break
                    if all(lin(e, rho, t) <= 0 for e in f.get("post", [])):
                        s.clear()
                        s.update(t)
                        return
                raise Blocked()
        else:
            raise ValueError("unknown node " + k)


def initial(fn, nvars, rng):
    """A state and a valuation of the logical variables that satisfy the precondition."""
    pre = fn.get("pre", [])
    single = [g for g in pre if not any(g.get("lv", []))]
    nl = max([len(g.get("lv", [])) for g in pre] + [0])
    for _ in range(200):
        s = {}
        try:
            for x in range(nvars):
                only = [g for g in single if sum(1 for c in g.get("sv", []) if c) == 1
                        and x < len(g["sv"]) and g["sv"][x]]
                lo, hi = interval(only, x, s)
                s[x] = draw(rng, lo, hi)
        except Blocked:
            continue
        rho = {}
        for j in range(nl):
            for g in pre:
                lv = g.get("lv", [])
                if j < len(lv) and lv[j] and sum(1 for c in lv if c) == 1:
                    num = -(dot(g.get("sv", []), s) + g.get("c", 0))
                    if num % lv[j] == 0:
                        rho[j] = num // lv[j]
                        break
            rho.setdefault(j, 0)
        if all(lin(g, rho, s) <= 0 for g in pre):
            return s, rho
    return None


def violation(program, index, rng, runs=200, seconds=None):
    """A description of a run of function `index` that exceeds its bound or ends outside
    its postcondition, or None (also when `seconds` have passed without one)."""
    deadline = time.monotonic() + seconds if seconds else None
    fn = program["functions"][index]
    if fn.get("body") is None:
        return None
    nvars = len(program.get("variables", []))
    for _ in range(runs):
        init = initial(fn, nvars, rng)
        if init is None:
            return None  # no state found in the precondition: nothing to test
        s, rho = init
        start = dict(s)
        if deadline and time.monotonic() > deadline:
            return None
        run = Run(program, rng, sb(fn["bound"], rho), deadline)
        try:
            run.exec(fn["body"], s)
        except OutOfTime:
            return None
        except Exceeded:
            return f"{fn['name']}: cost exceeds {run.limit} from {start} with gamma {rho}"
        except Blocked:
            continue
        bad = [e for e in fn.get("post", []) if lin(e, rho, s) > 0]
        if bad:
            return f"{fn['name']}: postcondition {bad[0]} false after a run from {start}"
    return None
