#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Random loop programs: every derived loop bound is compared with executions.

    fuzz_bounds.py TOOL INCLUDE [--checker CHECKER] [--seed S] [--files N] [--functions M]
                   [--keep DIR] [-- clang flags...]

Each generated file holds M functions over `int` (or `unsigned`) parameters with small
declared ranges; their loops are drawn from shapes the analysis is meant to bound
(counters, steps, halving, doubling, reset of an inner counter, early exits) and from
arbitrary combinations of tests and updates, most of which have no bound or do not
terminate. The same file is

- analysed by the tool (report: a bound per loop, counted in executions of the body per
  entry of the loop), and
- compiled with -DRUN, which instruments every loop with a counter and runs every
  function on all the inputs of its ranges (or a sample with the corners).

A loop whose observed count exceeds its derived bound is a **violation** (exit status 1).
Runs are cut after a number of iterations (a count above the cut is still a valid
observation of a prefix). In the `int` functions the run uses 64-bit variables and a run
in which a value leaves the range of `int` is discarded: the analysis assumes that signed
overflow does not happen. In the `unsigned` functions the run uses 32-bit unsigned
variables, whose wrap-around the analysis must account for.

With --checker, the certificates of the file are also emitted and checked: a rejected
certificate is reported (a generator defect, not an unsound bound) and fails the test.
The invariants and variants that the report exports for ACSL (scripts/acsl_export.py)
are compiled into the run as checks at the start of every loop body: a false invariant, a
negative variant or one that does not decrease fails the test.
The mini-C export of each certified function (`--opt=minic`, the trusted part of a
validated certificate) is tested too: an interpreter of mini-C, written here from the Lean
definition, must count the same loop iterations as the compiled C on the same inputs.
"""
import argparse
import json
import os
import random
import subprocess
import sys
import tempfile

HEADER = r"""
#include <crosscheck/attributes.hpp>
#ifdef RUN
#include <csetjmp>
#include <cstdio>
static std::jmp_buf env;
static long cnt[64], mx[64], steps;
#define CAP 3000
#define ENTER(k) cnt[k] = 0;
static long ccfail[64][2], ccrun[64][2];
static long long ccprev[64];
#include CHECKS
#define BODY(k) if (++cnt[k] > mx[k]) mx[k] = cnt[k]; if (cnt[k] > CAP || ++steps > 200000) std::longjmp(env, 1); CCHK_##k
#define CHK(v) if ((v) > 2147483647LL || (v) < -2147483648LL) std::longjmp(env, 2);
typedef long long I;
#else
#define ENTER(k)
#define BODY(k)
#define CHK(v)
typedef int I;
#endif
typedef unsigned U;
"""


class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.lines = []
        self.loops = []  # (function, loop id within the function, line)
        self.funcs = []  # (name, [(lo, hi)], nloops, signed)

    def emit(self, text):
        self.lines.append(text)
        return len(self.lines) + HEADER.count("\n")

    # --- one function -------------------------------------------------------------
    def function(self, idx):
        r = self.rng
        self.signed = r.random() < 0.75
        # Nearly half of the signed functions stay inside the mini-C fragment (no
        # disequality, few inputs), so that the export is compared with the C.
        self.plain = self.signed and r.random() < 0.45
        self.T = "I" if self.signed else "U"
        self.name = f"f{idx}"
        np = r.randint(1, 2) if self.plain else r.randint(1, 3)
        self.ranges = []
        params = []
        for i in range(np):
            lo = r.choice([0, 0, 1, 1, 2, -3]) if self.signed else r.choice([0, 0, 1, 2])
            hi = lo + (r.choice([3, 8, 20, 40]) if self.plain else r.choice([3, 8, 20, 40, 100, 1000]))
            self.ranges.append((lo, hi))
            params.append(f"CROSSCHECK_RANGE({lo}, {hi}) {self.T} p{i}")
        self.vars = [f"p{i}" for i in range(np)]
        self.nloops = 0
        self.emit(f"CROSSCHECK_REALTIME {self.T} {self.name}({', '.join(params)}) {{")
        nl = r.randint(1, 3)
        for i in range(nl):
            init = r.choice([str(r.randint(0, 3)), r.choice(self.vars)])
            self.emit(f"  {self.T} l{i} = {init};")
        self.vars += [f"l{i}" for i in range(nl)]
        self.emit(f"  {self.T} acc = 0;")
        for _ in range(r.randint(1, 2)):
            self.loop(1, "  ")
        self.emit("  return acc;")
        self.emit("}")
        self.funcs.append((self.name, self.ranges, self.nloops, self.signed))

    def const(self):
        return self.rng.choice([0, 1, 1, 2, 3, 5, 10, 16, 50])

    def operand(self):
        return self.rng.choice(self.vars) if self.rng.random() < 0.6 else str(self.const())

    def cond(self):
        r = self.rng
        ops = ['<', '<=', '>', '>=', '<', '>'] + ([] if self.plain else ['!='])
        c = f"{r.choice(self.vars)} {r.choice(ops)} {self.operand()}"
        if r.random() < 0.2:
            c += f" && {r.choice(self.vars)} {r.choice(['<', '>', '<=', '>='])} {self.operand()}"
        return c

    def update(self, v=None):
        r = self.rng
        v = v or r.choice(self.vars)
        k = r.random()
        chk = f" CHK({v})" if self.signed else ""
        if self.plain and 0.55 <= k < 0.62:
            k = 0.5  # (a signed shift is written as a division below anyway)
        if k < 0.25:
            return f"{v} += {r.choice([1, 1, 1, 2, 3])};{chk}"
        if k < 0.45:
            return f"{v} -= {r.choice([1, 1, 1, 2, 3])};{chk}"
        if k < 0.55:
            return f"{v} = {v} / {r.choice([2, 2, 3, 4, 10])};"
        if k < 0.62:
            return f"{v} >>= {r.choice([1, 1, 2])};" if not self.signed else f"{v} = {v} / 2;"
        if k < 0.72:
            return f"{v} = {v} * {r.choice([2, 2, 3])};{chk}"
        if k < 0.78:
            return f"{v} <<= 1;{chk}" if not self.signed else f"{v} = {v} * 2;{chk}"
        if k < 0.88:
            return f"{v} = {self.operand()};"
        w = r.choice(self.vars)
        return f"{v} = {w} {r.choice(['+', '-'])} {r.choice([1, 1, 2])};{chk}"

    def body(self, depth, ind, v=None):
        r = self.rng
        for _ in range(r.randint(0, 2)):
            k = r.random()
            if k < 0.45:
                self.emit(f"{ind}{self.update()}")
            elif k < 0.8:
                self.emit(f"{ind}if ({self.cond()}) {{ {self.update()} }} else {{ {self.update()} }}")
            elif k < 0.9:
                # also in the plain functions: the export writes `break` with a flag
                self.emit(f"{ind}if ({self.cond()}) break;")
            elif depth < 2 and self.nloops < 7:
                self.loop(depth + 1, ind)
        self.emit(f"{ind}acc += 1;")

    def loop(self, depth, ind):
        r = self.rng
        k = self.nloops
        self.nloops += 1
        v = r.choice(self.vars)
        w = r.choice([x for x in self.vars if x != v] or [v])
        chk = f" CHK({v})" if self.signed else ""
        shape = r.random()
        if shape < 0.18:    # counter up to a limit
            head = f"for ({v} = {r.choice(['0', '1', w])}; {v} {r.choice(['<', '<='] if self.plain else ['<', '<=', '!='])} {self.operand()}; {v} += {r.choice([1, 1, 2, 3])})"
            tail = None
        elif shape < 0.32:  # counter down
            head = f"while ({v} {r.choice(['>', '>='] if self.plain else ['>', '>=', '!='])} {r.choice(['0', '1', w])})"
            tail = f"{v} -= {r.choice([1, 1, 2, 3])};{chk}"
        elif shape < 0.44:  # halving
            head = f"while ({v} {r.choice(['>', '>='])} {r.choice(['0', '1', '2'])})"
            tail = f"{v} = {v} / {r.choice([2, 2, 3, 4, 10])};" if r.random() < 0.6 or self.signed else f"{v} >>= {r.choice([1, 2])};"
        elif shape < 0.54:  # doubling
            head = f"for ({v} = {r.choice(['1', '1', '0', '2'])}; {v} {r.choice(['<', '<='])} {w}; {v} = {v} * {r.choice([2, 2, 3])})"
            tail = None
        elif shape < 0.66:  # inner counter reset
            head = f"while ({v} {r.choice(['<', '>'])} {self.operand()})"
            up = r.choice([f"{w} += 1;", f"{w} -= 1;"])
            adv = r.choice([f"{v} += 1;", f"{v} -= 1;", f"{v} = {v} / 2;"])
            tail = f"if ({w} {r.choice(['<', '>'])} {self.operand()}) {{ {up} }} else {{ {w} = {self.operand()}; {adv} }}"
        else:               # arbitrary
            head = f"while ({self.cond()})"
            tail = self.update()
        line = self.emit(f"{ind}ENTER({self.fid_base() + k}) {head} {{ BODY({self.fid_base() + k})")
        self.loops.append((self.name, k, line))
        self.body(depth, ind + "  ", v)
        if tail:
            self.emit(f"{ind}  {tail}")
        self.emit(f"{ind}}}")

    def fid_base(self):
        return 8 * len(self.funcs)

    # --- the file -----------------------------------------------------------------
    def source(self):
        main = ["#ifdef RUN", "int main() {"]
        for fi, (name, ranges, nloops, signed) in enumerate(self.funcs):
            total = 1
            for lo, hi in ranges:
                total *= hi - lo + 1
            T = "I" if signed else "U"
            args = ", ".join(f"({T})a{i}" for i in range(len(ranges)))
            main.append("  {")
            main.append(f"    long best[8] = {{0}}; long over = 0, cut = 0, runs = 0;")
            if total <= 4000:
                for i, (lo, hi) in enumerate(ranges):
                    main.append(f"    for (long a{i} = {lo}; a{i} <= {hi}; ++a{i})")
                main.append("    {")
            else:
                main.append("    unsigned long long seed = 88172645463325252ULL;")
                main.append("    for (int t = 0; t < 4000; ++t) {")
                for i, (lo, hi) in enumerate(ranges):
                    span = hi - lo + 1
                    main.append("      seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;")
                    main.append(f"      long a{i} = (t % 16 < 4) ? ((t >> {i}) & 1 ? {hi} : {lo}) : {lo} + (long)(seed % {span});")
            main.append(f"      for (int k = 0; k < 8; ++k) mx[{8 * fi} + k] = ccrun[{8 * fi} + k][0] = ccrun[{8 * fi} + k][1] = 0;")
            main.append("      steps = 0; ++runs;")
            main.append("      int why = setjmp(env);")
            main.append(f"      if (why == 0) {name}({args});")
            main.append("      if (why == 2) { ++over; continue; }")
            main.append("      if (why == 1) ++cut;")
            main.append(f"      for (int k = 0; k < 8; ++k) if (mx[{8 * fi} + k] > best[k]) best[k] = mx[{8 * fi} + k];")
            main.append(f"      for (int k = 0; k < 8; ++k) {{ ccfail[{8 * fi} + k][0] += ccrun[{8 * fi} + k][0]; ccfail[{8 * fi} + k][1] += ccrun[{8 * fi} + k][1]; }}")
            main.append("    }")
            main.append(f'    std::printf("{name} %ld %ld %ld", runs, over, cut);')
            main.append(f'    for (int k = 0; k < {nloops}; ++k) std::printf(" %ld", best[k]);')
            main.append('    std::printf("\\n");')
            main.append(f'    std::printf("@{name}");')
            main.append(f'    for (int k = 0; k < {nloops}; ++k) std::printf(" %ld %ld", ccfail[{8 * fi} + k][0], ccfail[{8 * fi} + k][1]);')
            main.append('    std::printf("\\n");')
            main.append("  }")
        main += ["  return 0;", "}", "#endif"]
        return HEADER + "\n".join(self.lines) + "\n" + "\n".join(main) + "\n"


# --- mini-C: an interpreter of the exported source (formalization/.../MiniCCore.lean) -----

class Unknown(Exception):
    """The run met a value or a test that mini-C does not model (`other`)."""


class Cut(Exception):
    pass


class Overflow(Exception):
    pass


class MiniC:
    CAP, STEPS = 3000, 200000  # as in HEADER

    def __init__(self, source):
        self.src = source
        self.order = []
        self.number(source)

    def number(self, s):
        k = s["s"]
        if k in ("while", "for"):
            s["_id"] = len(self.order)
            self.order.append(s)
        for key in ("init", "a", "b", "body", "inc"):
            if isinstance(s.get(key), dict) and "s" in s[key]:
                self.number(s[key])
        for c in s.get("ss", []):
            self.number(c)

    def exp(self, e, st):
        k = e["e"]
        if k == "var":
            return st.get(e["x"], 0)
        if k == "lit":
            return e["k"]
        if k == "neg":
            return -self.exp(e["a"], st)
        if k == "other":
            raise Unknown()
        a, b = self.exp(e["a"], st), self.exp(e["b"], st)
        return a + b if k == "add" else a - b if k == "sub" else a * b

    def cond(self, c, st):
        k = c["c"]
        if k == "other":
            raise Unknown()
        if k == "not":
            return not self.cond(c["a"], st)
        a, b = self.exp(c["a"], st), self.exp(c["b"], st)
        return {"<": a < b, "<=": a <= b, ">": a > b, ">=": a >= b}[c["op"]]

    def run(self, st):
        """Largest number of body executions per entry of each loop, in source order."""
        self.mx = [0] * len(self.order)
        self.steps = 0
        try:
            self.stmt(self.src, st)
        except Cut:
            pass
        return self.mx

    def stmt(self, s, st):
        k = s["s"]
        if k == "skip" or k == "cost":
            return
        if k == "assign":
            v = self.exp(s["e"], st)
            if v > 2**31 - 1 or v < -2**31:
                raise Overflow()
            st[s["x"]] = v
        elif k == "assignU":
            # In range: the value; otherwise C wraps and mini-C says nothing.
            v = self.exp(s["e"], st)
            if not 0 <= v <= s["hi"]:
                raise Unknown()
            st[s["x"]] = v
        elif k == "div":
            # The C value is one of the values mini-C allows (`divFacts`) when y >= 0;
            # for a negative y mini-C says nothing of a quotient or a remainder.
            y, c = self.exp(s["y"], st), s["c"]
            if y < 0:
                raise Unknown()
            if "old" in s:
                st[s["old"]] = y
            st[s["x"]] = y // c if s["op"] == "div" else y % c if s["op"] == "rem" else y & c
        elif k == "seq":
            for c in s["ss"]:
                self.stmt(c, st)
        elif k == "if":
            self.stmt(s["a"] if self.cond(s["c"], st) else s["b"], st)
        elif k in ("while", "for"):
            if k == "for":
                self.stmt(s["init"], st)
            n = 0
            while all(self.cond(c, st) for c in s["cs"]):
                n += 1
                if n > self.mx[s["_id"]]:
                    self.mx[s["_id"]] = n
                self.steps += 1 if n <= self.CAP else 0
                if n > self.CAP or self.steps > self.STEPS:
                    raise Cut()
                self.stmt(s["body"], st)
                if k == "for":
                    self.stmt(s["inc"], st)
        else:
            raise Unknown()


def minic_counts(fn, variables, ranges, seconds=3.0):
    """Counts of the mini-C source over all inputs of the ranges, as the C harness computes
    them; None if the source has unknowns on some run or the time is over."""
    import itertools
    import time
    name = fn["name"]
    try:
        params = [variables.index(f"{name}::p{i}") if f"{name}::p{i}" in variables else None
                  for i in range(len(ranges))]
        m = MiniC(fn["source"])
    except (KeyError, TypeError):
        return None
    best = [0] * len(m.order)
    end = time.monotonic() + seconds
    for vals in itertools.product(*[range(lo, hi + 1) for lo, hi in ranges]):
        if time.monotonic() > end:
            return None
        st = {x: v for x, v in zip(params, vals) if x is not None}
        try:
            mx = m.run(st)
        except Unknown:
            return None
        except Overflow:
            continue
        best = [max(a, b) for a, b in zip(best, mx)]
    return best


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def main():
    argv = sys.argv[1:]
    flags = []
    if "--" in argv:
        i = argv.index("--")
        argv, flags = argv[:i], argv[i + 1:]
    ap = argparse.ArgumentParser()
    ap.add_argument("tool")
    ap.add_argument("include")
    ap.add_argument("--checker")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--files", type=int, default=5)
    ap.add_argument("--functions", type=int, default=8)
    ap.add_argument("--cxx", default="g++")
    ap.add_argument("--keep", help="directory for the generated files (default: temporary)")
    a = ap.parse_args(argv)
    tmp = a.keep or tempfile.mkdtemp(prefix="fuzz-bounds-")
    os.makedirs(tmp, exist_ok=True)
    stats = dict(functions=0, loops=0, bounded=0, compared=0, tight=0, violations=0,
                 runs=0, discarded=0, certificates=0, rejected=0, timeouts=0,
                 minic_sources=0, minic_compared=0, minic_mismatches=0,
                 invariants=0, variants=0, annotation_failures=0)
    failures = []
    for n in range(a.files):
        g = Gen(random.Random(a.seed * 100003 + n))
        for i in range(a.functions):
            g.function(i)
        src = os.path.join(tmp, f"fuzz_{a.seed}_{n}.cpp")
        with open(src, "w") as f:
            f.write(g.source())
        report = src[:-4] + ".report.json"
        certs = src[:-4] + ".cert.json"
        cmd = [a.tool, f"--report={report}"]
        if a.checker:
            cmd += [f"--opt=certificates={certs}", "--opt=minic"]
        try:
            r = run(cmd + [src, "--", "-std=c++20", f"-I{a.include}"] + flags, timeout=600)
        except subprocess.TimeoutExpired:
            stats["timeouts"] += 1
            continue
        if r.returncode > 1 or not os.path.exists(report):
            failures.append(f"{src}: the tool failed (status {r.returncode})")
            continue
        rep = json.load(open(report))
        bounds = {}  # (function, line) -> bound
        for fn in rep["functions"]:
            for lp in fn.get("loops", []):
                if lp.get("verified") and lp.get("bound") is not None:
                    bounds[(fn["name"], lp["line"])] = lp["bound"]
        # The exported ACSL annotations (invariants at the loop head, variant), executed:
        # each invariant must hold whenever a body starts, the variant must be
        # non-negative there and smaller than at the previous start.
        import re
        annot = {}
        for fn in rep["functions"]:
            for lp in fn.get("loops", []):
                annot[(fn["name"], lp["line"])] = (lp.get("invariants", []), lp.get("variant", ""))
        wide = lambda e: re.sub(r"\b[A-Za-z_]\w*\b", lambda m: f"((long long)({m.group(0)}))", e)
        gid = {}
        fbase = {name: 8 * i for i, (name, _, _, _) in enumerate(g.funcs)}
        defs = {k: "" for k in range(64)}
        for name, k, line in g.loops:
            gid[(name, k)] = fbase[name] + k
            invs, var = annot.get((name, line), ([], ""))
            body = ""
            if invs:
                stats["invariants"] += len(invs)
                body += f"if (!({' && '.join('(' + wide(i) + ')' for i in invs)})) ccrun[{fbase[name] + k}][0]++; "
            if var:
                stats["variants"] += 1
                g_ = fbase[name] + k
                body += (f"{{ long long v_ = {wide(var)}; if (v_ < 0 || (cnt[{g_}] > 1 && v_ >= ccprev[{g_}])) "
                         f"ccrun[{g_}][1]++; ccprev[{g_}] = v_; }}")
            defs[fbase[name] + k] = body
        checks = src[:-4] + ".checks.h"
        with open(checks, "w") as f:
            for k in range(64):
                f.write(f"#define CCHK_{k} {defs[k]}\n")
        exe = src[:-4] + ".run"
        c = run([a.cxx, "-O1", "-w", "-DRUN", f'-DCHECKS="{checks}"', f"-I{a.include}", "-std=c++20", "-o", exe, src])
        if c.returncode != 0:
            failures.append(f"{src}: does not compile: {c.stderr[:300]}")
            continue
        try:
            out = run([exe], timeout=600).stdout
        except subprocess.TimeoutExpired:
            stats["timeouts"] += 1
            continue
        observed = {}
        for line in out.splitlines():
            w = line.split()
            if w[0].startswith("@"):
                fails = [int(x) for x in w[1:]]
                for k in range(len(fails) // 2):
                    if fails[2 * k]:
                        stats["annotation_failures"] += 1
                        failures.append(f"{src}: {w[0][1:]} loop {k}: an exported invariant is false at a loop head ({fails[2 * k]} times)")
                    if fails[2 * k + 1]:
                        stats["annotation_failures"] += 1
                        failures.append(f"{src}: {w[0][1:]} loop {k}: the exported variant is negative or does not decrease ({fails[2 * k + 1]} times)")
                continue
            observed[w[0]] = [int(x) for x in w[1:]]
        for name, k, line in g.loops:
            stats["loops"] += 1
            if name not in observed:
                continue
            obs = observed[name][3 + k]
            b = bounds.get((name, line))
            if b is None:
                continue
            stats["bounded"] += 1
            stats["compared"] += 1
            if obs == b:
                stats["tight"] += 1
            if obs > b:
                stats["violations"] += 1
                failures.append(f"{src}:{line}: {name} loop {k}: bound {b}, observed {obs}")
        for name in observed:
            stats["functions"] += 1
            stats["runs"] += observed[name][0]
            stats["discarded"] += observed[name][1]
        if a.checker and os.path.exists(certs):
            # The mini-C export, interpreted, against the compiled C: same loop counts on
            # the same inputs (functions whose inputs the harness enumerates in full).
            doc = json.load(open(certs))
            ranges = {name: rg for name, rg, _, signed in g.funcs}
            for prog in doc.get("programs", []):
                for fn in prog["functions"]:
                    if "source" not in fn or fn["name"] not in ranges or fn["name"] not in observed:
                        continue
                    stats["minic_sources"] += 1
                    rg = ranges[fn["name"]]
                    total = 1
                    for lo, hi in rg:
                        total *= hi - lo + 1
                    # Not when a C run was discarded for an overflow: it may be in a variable
                    # that mini-C does not track, and the two sets of runs would differ.
                    if total > 4000 or observed[fn["name"]][1] > 0:
                        continue
                    got = minic_counts(fn, prog["variables"], rg)
                    if got is None:
                        continue
                    stats["minic_compared"] += 1
                    want = observed[fn["name"]][3:]
                    if got != want:
                        stats["minic_mismatches"] += 1
                        failures.append(f"{src}: {fn['name']}: mini-C loop counts {got}, compiled C {want}")
            ck = run([a.checker, certs]).stdout
            for line in ck.splitlines():
                if line.startswith("ACCEPTED"):
                    stats["certificates"] += 1
                elif line.startswith("NOT VALIDATED"):
                    stats["rejected"] += 1
                    failures.append(f"{src}: {line}")
                elif line.startswith("REJECTED"):
                    stats["rejected"] += 1
                    failures.append(f"{src}: certificate rejected: {line}")
    print(json.dumps(stats))
    for f in failures:
        print("FAILURE", f)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
