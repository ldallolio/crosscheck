#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""The certificate checker's JSON reader (`ImperativeOptimization/JsonCore.lean`) against
`Lean.Json.parse`, through `lake exe json-differential` (`test/JsonDifferential.lean`).

Documents: generated values (nesting, Unicode and escapes, integers beyond 64 bits, fractions),
printed in several layouts, which both readers must read alike (AGREE); malformed texts
(cut, altered, and a list of classic mistakes), which the checker's reader must refuse whenever
Lean's does (never LEANERR); and texts where it is stricter on purpose (repeated keys, lone
surrogates: COREERR, or BOTHERR/AGREE where Lean is as strict; an exponent of more than five
digits refused; exponents, read as integers by Lean and as other numbers by the
checker: AGREE or DIFF). Exit status 1 on any other outcome.

    python3 test/json_differential.py [--exe PATH] [--count N] [--seed S]
"""
import argparse
import json
import os
import pathlib
import random
import re
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
EXE = HERE.parent / ".lake" / "build" / "bin" / "json-differential"

ALPHABET = "abcXYZ019 _-\"\\/\b\f\n\r\t\u00e9\u20ac\U0001F600\u0001\u001f\u007f"


def rstring(r):
    return "".join(r.choice(ALPHABET) for _ in range(r.randint(0, 8)))


def rnumber(r):
    k = r.random()
    if k < 0.4:
        return r.randint(-1000, 1000)
    if k < 0.7:
        return r.randint(-(1 << 70), 1 << 70)
    return round(r.uniform(-1e6, 1e6), r.randint(1, 6))


def rvalue(r, depth=0):
    k = r.random()
    if depth > 6 or k < 0.35:
        return r.choice([None, True, False, rnumber(r), rnumber(r), rstring(r)])
    if k < 0.65:
        return [rvalue(r, depth + 1) for _ in range(r.randint(0, 5))]
    keys = list({rstring(r) for _ in range(r.randint(0, 5))})
    return {key: rvalue(r, depth + 1) for key in keys}


def dump(r, v):
    opts = r.choice([dict(), dict(indent=2), dict(separators=(",", ":")),
                     dict(ensure_ascii=False), dict(indent="\t", ensure_ascii=False)])
    s = json.dumps(v, **opts)
    if r.random() < 0.3:
        s = r.choice([" ", "\n", "\r\n", "\t"]) + s + r.choice(["", " ", "\n"])
    return s


MALFORMED = [
    "", " ", "nul", "tru", "True", "NaN", "Infinity", "-Infinity", "01", "-01", "00", "-",
    "1.", ".5", "+1", "1e", "1e+", "0x10", "[1,]", "[,1]", "[1 2]", "{\"a\":1,}", "{\"a\" 1}",
    "{a:1}", "{'a':1}", "'a'", "\"a", "\"\\x\"", "\"\\u12\"", "\"\\u12g4\"", "\"a\nb\"",
    "\"\t\"", "[1]x", "{} {}", "[[[]]", "{\"a\":[}", "\"\\\"", "[1,2", "{\"a\":1 \"b\":2}",
    "\u00a0[]", "[\u00a01]", "/* c */ 1", "1 // c", "[1]]", "\"\x00\"",
]
STRICT = ["{\"a\":1,\"a\":2}", "{\"k\":{\"x\":1,\"x\":1}}", "[{\"a\":1,\"b\":2,\"a\":3}]",
          "\"\\ud800\"", "\"\\udc00\"", "\"\\ud800x\"", "\"\\ud800\\u0041\""]
EXPONENT = ["1e2", "1E2", "-1e+2", "2.5e-1", "[1e0]", "{\"a\":10e3}", "0e0", "1.0", "1.50", "-0.0"]


def mutate(r, s):
    if not s:
        return "x"
    i = r.randrange(len(s))
    k = r.random()
    if k < 0.4:
        return s[:i]
    if k < 0.7:
        return s[:i] + r.choice("{}[],:\"\\ 0a-.e") + s[i + 1:]
    return s[:i] + r.choice("{}[],:\"\\0-") + s[i:]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--exe", default=str(EXE))
    ap.add_argument("--count", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    r = random.Random(a.seed)
    docs = []   # (text, allowed outcomes)
    for _ in range(a.count):
        docs.append((dump(r, rvalue(r)), {"AGREE"}))
    for _ in range(a.count):
        s = mutate(r, dump(r, rvalue(r)))
        # a mutation may write an exponent: Lean may read it as an integer, the checker not
        docs.append((s, {"AGREE", "BOTHERR", "COREERR"} | ({"DIFF"} if re.search(r"[0-9][eE]", s) else set())))
    docs += [(s, {"BOTHERR", "COREERR"}) for s in MALFORMED]
    docs += [(s, {"COREERR", "BOTHERR", "AGREE"}) for s in STRICT]
    docs += [(s, {"AGREE", "DIFF"}) for s in EXPONENT]
    with tempfile.TemporaryDirectory() as d:
        files = []
        for k, (s, _ok) in enumerate(docs):
            p = os.path.join(d, f"{k}.json")
            with open(p, "w", encoding="utf-8", newline="") as f:
                f.write(s)
            files.append(p)
        out = {}
        for i in range(0, len(files), 400):
            res = subprocess.run([a.exe, *files[i:i + 400]], capture_output=True, text=True)
            if res.returncode != 0:
                sys.exit(f"json-differential failed: {res.stderr[-2000:]}")
            for line in res.stdout.splitlines():
                path, outcome = line.split(" ", 2)[:2]
                out[path] = outcome
    bad = [(s, out.get(p)) for p, (s, ok) in zip(files, docs) if out.get(p) not in ok]
    counts = {}
    for p in files:
        counts[out.get(p)] = counts.get(out.get(p), 0) + 1
    print(f"{len(docs)} documents: {counts}")
    for s, o in bad[:20]:
        print(f"unexpected {o}: {s[:120]!r}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
