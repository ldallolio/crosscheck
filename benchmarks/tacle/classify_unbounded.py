#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Classifies the loops of the TACLeBench kernels that receive no bound, by the cause that
the analyser states in its diagnostic ("cannot derive an iteration bound for this loop
(cause)").

    classify_unbounded.py [--work DIR] [--list]

Reads the reports that `run_tacle.py` left in `.cache/work/<kernel>.json` (run it first)
and the concatenated sources next to them. A loop is counted if it has a `loopbound`
flow fact and no bound for every call, as in the column "No bound" of `run_tacle.py`.
The cause is a hint computed where the loop starts; it is not a proof that no bound
exists. The classes:

    memory    the test does not depend on a tracked integer variable (it reads memory, a
              floating-point value, a pointer or the result of a call)
    range     a variable of the test has no known range, or no bound on the side that
              matters, where the loop starts (a parameter, a global, a value read)
    potential the variables of the test are bounded where the loop starts, but no affine
              or logarithmic potential was found (a product, a data-driven update)
    notest    the loop has no test (`while (1)`) and no bounded counter controls its exits
    callee    no diagnostic of this loop: an error inside its body (a call of a function
              without a bound) stopped the analysis of the function before the loop
"""
import argparse
import collections
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from run_tacle import pragmas  # noqa: E402


def cause(msg):
    if "its test does not depend on a tracked integer variable" in msg:
        return "memory"
    if "the loop has no test" in msg:
        return "notest"
    if "are bounded where the loop starts" in msg:
        return "potential"
    if "where the loop starts" in msg:
        return "range"
    return "other"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--work", default=str(HERE / ".cache" / "work"))
    ap.add_argument("--kernels", default=str(HERE / ".cache" / "tacle-bench" / "bench" / "kernel"))
    ap.add_argument("--list", action="store_true", help="print every loop with its class")
    a = ap.parse_args()
    work = pathlib.Path(a.work)
    total = collections.Counter()
    loops = unbounded = 0
    for k in sorted(p.name for p in pathlib.Path(a.kernels).iterdir() if p.is_dir()):
        rep = json.loads((work / f"{k}.json").read_text())
        bounded, msgs = set(), {}
        for f in rep["functions"]:
            for lp in f.get("loops") or []:
                if lp.get("verified") and lp.get("bound") is not None:
                    bounded.add(lp["line"])
            for e in f.get("errors") or []:
                m = re.match(r"line (\d+): cannot derive an iteration bound for this loop(.*)", e)
                if m:
                    msgs[int(m.group(1))] = m.group(2)
        for line in sorted(pragmas((work / f"{k}.c").read_text(errors="replace").splitlines())):
            loops += 1
            if line in bounded:
                continue
            unbounded += 1
            c = cause(msgs[line]) if line in msgs else "callee"
            total[c] += 1
            if a.list:
                print(f"{k}:{line}: {c}{msgs.get(line, '')[:110]}")
    print(json.dumps(dict(loops=loops, unbounded=unbounded, **dict(total.most_common()))))


if __name__ == "__main__":
    main()
