#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Compare the loops certified on the machine code by two runs of `run_cycles.py
--certify-loops --json`: loops lost, gained, certified bounds higher or lower.

    python3 benchmarks/cycles/compare_runs.py OLD.json NEW.json [--check] [--quiet]

With `--check`, exits with status 1 if a loop certified by OLD is not certified by NEW or
gets a higher bound (the regression check after a change of the producer). Only kernels
present in both runs are compared, so that a run on a subset (`--only`) can be compared
with a full one. The run-time division routines (`__aeabi_*`) are left out.
"""
import argparse
import collections
import json
import sys


def load(path):
    d = json.load(open(path))
    loops, secs, runtime = {}, {}, 0
    for k in d["kernels"]:
        secs[k["kernel"]] = k.get("seconds", 0)
        for fn, v in k.get("loops_detail", {}).items():
            if fn.startswith("__aeabi"):
                runtime += len(v["certified"])
                continue
            for c in v["certified"]:
                loops[(k["kernel"], fn, c[0])] = tuple(c[1:])
    return loops, secs, runtime


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("old")
    ap.add_argument("new")
    ap.add_argument("--check", action="store_true", help="fail on a lost loop or a higher bound")
    ap.add_argument("--quiet", action="store_true", help="counts only")
    a = ap.parse_args()
    a_loops, a_secs, a_rt = load(a.old)
    b_loops, b_secs, b_rt = load(a.new)
    common = set(a_secs) & set(b_secs)
    a_loops = {k: v for k, v in a_loops.items() if k[0] in common}
    b_loops = {k: v for k, v in b_loops.items() if k[0] in common}
    lost = sorted(k for k in a_loops if k not in b_loops)
    gained = sorted(k for k in b_loops if k not in a_loops)
    higher = sorted(k for k in a_loops if k in b_loops and b_loops[k][0] > a_loops[k][0])
    lower = sorted(k for k in a_loops if k in b_loops and b_loops[k][0] < a_loops[k][0])
    print(f"kernels compared {len(common)}; loops certified {len(a_loops)} -> {len(b_loops)}; "
          f"gained {len(gained)}, lost {len(lost)}, higher {len(higher)}, lower {len(lower)}; "
          f"loops of the run-time routines certified {a_rt} -> {b_rt} (not compared)")
    if not a.quiet:
        show = lambda k, v: f"  {k[0]} {k[1]} {hex(k[2])} {v}"  # noqa: E731
        for name, keys in (("lost", lost), ("higher", higher), ("lower", lower), ("gained", gained)):
            for k in keys:
                print(name, show(k, (a_loops.get(k), b_loops.get(k))))
        if gained:
            print("gained per kernel:", dict(collections.Counter(k[0] for k in gained)))
    if a.check and (lost or higher):
        sys.exit(1)


if __name__ == "__main__":
    main()
