#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Mutation test of the checker program.

    mutate_certificates.py CHECKER FILE.json... [--mutants N] [--runs R] [--seed S]

For each certificate file (version 2), first the unchanged programs: every program that
`crosscheck-check` accepts is run by the independent interpreter (cert_interp.py) and no
run may exceed a bound. Then N mutants: one integer of one function (a coefficient, a
weight, a bound, a multiplier, an index) is changed, the checker is run on the mutant,
and

- a mutant the checker rejects counts as *killed*;
- a mutant the checker accepts is run by the interpreter (for a limited time per function): a run that exceeds the claimed
  bound, or ends outside the postcondition, is a **failure** of the checker program
  (exit status 1). Accepted mutants without such a run are still correct certificates
  (for instance a larger bound, or a different but valid Farkas certificate).

The Lean theorem `program_sound` says that no failure can exist for the function `check`;
this test covers what the theorem does not: the JSON reader and the main program.
"""
import argparse
import copy
import json
import os
import random
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert_interp  # noqa: E402


def int_sites(node, path, out):
    if isinstance(node, bool):
        return
    if isinstance(node, int):
        out.append(path)
    elif isinstance(node, list):
        for i, v in enumerate(node):
            int_sites(v, path + [i], out)
    elif isinstance(node, dict):
        for k, v in node.items():
            if k in ("source", "source_refused", "name"):
                continue
            int_sites(v, path + [k], out)


def get(node, path):
    for p in path:
        node = node[p]
    return node


def put(node, path, v):
    for p in path[:-1]:
        node = node[p]
    node[path[-1]] = v


def mutate(v, rng):
    return rng.choice([v + 1, v - 1, 0, -v, 2 * v, v // 2, v + rng.choice([2, 5, 10, 100]),
                       v - rng.choice([2, 5, 10, 100])])


def accepted(checker, program, tmp):
    path = os.path.join(tmp, "m.json")
    with open(path, "w") as f:
        json.dump({"format": "crosscheck-certificates", "version": 2, "programs": [program]}, f)
    r = subprocess.run([checker, path], capture_output=True, text=True)
    for line in r.stdout.splitlines():
        if line.startswith("PROGRAM"):
            return ": ACCEPTED" in line
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("checker")
    ap.add_argument("files", nargs="+")
    ap.add_argument("--mutants", type=int, default=300, help="per file")
    ap.add_argument("--runs", type=int, default=60, help="interpreter runs per function")
    ap.add_argument("--seconds", type=float, default=0.5, help="interpreter time per function")
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    total = killed = survived = failures = base_ok = probes = detected = 0
    with tempfile.TemporaryDirectory() as tmp:
        for path in a.files:
            doc = json.load(open(path))
            if doc.get("version") != 2:
                continue
            for program in doc["programs"]:
                for fn in program["functions"]:
                    fn.pop("source", None)  # validation is tested elsewhere
                if not accepted(a.checker, program, tmp):
                    continue
                for i in range(len(program["functions"])):
                    v = cert_interp.violation(program, i, rng, a.runs, a.seconds)
                    if v:
                        print(f"FAILURE (unchanged certificate) {path}: {v}")
                        failures += 1
                base_ok += 1
                # Self-test of the interpreter: with the bound halved (not shown to the
                # checker), a run above it should usually be found.
                for i, fn in enumerate(program["functions"]):
                    b = fn["bound"]
                    c = b if isinstance(b, int) else b.get("c", 0)
                    if fn.get("body") is None or c < 2:
                        continue
                    low = copy.deepcopy(program)
                    low["functions"][i]["bound"] = c // 2
                    probes += 1
                    if cert_interp.violation(low, i, rng, a.runs, a.seconds):
                        detected += 1
                sites = []
                int_sites(program["functions"], [], sites)
                if not sites:
                    continue
                for _ in range(a.mutants):
                    site = rng.choice(sites)
                    m = copy.deepcopy(program)
                    old = get(m["functions"], site)
                    new = mutate(old, rng)
                    if new == old:
                        continue
                    put(m["functions"], site, new)
                    total += 1
                    if not accepted(a.checker, m, tmp):
                        killed += 1
                        continue
                    survived += 1
                    for i in range(site[0], len(m["functions"])):
                        v = cert_interp.violation(m, i, rng, a.runs, a.seconds)
                        if v:
                            failures += 1
                            print(f"FAILURE {path}: mutant accepted, {'/'.join(map(str, site))}: "
                                  f"{old} -> {new}; {v}")
                            break
    print(f"programs accepted unchanged: {base_ok}; mutants: {total}, rejected: {killed}, "
          f"accepted: {survived}, accepted with a run above the bound: {failures}")
    print(f"interpreter self-test: a halved bound is exceeded by a run in {detected} of {probes} functions")
    return 1 if failures or (probes and not detected) else 0


if __name__ == "__main__":
    sys.exit(main())
