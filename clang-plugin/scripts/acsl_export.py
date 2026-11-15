#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Writes copies of the analysed sources with ACSL annotations taken from CrossCheck
reports (`--report=FILE`), for a deductive verifier such as Frama-C/WP.

    acsl_export.py REPORT.json... --out DIR

For each function of a report: `requires` clauses for the declared ranges and
CROSSCHECK_REQUIRE conditions on its integer parameters; for each loop: `loop invariant`
clauses (the invariants the analysis proved at the loop head) and a `loop variant` (the
ranking potential scaled to integers, or the divided or multiplied counter of a
logarithmic loop). The annotations are comments: the files compile as before.

What this gives and what it does not:
- the annotations are *claims for another tool to prove*, in the mathematical integers of
  ACSL; CrossCheck proved them assuming that signed arithmetic does not overflow, so a
  verifier needs its own run-time-error checks (Frama-C: -wp-rte) to discharge them;
- a variant proves termination of the loop, not CrossCheck's numeric bound; the bound is
  written as a comment next to it;
- no `assigns` clauses and no invariants about memory are produced, so loops that write
  through pointers will need them added by hand;
- do-while loops get no annotation; a loop in a macro is annotated at its expansion.
The export is tested by executing the annotations as run-time checks on random programs
(tests/fuzz_bounds.py); it has not been run through Frama-C in this repository.
"""
import argparse
import collections
import json
import os
import pathlib
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("reports", nargs="+")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    inserts = collections.defaultdict(list)  # file -> [(line, column, text)]
    for rp in a.reports:
        for fn in json.load(open(rp))["functions"]:
            if fn.get("requires"):
                text = "/*@ " + " ".join(f"requires {r};" for r in fn["requires"]) + " */\n"
                inserts[fn["file"]].append((fn["line"], 0, text))
            for lp in fn.get("loops", []):
                parts = [f"loop invariant {i};" for i in lp.get("invariants", [])]
                if lp.get("variant"):
                    parts.append(f"loop variant {lp['variant']};")
                if not parts:
                    continue
                note = f" /* CrossCheck: at most {lp['bound']} executions of the body */" if lp.get("verified") else ""
                inserts[lp["file"]].append((lp["line"], lp["column"], "/*@ " + " ".join(parts) + " */" + note + " "))
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    n = 0
    for path, ins in inserts.items():
        try:
            lines = open(path).read().split("\n")
        except OSError as e:
            print(f"skipped {path}: {e}", file=sys.stderr)
            continue
        # From the end of the file, so that earlier positions stay valid; a set, since a
        # function analysed in several reports yields the same annotation several times.
        for line, col, text in sorted(set(ins), reverse=True):
            if not 1 <= line <= len(lines):
                continue
            s = lines[line - 1]
            if col == 0:
                indent = s[:len(s) - len(s.lstrip())]
                lines[line - 1] = indent + text + s
            else:
                lines[line - 1] = s[:col - 1] + text + s[col - 1:]
            n += 1
        (out / os.path.basename(path)).write_text("\n".join(lines))
    print(f"{n} annotations in {len(inserts)} file(s), written to {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
