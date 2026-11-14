#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Compares two sets of CrossCheck reports (`--report=FILE` JSON), function by
function: the "cost diff" of a change, for code review and CI.

    cost_diff.py BASE HEAD [--max-increase PCT] [--exact] [--markdown FILE]
    cost_diff.py --snapshot REPORTS OUT.json

BASE and HEAD are report files, directories of report files (*.json), or snapshots.
A snapshot keeps, per function, only what is compared (file name without directory,
qualified name, accepted or not, bound): small, and free of machine-specific paths,
so that it can be committed as a baseline.

Functions are matched by source file name (without directory) and qualified name.

Exit status 1 (and the reason on stderr) when, from BASE to HEAD:
  * a function that was accepted is rejected, or loses its bound;
  * a bound grows by more than PCT percent (--max-increase; 0 means any growth);
  * with --exact, anything changes (functions added, removed, or a different bound;
    used to keep stored figures, e.g. Table tab:plugin, in step with the analyser).
Otherwise 0. --markdown writes the table, e.g. for a pull-request comment.
"""
import argparse
import json
import pathlib
import sys


def load(path):
    p = pathlib.Path(path)
    files = sorted(p.glob("*.json")) if p.is_dir() else [p]
    out = {}
    for f in files:
        for fn in json.loads(f.read_text()).get("functions", []):
            key = (pathlib.Path(fn.get("file") or "").name, fn["name"])
            out[key] = fn
    return out


def describe(fn):
    if fn is None:
        return "—"
    if fn.get("wcet") is None:
        return "no bound"
    return f"{fn['wcet']}" + ("" if fn.get("ok") else " (rejected)")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("base")
    ap.add_argument("head", nargs="?")
    ap.add_argument("--snapshot", metavar="OUT", help="write a snapshot of BASE to OUT and exit")
    ap.add_argument("--max-increase", type=float, help="allowed growth of a bound, in percent")
    ap.add_argument("--exact", action="store_true", help="fail on any change")
    ap.add_argument("--markdown", help="write a Markdown table to this file")
    a = ap.parse_args()
    if a.snapshot:
        fns = [dict(file=k[0], name=k[1], ok=bool(f.get("ok")), wcet=f.get("wcet"))
               for k, f in sorted(load(a.base).items())]
        pathlib.Path(a.snapshot).write_text(json.dumps({"functions": fns}, indent=1) + "\n")
        return
    if a.head is None:
        ap.error("HEAD is required")
    base, head = load(a.base), load(a.head)
    rows, failures = [], []
    for key in sorted(set(base) | set(head)):
        b, h = base.get(key), head.get(key)
        name = f"{key[1]} ({key[0]})"
        change = ""
        if b and h and b.get("wcet") is not None and h.get("wcet") is not None:
            d = h["wcet"] - b["wcet"]
            pct = 100.0 * d / b["wcet"] if b["wcet"] else (0.0 if d == 0 else float("inf"))
            change = "=" if d == 0 else f"{d:+d} ({pct:+.1f}%)"
            if a.max_increase is not None and pct > a.max_increase:
                failures.append(f"{name}: bound {b['wcet']} -> {h['wcet']} ({pct:+.1f}%)")
        if b and h:
            if b.get("ok") and not h.get("ok"):
                failures.append(f"{name}: accepted before, rejected now")
            elif b.get("wcet") is not None and h.get("wcet") is None:
                failures.append(f"{name}: lost its bound")
        if a.exact and (b is None or h is None or b.get("wcet") != h.get("wcet") or b.get("ok") != h.get("ok")):
            failures.append(f"{name}: {describe(b)} -> {describe(h)}")
        if b is None or h is None or describe(b) != describe(h):
            rows.append((name, describe(b), describe(h), change or ("new" if b is None else "removed" if h is None else "")))
    table = ["| Function | Before | After | Change |", "|---|---|---|---|"]
    table += [f"| `{r[0]}` | {r[1]} | {r[2]} | {r[3]} |" for r in rows]
    summary = (f"{len(rows)} of {len(set(base) | set(head))} functions changed"
               if rows else f"no change in {len(set(base) | set(head))} functions")
    print(summary)
    for r in rows:
        print(f"  {r[0]}: {r[1]} -> {r[2]} {r[3]}")
    if a.markdown:
        pathlib.Path(a.markdown).write_text(
            "### CrossCheck cost bounds\n\n" + summary + "\n\n" + ("\n".join(table) + "\n" if rows else ""))
    if failures:
        sys.stderr.write("cost regression:\n" + "".join(f"  {f}\n" for f in failures))
        sys.exit(1)


if __name__ == "__main__":
    main()
