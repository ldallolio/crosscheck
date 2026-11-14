#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Compares the FFX flow facts written by CrossCheck (run_tacle.py --flow-facts DIR,
in-context bounds) with the FFX files written by oRange (results/orange/, see
README.md), loop by loop. Both are read the same way: every <loop> element with a
source, a line and a numeric maxcount; for oRange, the maximum over its calling
contexts. Loops are matched by file name (without directory) and line.

    python3 benchmarks/tacle/compare_ffx.py DIR [--orange-dir results/orange]
"""
import argparse
import pathlib
import sys
import xml.etree.ElementTree as ET

HERE = pathlib.Path(__file__).resolve().parent


def loops(path):
    out = {}
    try:
        root = ET.parse(path).getroot()
    except (ET.ParseError, FileNotFoundError):
        return None
    for l in root.iter("loop"):
        src, line, mx = l.get("source"), l.get("line"), l.get("maxcount")
        if src and line and mx and mx.isdigit():
            k = (pathlib.Path(src).name, int(line))
            out[k] = max(out.get(k, 0), int(mx))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dir")
    ap.add_argument("--orange-dir", default=str(HERE / "results/orange"))
    a = ap.parse_args()
    tot = dict(both=0, equal=0, crosscheck_larger=0, orange_larger=0, crosscheck_only=0, orange_only=0)
    diffs = []
    for ours in sorted(pathlib.Path(a.dir).glob("*.ffx")):
        k = ours.stem
        cc = loops(ours)
        orng = loops(pathlib.Path(a.orange_dir) / f"{k}.xml") or {}
        if cc is None:
            sys.exit(f"{ours}: not well-formed XML")
        for key in set(cc) | set(orng):
            if key in cc and key in orng:
                tot["both"] += 1
                if cc[key] == orng[key]:
                    tot["equal"] += 1
                else:
                    tot["crosscheck_larger" if cc[key] > orng[key] else "orange_larger"] += 1
                    diffs.append(f"{k} line {key[1]}: CrossCheck {cc[key]}, oRange {orng[key]}")
            elif key in cc:
                tot["crosscheck_only"] += 1
            else:
                tot["orange_only"] += 1
    print(" ".join(f"{n}={v}" for n, v in tot.items()))
    for d in diffs:
        print("  " + d)


if __name__ == "__main__":
    main()
