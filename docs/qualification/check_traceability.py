#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Checks requirements.yaml against the repository: every requirement has evidence, every
Lean name is declared in the file it is said to be in, every test file exists, every CI
step is present in its workflow. Prints the traceability matrix (Markdown).

    check_traceability.py [--root REPO]

The YAML subset used by requirements.yaml is read here without an external package.
"""
import argparse
import pathlib
import re
import sys


def parse(text):
    """requirements.yaml: a list of {id, text, evidence: [flow mappings]}."""
    reqs, cur, in_text = [], None, False
    for raw in text.splitlines():
        line = raw.rstrip()
        if not line or line.lstrip().startswith("#"):
            continue
        m = re.match(r"\s*- id: (\S+)", line)
        if m:
            cur = dict(id=m.group(1), text="", evidence=[])
            reqs.append(cur)
            in_text = False
            continue
        if cur is None:
            continue
        if re.match(r"\s*text: >", line):
            in_text = True
            continue
        if re.match(r"\s*evidence:", line):
            in_text = False
            continue
        m = re.match(r"\s*- \{(.*)\}\s*$", line)
        if m:
            ev = {}
            for k, v in re.findall(r'(\w+): (\[[^\]]*\]|"[^"]*"|[^,]+)', m.group(1)):
                v = v.strip()
                ev[k] = [x.strip() for x in v[1:-1].split(",")] if v.startswith("[") else v.strip('"')
            cur["evidence"].append(ev)
        elif in_text:
            cur["text"] += line.strip() + " "
    return reqs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(pathlib.Path(__file__).resolve().parents[2]))
    a = ap.parse_args()
    root = pathlib.Path(a.root)
    reqs = parse((root / "docs/qualification/requirements.yaml").read_text())
    bad = []
    print("| Requirement | Proofs (Lean) | Tests | Other |")
    print("|---|---|---|---|")
    for r in reqs:
        proofs, tests, other = [], [], []
        if not r["evidence"]:
            bad.append(f"{r['id']}: no evidence")
        for ev in r["evidence"]:
            kind = ev.get("kind")
            if kind == "proof":
                src = (root / ev["file"]).read_text() if (root / ev["file"]).exists() else None
                if src is None:
                    bad.append(f"{r['id']}: missing file {ev['file']}")
                    continue
                for name in ev["lean"]:
                    if not re.search(rf"^\s*(theorem|lemma|def|structure|inductive|abbrev) {re.escape(name)}\b", src, re.M):
                        bad.append(f"{r['id']}: {name} is not declared in {ev['file']}")
                    proofs.append(f"`{name}`")
            elif kind == "test":
                for f in ev["files"]:
                    if not (root / f).exists():
                        bad.append(f"{r['id']}: missing test file {f}")
                    tests.append(f"`{pathlib.Path(f).name}`")
            elif kind == "ci":
                wf = root / ev["workflow"]
                text = wf.read_text() if wf.exists() else ""
                for s in ev["contains"]:
                    if s not in text:
                        bad.append(f"{r['id']}: {ev['workflow']} does not mention {s}")
                other.append(f"CI: `{pathlib.Path(ev['workflow']).name}`")
            elif kind == "inspection":
                other.append("inspection")
            else:
                bad.append(f"{r['id']}: unknown kind of evidence {kind}")
        print(f"| {r['id']} | {', '.join(proofs)} | {', '.join(tests)} | {', '.join(other)} |")
    if len({r["id"] for r in reqs}) != len(reqs):
        bad.append("duplicate requirement identifiers")
    for b in bad:
        print("PROBLEM:", b, file=sys.stderr)
    print(f"\n{len(reqs)} requirements, {len(bad)} problem(s)")
    return 1 if bad or not reqs else 0


if __name__ == "__main__":
    sys.exit(main())
