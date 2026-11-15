#!/usr/bin/env python3
"""Mini-C validation: check_minic.py TOOL CHECKER FILE.c INCLUDE [clang flags...]

Runs the tool with certificates and mini-C sources on FILE.c, then the Lean checker.
Every function named ok_* must be VALIDATED; no function named no_* may be VALIDATED;
no certificate may be rejected."""
import json, re, subprocess, sys, tempfile, pathlib

tool, checker, src, inc, *flags = sys.argv[1:]
with tempfile.TemporaryDirectory() as d:
    cert = pathlib.Path(d) / "minic.json"
    p = subprocess.run([tool, "--all", "--opt=minic", f"--opt=certificates={cert}", src, "--",
                        "-x", "c", f"-I{inc}", *flags], capture_output=True, text=True)
    if p.returncode > 1 or not cert.exists():
        sys.exit(f"the tool failed ({p.returncode})\n{p.stderr[-3000:]}")
    out = subprocess.run([checker, "--print", str(cert)], capture_output=True, text=True).stdout
    print(out)
    funs = {f["name"]: f for prog in json.loads(cert.read_text())["programs"] for f in prog["functions"]}
validated = set(re.findall(r"^VALIDATED (\w+):", out, re.M))
bad = []
if re.search(r"^REJECTED|^PROGRAM.*REJECTED", out, re.M):
    bad.append("a certificate was rejected")
for name in re.findall(r"^\w[\w ]*\b(ok_\w+|no_\w+)\s*\(", pathlib.Path(src).read_text(), re.M):
    if name.startswith("ok_") and name not in validated:
        bad.append(f"{name}: not validated ({funs.get(name, {}).get('source_refused', 'no certificate' if name not in funs else 'mismatch')})")
    if name.startswith("no_") and name in validated:
        bad.append(f"{name}: validated, but an exact translation would be wrong")
for name in sorted(funs):
    if name.startswith("no_"):
        print(f"{name}: {funs[name].get('source_refused') or 'exported, not validated'}")
if bad:
    sys.exit("\n".join(bad))
print(f"{len(validated)} validated")
