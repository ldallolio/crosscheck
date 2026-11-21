#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Mini-C validation: check_minic.py TOOL CHECKER FILE.c INCLUDE [clang flags...]

Runs the tool with certificates and mini-C sources on FILE.c, then the Lean checker.
Every function named ok_* must be VALIDATED; no function named no_* may be VALIDATED;
no certificate may be rejected.

Then, for every validated function whose source has ghost variables (the flags of its
jumps, `fb`/`fc`, or the variable of a `switch`, `sc`): the same file with one ghost
index replaced by a variable of the function's source must not validate that function
(`MiniC.tr` refuses a source that names a ghost variable)."""
import copy, json, re, subprocess, sys, tempfile, pathlib

tool, checker, src, inc, *flags = sys.argv[1:]


def ghosts(j, out):
    if isinstance(j, dict):
        for key in ("fb", "fc", "sc"):
            if key in j:
                out.append((j, key))
        for v in j.values():
            ghosts(v, out)
    elif isinstance(j, list):
        for v in j:
            ghosts(v, out)


bad = []
with tempfile.TemporaryDirectory() as d:
    cert = pathlib.Path(d) / "minic.json"
    p = subprocess.run([tool, "--all", "--opt=minic", f"--opt=certificates={cert}", src, "--",
                        "-x", "c", f"-I{inc}", *flags], capture_output=True, text=True)
    if p.returncode > 1 or not cert.exists():
        sys.exit(f"the tool failed ({p.returncode})\n{p.stderr[-3000:]}")
    out = subprocess.run([checker, "--print", str(cert)], capture_output=True, text=True).stdout
    print(out)
    doc = json.loads(cert.read_text())
    funs = {f["name"]: f for prog in doc["programs"] for f in prog["functions"]}
    validated = set(re.findall(r"^VALIDATED (\w+):", out, re.M))
    mutated = 0
    for pi, prog in enumerate(doc["programs"]):
        for fi, fn in enumerate(prog["functions"]):
            if fn["name"] not in validated or "jsource" not in fn:
                continue
            spots = []
            ghosts(fn["jsource"]["body"], spots)
            own = [i for i, v in enumerate(prog["variables"])
                   if v.startswith(fn["name"] + "::") and "?" not in v
                   and f'"x": {i}' in json.dumps(fn["jsource"])]
            if not spots or not own:
                continue
            for si in range(len(spots)):
                doc2 = copy.deepcopy(doc)
                fn2 = doc2["programs"][pi]["functions"][fi]
                spots2 = []
                ghosts(fn2["jsource"]["body"], spots2)
                node, key = spots2[si]
                node[key] = own[0]
                f2 = pathlib.Path(d) / "mutated.json"
                f2.write_text(json.dumps(doc2))
                out2 = subprocess.run([checker, str(f2)], capture_output=True, text=True).stdout
                mutated += 1
                if re.search(rf"^VALIDATED {re.escape(fn['name'])}:", out2, re.M):
                    bad.append(f"{fn['name']}: validated with the ghost variable '{key}' replaced by a variable of its source")
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
if mutated == 0:
    bad.append("no source with ghost variables to mutate")
if bad:
    sys.exit("\n".join(bad))
print(f"{len(validated)} validated; {mutated} sources with a ghost variable named by the source, none validated")
