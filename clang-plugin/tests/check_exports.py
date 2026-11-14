#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Runs crosscheck-tool on the example programs with every export format and reads
the outputs back:

* FFX: parsed as XML with the rules of OTAWA's loader
  (src/prog/flowfact_FlowFactLoader.cpp): root `flowfacts`; a `loop` at top level
  needs `source` and `line` (a source location) and an integer `maxcount`; and every
  exported value must equal the loop bound of the JSON report.
* AIS / AIS2: every non-comment line has the documented form
  (`loop "R" + n loops max k;`, resp. `loop "R.Ln" { bound: 0 .. k; }`).
* SARIF: validated against the SARIF 2.1.0 JSON schema if its path is given with
  --sarif-schema (CI downloads it), otherwise checked structurally.

Usage: check_exports.py TOOL BENCHDIR INCLUDE [--sarif-schema FILE] [-- clang flags...]
"""
import argparse
import json
import pathlib
import re
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET

AIS = re.compile(r'^loop "[^"]+" \+ (\d+) loops max (\d+);$')
AIS2 = re.compile(r'^loop "[^"]+\.L(\d+)" \{ bound: 0 \.\. (\d+); \}$')


def run(tool, src, inc, flags, out, extra):
    cmd = [tool, "--all", f"--report={out}/r.json", *extra, str(src), "--", "-std=c++20", f"-I{inc}", *flags]
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode > 1:
        sys.exit(f"tool failed ({p.returncode}) on {src}:\n{p.stderr[-2000:]}")
    return json.loads((out / "r.json").read_text())


def main():
    argv = sys.argv[1:]
    flags = []
    if "--" in argv:
        i = argv.index("--")
        argv, flags = argv[:i], argv[i + 1:]
    ap = argparse.ArgumentParser()
    ap.add_argument("tool")
    ap.add_argument("bench")
    ap.add_argument("include")
    ap.add_argument("--sarif-schema")
    a = ap.parse_args(argv)
    facts = sarifs = 0
    with tempfile.TemporaryDirectory() as d:
        out = pathlib.Path(d)
        for src in sorted(pathlib.Path(a.bench).glob("*.cpp")):
            rep = run(a.tool, src, a.include, flags, out,
                      [f"--opt=flowfacts={out}/f.ffx", f"--opt=sarif={out}/r.sarif"])
            expected = {}
            for f in rep["functions"]:
                for l in f["loops"]:
                    if l["verified"]:
                        k = (l["file"], l["line"])
                        expected[k] = max(expected.get(k, 0), l["bound"])
            root = ET.parse(out / "f.ffx").getroot()
            assert root.tag == "flowfacts", src
            got = {}
            for loop in root:
                assert loop.tag == "loop", (src, loop.tag)
                assert loop.get("source") and loop.get("line"), (src, loop.attrib)
                assert loop.get("maxcount", "").isdigit(), (src, loop.attrib)
                got[(loop.get("source"), int(loop.get("line")))] = int(loop.get("maxcount"))
            assert got == expected, (src, got, expected)
            facts += len(got)
            for fmt, rx in (("ais", AIS), ("ais2", AIS2)):
                run(a.tool, src, a.include, flags, out,
                    [f"--opt=flowfacts={out}/f.{fmt}", f"--opt=flowfacts-format={fmt}"])
                lines = [l for l in (out / f"f.{fmt}").read_text().splitlines() if l and not l.startswith("#")]
                assert len(lines) == len(expected), (src, fmt, lines)
                for l in lines:
                    m = rx.match(l)
                    assert m and int(m.group(2)) in expected.values(), (src, fmt, l)
            log = json.loads((out / "r.sarif").read_text())
            assert log["version"] == "2.1.0" and len(log["runs"]) == 1, src
            rules = [r["id"] for r in log["runs"][0]["tool"]["driver"]["rules"]]
            for r in log["runs"][0]["results"]:
                assert rules[r["ruleIndex"]] == r["ruleId"], (src, r)
            errors = sum(1 for r in log["runs"][0]["results"] if r["level"] == "error")
            assert errors == sum(len(f["errors"]) for f in rep["functions"]), src
            if a.sarif_schema:
                import jsonschema
                schema = json.loads(pathlib.Path(a.sarif_schema).read_text())
                jsonschema.validators.validator_for(schema)(schema).validate(log)
            sarifs += 1
    print(f"exports OK: {facts} loop facts in FFX/AIS/AIS2, {sarifs} SARIF logs"
          + (" (schema-validated)" if a.sarif_schema else ""))


if __name__ == "__main__":
    main()
