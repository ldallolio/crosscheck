#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Runs CrossCheck on a whole project described by a compilation database.

    crosscheck_project.py --tool TOOL -p BUILD_DIR --out OUT [--checker CHECKER]
        [--filter REGEX] [--jobs N] [--all] [--opt KEY=VALUE]... [--timeout SECONDS]
        [--baseline SNAPSHOT [--max-increase PCT]]

BUILD_DIR contains `compile_commands.json` (CMake: -DCMAKE_EXPORT_COMPILE_COMMANDS=ON;
Bear or `intercept-build` for other build systems). Every translation unit of the database
(or those whose path matches --filter) is analysed with its own compile command, in
parallel. OUT receives

    reports/<n>.json        the report of each translation unit (`--report`)
    certificates/<n>.json   its certificates (with --checker: also checked, and exported
                            as mini-C and validated)
    project.json            one record per function: file, bound, loops, certificate and
                            validation status, assumptions, errors
    index.html              the same as a page: totals, then one row per function
    snapshot.json           the input of `cost_diff.py` (baseline for the next run)

Without --all only the functions annotated CROSSCHECK_REALTIME are analysed; with --all
every function of the main file of each translation unit.

Exit status: 0; 1 if the tool crashed or timed out on a file, if the checker rejected a
certificate, or if --baseline is given and `cost_diff.py` reports a regression. A function
without a bound is not a failure of this script: it is a row of the report.
"""
import argparse
import concurrent.futures
import html
import json
import os
import pathlib
import re
import subprocess
import sys


def analyse(job):
    tool, build, src, n, out, opts, analyse_all, checker, timeout = job
    rep = out / "reports" / f"{n}.json"
    cert = out / "certificates" / f"{n}.json"
    cmd = [tool, "-p", build, f"--report={rep}", f"--opt=certificates={cert}"]
    if checker:
        cmd.append("--opt=minic")
    cmd += [f"--opt={o}" for o in opts]
    if analyse_all:
        cmd.append("--all")
    cmd.append(src)
    res = dict(file=src, status="ok", checker={})
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        res["status"] = "timeout"
        return res
    if r.returncode > 1 or not rep.exists():
        res["status"] = f"tool failed ({r.returncode})"
        res["stderr"] = r.stderr[-2000:]
        return res
    res["report"] = json.load(open(rep))
    if checker and cert.exists():
        c = subprocess.run([checker, str(cert)], capture_output=True, text=True)
        for line in c.stdout.splitlines():
            m = re.match(r"(ACCEPTED|REJECTED|VALIDATED|NOT VALIDATED|ASSUMED) +(.+?)(: bound|: the certificate| \(contract\))", line)
            if m:
                res["checker"].setdefault(m.group(2).strip(), []).append(m.group(1))
    return res


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tool", required=True)
    ap.add_argument("-p", "--build", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--checker")
    ap.add_argument("--filter")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--opt", action="append", default=[])
    ap.add_argument("--timeout", type=float, default=600)
    ap.add_argument("--baseline")
    ap.add_argument("--max-increase", type=float)
    a = ap.parse_args()

    db = json.load(open(pathlib.Path(a.build) / "compile_commands.json"))
    files = []
    for e in db:
        f = os.path.normpath(os.path.join(e.get("directory", "."), e["file"]))
        if f not in files and (not a.filter or re.search(a.filter, f)):
            files.append(f)
    out = pathlib.Path(a.out)
    (out / "reports").mkdir(parents=True, exist_ok=True)
    (out / "certificates").mkdir(exist_ok=True)
    jobs = [(a.tool, a.build, f, i, out, a.opt, a.all, a.checker, a.timeout) for i, f in enumerate(files)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, a.jobs)) as ex:
        results = list(ex.map(analyse, jobs))

    rows, failed = [], []
    for r in results:
        if r["status"] != "ok":
            failed.append(r)
            continue
        for fn in r["report"]["functions"]:
            # The checker prints qualified names (`ns::f`), the report the declared name.
            ck = [v for name, vs in r["checker"].items()
                  if name == fn["name"] or name.endswith("::" + fn["name"]) for v in vs]
            rows.append(dict(
                file=fn["file"], line=fn["line"], name=fn["name"], ok=fn["ok"], bound=fn["wcet"],
                in_context=fn.get("wcet_in_context"), deadline=fn.get("deadline"),
                loops=[dict(line=l["line"], bound=l["bound"] if l["verified"] else None,
                            potential=l.get("potential", "")) for l in fn.get("loops", [])],
                certificate=("rejected" if "REJECTED" in ck else "accepted" if "ACCEPTED" in ck
                             else fn.get("certificate", "")),
                validated="VALIDATED" in ck,
                summary=fn.get("certificate_summary", ""),
                assumptions=fn.get("assumptions", []), errors=fn.get("errors", [])))
    rows.sort(key=lambda x: (x["file"], x["line"]))
    totals = dict(
        files=len(files), files_failed=len(failed), functions=len(rows),
        bounded=sum(1 for x in rows if x["ok"]),
        certified=sum(1 for x in rows if x["certificate"] == "accepted"),
        validated=sum(1 for x in rows if x["validated"]),
        rejected_certificates=sum(1 for x in rows if x["certificate"] == "rejected"),
        loops=sum(len(x["loops"]) for x in rows),
        loops_bounded=sum(1 for x in rows for l in x["loops"] if l["bound"] is not None))
    json.dump(dict(totals=totals, functions=rows,
                   failed=[dict(file=f["file"], status=f["status"]) for f in failed]),
              open(out / "project.json", "w"), indent=1)

    here = pathlib.Path(__file__).resolve().parent
    subprocess.run([sys.executable, str(here / "cost_diff.py"), str(out / "reports"), "--snapshot",
                    str(out / "snapshot.json")], check=False)

    def td(x, cls=""):
        return f'<td class="{cls}">{html.escape(str(x))}</td>'
    lines = ["<!doctype html><html><head><meta charset='utf-8'><title>CrossCheck project report</title>",
             "<style>body{font-family:sans-serif;margin:16px}table{border-collapse:collapse;font-size:14px}"
             "td,th{border:1px solid #bbb;padding:3px 8px;vertical-align:top;text-align:left}"
             ".no{background:#fde0e0}.yes{background:#e3f4e3}.num{text-align:right}"
             "details{max-width:60em}</style></head><body>",
             "<h1>CrossCheck project report</h1>",
             "<p>Bounds are in the abstract units of the cost model, not in time. A bound holds under "
             "the assumptions listed for its function. Certificates are checked by the Lean checker; "
             "a validated certificate was also compared with the mini-C export of its function.</p>",
             "<table><tr>" + "".join(f"<th>{k.replace('_', ' ')}</th>" for k in totals) + "</tr><tr>" +
             "".join(td(v, "num") for v in totals.values()) + "</tr></table>"]
    if failed:
        lines.append("<h2>Files not analysed</h2><ul>" +
                     "".join(f"<li>{html.escape(f['file'])}: {html.escape(f['status'])}</li>" for f in failed) + "</ul>")
    lines.append("<h2>Functions</h2><table><tr><th>File</th><th>Function</th><th>Bound</th><th>Loops "
                 "(line: bound)</th><th>Certificate</th><th>Assumptions and errors</th></tr>")
    for x in rows:
        loops = ", ".join(f"{l['line']}: {l['bound'] if l['bound'] is not None else 'none'}" for l in x["loops"])
        cert = x["certificate"] + (" + validated" if x["validated"] else "")
        notes = "".join(f"<div>error: {html.escape(e)}</div>" for e in x["errors"])
        if x["assumptions"]:
            notes += f"<details><summary>{len(x['assumptions'])} assumption(s)</summary>" + \
                     "".join(f"<div>{html.escape(s)}</div>" for s in x["assumptions"]) + "</details>"
        lines.append("<tr>" + td(f"{os.path.basename(x['file'])}:{x['line']}") + td(x["name"]) +
                     td(x["bound"] if x["ok"] else "none", "num " + ("yes" if x["ok"] else "no")) +
                     td(loops) + td(cert, "yes" if x["certificate"] == "accepted" else "") +
                     f"<td>{notes}</td></tr>")
    lines.append("</table></body></html>")
    (out / "index.html").write_text("\n".join(lines))

    print(json.dumps(totals))
    status = 0
    if failed or totals["rejected_certificates"]:
        for f in failed:
            print(f"not analysed: {f['file']}: {f['status']}", file=sys.stderr)
        status = 1
    if a.baseline:
        cmd = [sys.executable, str(here / "cost_diff.py"), a.baseline, str(out / "snapshot.json")]
        if a.max_increase is not None:
            cmd += ["--max-increase", str(a.max_increase)]
        if subprocess.run(cmd).returncode != 0:
            status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
