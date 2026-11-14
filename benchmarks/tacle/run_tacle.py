#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. MIT licence (see the repository's LICENSE).
"""Run crosscheck-tool on the kernel programs of TACLeBench and compare the loop
bounds it derives with the `#pragma loopbound min X max Y` flow facts that ship
with the benchmarks.

TACLeBench (Falk et al., WCET 2016) is not copied into this repository (its files
carry various licences); a pinned revision is fetched into a cache directory.

Usage (from the repository root, after building the plugin):

    python3 benchmarks/tacle/run_tacle.py [--extra-arg=--gcc-install-dir=...]
        [--markdown=out.md] [--latex=out.tex] [--json=out.json]

No annotation is added to the benchmark sources: every function is analysed
(`--all`) as written. For each kernel, its .c files are concatenated into one
translation unit so that helper functions in other files have a definition.

What is compared: for every loop that carries a loopbound pragma, the bound the
tool proves (if any) against the pragma's maximum. TACLeBench's flow facts
describe each program on its fixed built-in input; they are a reference, not an
independent proof of the worst case, and some are not tight.
"""

import argparse
import json
import pathlib
import re
import subprocess
import sys
import time

REPO = "https://github.com/RTSYork/tacle-bench"
REV = "4e4fbf7710e5d6a089f0bba86c8f425b9c71bf7e"  # master, 2020-10-15

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LOOP_RE = re.compile(r"\s*(for|while|do)\b")
PRAGMA_RE = re.compile(r"loopbound\s+min\s+(\d+)\s+max\s+(\d+)")
DIAG_RE = re.compile(r":(\d+):\d+: error: crosscheck: (.*)$")


def fetch(cache: pathlib.Path, rev: str) -> pathlib.Path:
    src = cache / "tacle-bench"
    if not (src / ".git").exists():
        src.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "init", "-q"], cwd=src, check=True)
        subprocess.run(["git", "remote", "add", "origin", REPO], cwd=src, check=True)
    head = subprocess.run(["git", "rev-parse", "-q", "--verify", "HEAD"], cwd=src,
                          capture_output=True, text=True).stdout.strip()
    if head != rev:
        subprocess.run(["git", "fetch", "-q", "--depth", "1", "origin", rev], cwd=src, check=True)
        subprocess.run(["git", "checkout", "-q", "--detach", rev], cwd=src, check=True)
    return src


def pragmas(lines):
    """Map the line of each loop to the max of the loopbound pragma above it."""
    out = {}
    for i, text in enumerate(lines, 1):
        m = PRAGMA_RE.search(text)
        if not m:
            continue
        j = i + 1
        while j <= len(lines) and not LOOP_RE.match(lines[j - 1]):
            j += 1
        out[j] = int(m.group(2))
    return out


def run_kernel(tool, kdir: pathlib.Path, work: pathlib.Path, extra, certdir=None):
    name = kdir.name
    unit = work / f"{name}.c"
    unit.write_text("".join(f.read_text(errors="replace") for f in sorted(kdir.glob("*.c"))))
    report = work / f"{name}.json"
    report.unlink(missing_ok=True)
    certs = [f"--opt=certificates={certdir / (name + '.json')}"] if certdir else []
    cmd = [str(tool), "--all", "--opt=entry=main", *certs, f"--report={report}", str(unit), "--",
           "-x", "c", "-std=gnu99", f"-I{kdir}", "-w", "-ferror-limit=0", *extra]
    t0 = time.monotonic()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
    seconds = time.monotonic() - t0
    if not report.exists():
        sys.exit(f"{name}: no report written\n{proc.stderr[-2000:]}")
    rep = json.loads(report.read_text())

    error_lines = {int(m.group(1)) for m in map(DIAG_RE.search, proc.stderr.splitlines()) if m}
    derived, in_ctx, main, program = {}, {}, None, None
    assumptions = 0
    bounded_fns = certified = cert_equal = 0
    for f in rep["functions"]:
        if f.get("ok"):
            bounded_fns += 1
            if f.get("certificate") == "emitted":
                certified += 1
                cert_equal += f.get("certificate_bound") == f.get("wcet")
        assumptions += len(f.get("assumptions") or [])
        if f["name"] == f"{name}_main":
            main = f
        if f["name"] == "main":
            program = f
        for lp in f.get("loops") or []:
            if lp.get("verified") and lp.get("bound") is not None:
                derived[lp["line"]] = min(derived.get(lp["line"], lp["bound"]), lp["bound"])
            # In the calling contexts reached from the C `main` (see README.md).
            if lp.get("in_context") is not None:
                in_ctx[lp["line"]] = max(in_ctx.get(lp["line"], 0), lp["in_context"])

    row = dict(kernel=name, loops=0, derived=0, equal=0, looser=0, tighter=0,
               no_bound=0, not_reached=0, main_ok=bool(main and main["ok"]),
               main_bound=main["wcet"] if main and main["ok"] else None,
               ctx_derived=0, ctx_equal=0, ctx_looser=0, ctx_tighter=0,
               program_ok=bool(program and program["ok"]),
               bounded_functions=bounded_fns, certified=certified, certified_equal=cert_equal,
               main_certified=bool(main and main.get("certificate") == "emitted"),
               assumptions=assumptions, seconds=round(seconds, 1), details=[], ctx_details=[])
    for line, mx in sorted(pragmas(unit.read_text(errors="replace").splitlines()).items()):
        row["loops"] += 1
        c = in_ctx.get(line)
        if c is not None:
            row["ctx_derived"] += 1
            key = "ctx_equal" if c == mx else "ctx_looser" if c > mx else "ctx_tighter"
            row[key] += 1
            if key != "ctx_equal":
                row["ctx_details"].append(dict(line=line, bound=c, pragma_max=mx))
        b = derived.get(line)
        if b is None:
            row["no_bound" if line in error_lines else "not_reached"] += 1
            continue
        row["derived"] += 1
        key = "equal" if b == mx else "looser" if b > mx else "tighter"
        row[key] += 1
        if key != "equal":
            row["details"].append(dict(line=line, bound=b, pragma_max=mx))
    return row


COLS = ["loops", "derived", "equal", "looser", "tighter", "no_bound", "not_reached"]
CTX = ["ctx_derived", "ctx_equal", "ctx_looser", "ctx_tighter"]


def markdown(rows, total):
    head = ("| Kernel | Loops | Derived | = max | > max | < max | No bound | Not reached | `_main` bound "
            "| In context: derived | = max | > max | < max |")
    out = [head, "|" + "---|" * 13]
    for r in rows + [total]:
        mb = f"{r['main_bound']:,}".replace(",", " ") if r.get("main_bound") is not None else (
            f"{r['main_ok']} kernels" if r is total else "—")
        out.append(f"| {r['kernel']} | " + " | ".join(str(r[c]) for c in COLS) + f" | {mb} | "
                   + " | ".join(str(r[c]) for c in CTX) + " |")
    return "\n".join(out) + "\n"


def latex(rows, total):
    out = []
    for r in rows + [total]:
        k = r["kernel"].replace("_", r"\_")
        if r is total:
            out.append(r"\midrule")
            mb = f"{r['main_ok']} of {len(rows)}"
        else:
            mb = "--" if r["main_bound"] is None else f"{r['main_bound']:,}".replace(",", r"\,")
        cols = [c for c in COLS if c != "not_reached"]  # always 0 so far; kept in JSON/Markdown
        out.append(f"{k} & " + " & ".join(str(r[c]) for c in cols) + f" & {mb} & "
                   + " & ".join(str(r[c]) for c in CTX[:2]) + " \\\\")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tool", default=str(ROOT / "clang-plugin/build/crosscheck-tool"))
    ap.add_argument("--cache", default=str(HERE / ".cache"))
    ap.add_argument("--rev", default=REV)
    ap.add_argument("--extra-arg", action="append", default=[],
                    help="extra Clang flag, e.g. --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13")
    ap.add_argument("--only", action="append", help="run only these kernels")
    ap.add_argument("--markdown"); ap.add_argument("--latex"); ap.add_argument("--json")
    ap.add_argument("--certificates", help="emit cost certificates into this directory")
    ap.add_argument("--checker", help="crosscheck-check executable: check the certificates (needs --certificates)")
    a = ap.parse_args()

    cache = pathlib.Path(a.cache)
    src = fetch(cache, a.rev)
    work = cache / "work"
    work.mkdir(parents=True, exist_ok=True)
    kernels = sorted(p for p in (src / "bench/kernel").iterdir() if p.is_dir())
    if a.only:
        kernels = [k for k in kernels if k.name in a.only]

    certdir = pathlib.Path(a.certificates) if a.certificates else None
    if certdir:
        certdir.mkdir(parents=True, exist_ok=True)
    rows = []
    for k in kernels:
        r = run_kernel(a.tool, k, work, a.extra_arg, certdir)
        rows.append(r)
        print(f"{r['kernel']:16s} " + " ".join(f"{c}={r[c]}" for c in COLS)
              + f" main={'ok' if r['main_ok'] else 'no'} {r['seconds']}s", file=sys.stderr)
    total = {c: sum(r[c] for r in rows) for c in COLS + CTX}
    for c in ("bounded_functions", "certified", "certified_equal", "main_certified"):
        total[c] = sum(r.get(c, 0) for r in rows)
    if certdir:
        print(f"certificates: {total['certified']} of {total['bounded_functions']} bounded functions "
              f"({total['certified_equal']} with the same bound), {total['main_certified']} entry functions",
              file=sys.stderr)
    if certdir and a.checker:
        files = sorted(str(p) for p in certdir.glob("*.json"))
        proc = subprocess.run([a.checker, *files], capture_output=True, text=True)
        acc = proc.stdout.count("ACCEPTED")
        rej = proc.stdout.count("REJECTED")
        total["checker_accepted"], total["checker_rejected"] = acc, rej
        print(f"checker: {acc} accepted, {rej} rejected (exit {proc.returncode})", file=sys.stderr)
        if proc.returncode != 0:
            sys.stderr.write(proc.stdout + proc.stderr)
            sys.exit("a certificate was rejected by the checker")
    total.update(kernel="Total", main_ok=sum(r["main_ok"] for r in rows), main_bound=None,
                 program_ok=sum(r["program_ok"] for r in rows),
                 assumptions=sum(r["assumptions"] for r in rows),
                 seconds=round(sum(r["seconds"] for r in rows), 1))

    md = markdown(rows, total)
    sys.stdout.write(md)
    if a.markdown:
        pathlib.Path(a.markdown).write_text(md)
    if a.latex:
        pathlib.Path(a.latex).write_text(latex(rows, total))
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(dict(revision=a.rev, kernels=rows, total=total), indent=2) + "\n")


if __name__ == "__main__":
    main()
