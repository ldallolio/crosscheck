#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""TACLeBench kernels with minimal annotations: how many trusted loop bounds does each
entry function need?

    run_annotated.py [--tool T] [--cache DIR] [--extra-arg A]... [--only K]... [--json OUT]

For each kernel, starting from the unannotated program (as in run_tacle.py, entry point
`main`):

1. run the tool; among the functions reached from `main` (`contexts` > 0), take the loops
   that the analyser reports as unbounded ("cannot derive an iteration bound");
2. give each of them `CROSSCHECK_LOOP_BOUND(n)` as the first statement of its body, with
   `n` the maximum of the benchmark's `loopbound` pragma for that loop (what an engineer
   would state from knowledge of the program; here taken from the benchmark);
3. repeat until `main` is bounded or no annotated loop is left to add.

The annotation is trusted: it is listed in the report's assumptions, and a function whose
bound rests on it gets no certificate. Only loops are annotated: a function that stays
unbounded for another reason (recursion, a call through a pointer, a call of a function
without code) is reported with that reason. The annotation is inserted on the loop's own
line, so the line numbers of the program do not change; a loop whose body is not a block
is given braces; one whose body cannot be delimited is not annotated (reported).

Every annotated value is then compared with the loop counts observed on the kernel's
built-in input (measure_loops.py): a value below an observed count is a wrong assumption,
and it is reported (`--check` fails). The flow facts of two `while (1)` loops left by
`break` are one below the observed count (run_tacle.py's README): they are expected here.
"""
import argparse
import json
import pathlib
import re
import shutil
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import measure_loops  # noqa: E402
import run_tacle  # noqa: E402

UNBOUNDED_RE = re.compile(r"^line (\d+): cannot derive an iteration bound for this loop")


def run(tool, unit, kdir, report, extra):
    report.unlink(missing_ok=True)
    cmd = [str(tool), "--all", "--opt=entry=main", f"--report={report}", str(unit), "--",
           "-x", "c", "-std=gnu99", f"-I{kdir}", f"-I{ROOT / 'clang-plugin/include'}",
           "-include", "crosscheck/attributes.hpp", "-w", "-ferror-limit=0",
           "-Wno-error=implicit-function-declaration", *extra]
    subprocess.run(cmd, capture_output=True, text=True, timeout=3600)
    if not report.exists():
        return None
    return json.loads(report.read_text())


def _skip_ws(text, pos):
    while pos < len(text):
        if text[pos].isspace():
            pos += 1
        elif text.startswith("/*", pos):
            pos = text.index("*/", pos) + 2
        elif text.startswith("//", pos):
            pos = text.index("\n", pos)
        else:
            break
    return pos


def _parens(text, pos):
    """The position after the parenthesised group that starts at or after `pos`."""
    while text[pos] != "(":
        pos += 1
    depth = 0
    while True:
        depth += {"(": 1, ")": -1}.get(text[pos], 0)
        pos += 1
        if depth == 0:
            return pos


def _stmt_end(text, pos):
    """The position after the C statement that starts at `pos` (blocks, loops, `if`/`else`,
    `do`/`while`, or a simple statement ending with `;`). Strings and character constants
    containing braces or semicolons are not handled: such a statement is not annotated."""
    pos = _skip_ws(text, pos)
    kw = re.compile(r"(for|while|if|do|else|switch)\b").match(text, pos)
    if text[pos] == "{":
        depth = 0
        while True:
            depth += {"{": 1, "}": -1}.get(text[pos], 0)
            pos += 1
            if depth == 0:
                return pos
    if kw and kw.group(1) in ("for", "while", "switch"):
        return _stmt_end(text, _parens(text, kw.end()))
    if kw and kw.group(1) == "if":
        end = _stmt_end(text, _parens(text, kw.end()))
        q = _skip_ws(text, end)
        if re.compile(r"else\b").match(text, q):
            return _stmt_end(text, q + 4)
        return end
    if kw and kw.group(1) == "do":
        end = _stmt_end(text, kw.end())
        return text.index(";", _parens(text, end)) + 1
    depth = 0
    while True:
        c = text[pos]
        if c in "\"'":
            raise ValueError("string in a statement")
        depth += {"(": 1, ")": -1, "{": 1, "}": -1}.get(c, 0)
        pos += 1
        if c == ";" and depth == 0:
            return pos


def annotate(lines, line, n):
    """Insert `CROSSCHECK_LOOP_BOUND(n);` as the first statement of the body of the loop
    that starts on `line` (1-based), without adding a line: after the `{` of a block, or
    with braces around a body that is a single statement. None if the loop is not found
    or its body cannot be delimited."""
    text = "\n".join(lines)
    start = sum(len(l) + 1 for l in lines[:line - 1])
    m = re.compile(r"\s*(for|while|do)\b").match(text, start)
    if not m:
        return None
    try:
        pos = m.end() if m.group(1) == "do" else _parens(text, m.end())
        pos = _skip_ws(text, pos)
        ann = f" CROSSCHECK_LOOP_BOUND({n});"
        if text[pos] == "{":
            new = text[:pos + 1] + ann + text[pos + 1:]
        else:
            end = _stmt_end(text, pos)
            new = text[:pos] + "{" + ann + " " + text[pos:end] + " }" + text[end:]
    except (ValueError, IndexError):
        return None
    return new.split("\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tool", default=str(ROOT / "clang-plugin/build/crosscheck-tool"))
    ap.add_argument("--cache", default=str(HERE / ".cache"))
    ap.add_argument("--extra-arg", action="append", default=[])
    ap.add_argument("--only", action="append")
    ap.add_argument("--clang", default=shutil.which("clang") or "/usr/lib/llvm-18/bin/clang")
    ap.add_argument("--opt", default=shutil.which("opt") or "/usr/lib/llvm-18/bin/opt")
    ap.add_argument("--cc", default="cc")
    ap.add_argument("--json")
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    src = run_tacle.fetch(pathlib.Path(a.cache), run_tacle.REV)
    work = pathlib.Path(a.cache) / "annotated"
    work.mkdir(parents=True, exist_ok=True)
    rows = []
    for kdir in sorted(p for p in (src / "bench/kernel").iterdir() if p.is_dir()):
        k = kdir.name
        if a.only and k not in a.only:
            continue
        orig = "".join(f.read_text(errors="replace") for f in sorted(kdir.glob("*.c")))
        lines = orig.split("\n")
        prag = run_tacle.pragmas(lines)
        unit, report = work / f"{k}.c", work / f"{k}.json"
        annotated, missing, unbraced = {}, set(), set()
        row = dict(kernel=k)
        before = None
        while True:
            unit.write_text("\n".join(lines))
            rep = run(a.tool, unit, kdir, report, a.extra_arg)
            if rep is None:
                row["status"] = "no report"
                break
            fns = {f["name"]: f for f in rep["functions"]}
            if before is None:
                before = fns.get("main", {}).get("ok", False)
                row["main_bounded_before"] = before
            if fns.get("main", {}).get("ok"):
                break
            todo = set()
            for f in rep["functions"]:
                if not f.get("contexts"):
                    continue
                for e in f.get("errors") or []:
                    m = UNBOUNDED_RE.match(e)
                    if m:
                        todo.add(int(m.group(1)))
            todo -= set(annotated) | missing | unbraced
            if not todo:
                break
            for ln in sorted(todo, reverse=True):
                if ln not in prag:
                    missing.add(ln)
                    continue
                new = annotate(lines, ln, prag[ln])
                if new is None:
                    unbraced.add(ln)
                    continue
                lines = new
                annotated[ln] = prag[ln]
        main = fns.get("main", {}) if rep else {}
        row.update(main_bounded=bool(main.get("ok")), main_bound=main.get("wcet") if main.get("ok") else None,
                   annotations=len(annotated), annotated=annotated,
                   without_flow_fact=sorted(missing), not_a_block=sorted(unbraced),
                   assumptions=sum(len(f.get("assumptions") or []) for f in rep["functions"]) if rep else None,
                   blockers=[] if main.get("ok") else (main.get("errors") or [])[:3])
        if annotated:
            try:
                obs, _, _ = measure_loops.observed_counts(work / f"{k}.c", kdir, a.clang, a.opt,
                                                         [f"-I{ROOT / 'clang-plugin/include'}", "-include",
                                                          "crosscheck/attributes.hpp", *a.extra_arg],
                                                         work, a.cc)
            except Exception as ex:  # noqa: BLE001
                obs = None
                row["observed"] = f"not measured: {type(ex).__name__}"
            if obs is not None:
                row["below_observed"] = {ln: (n, obs[ln]) for ln, n in annotated.items() if ln in obs and n < obs[ln]}
                row["annotated_reached"] = sum(ln in obs for ln in annotated)
        rows.append(row)
        print(f"{k:16s} before={'yes' if row.get('main_bounded_before') else 'no ':3s} after="
              f"{'yes' if row['main_bounded'] else 'no ':3s} annotations={row['annotations']}"
              f" below_observed={len(row.get('below_observed', {}))}"
              + (f" missing={row['without_flow_fact']}" if row["without_flow_fact"] else "")
              + (f" not_a_block={row['not_a_block']}" if row["not_a_block"] else ""), file=sys.stderr)
        for b in row["blockers"]:
            print(f"   {b[:200]}", file=sys.stderr)
    tot = dict(kernels=len(rows), main_before=sum(bool(r.get("main_bounded_before")) for r in rows),
               main_after=sum(r["main_bounded"] for r in rows),
               annotations=sum(r["annotations"] for r in rows),
               kernels_annotated=sum(r["annotations"] > 0 for r in rows),
               below_observed=sum(len(r.get("below_observed", {})) for r in rows))
    print(json.dumps(tot))
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(dict(total=tot, kernels=rows), indent=1) + "\n")
    if a.check and tot["below_observed"]:
        sys.exit(1)


if __name__ == "__main__":
    main()
