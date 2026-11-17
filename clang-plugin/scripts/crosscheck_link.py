#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Check CrossCheck's time budgets after compilation, on the binary.

Time is a property of the machine code on a processor, not of the source: the plugin
records `CROSSCHECK_DEADLINE_CYCLES(n)` and `CROSSCHECK_DEADLINE_US(n)` in its report,
together with its loop bounds, and this script checks them on the compiled code:

    crosscheck_link.py --report REPORT.json --binary prog.o --source prog.c \\
        [--clock-mhz 48] [--context] [--json out.json]

For every function of the report with a time budget, the cycle bound of its code in the
binary is computed from the plugin's loop bounds (source loops matched with binary loops
through the debug line table) and the processor's timing table; microseconds are cycles
divided by the clock frequency in MHz. The script exits with status 1 if a budget is
exceeded or a function with a budget gets no cycle bound, 2 on a usage error.

Processor model: Cortex-M0 (ARMv6-M), the timing table and analysis of
`benchmarks/cycles/m0.py` and `wcet.py` (compile with `--target=thumbv6m-none-eabi
-mcpu=cortex-m0 -g`, as `run_cycles.py` does). Trusted, and printed with the results:
the timing table (zero-wait-state memory, no interrupt taken during the function), that
the compiler preserves the source loops' iteration counts, and the plugin's loop bounds
(for every call; with `--context`, those of the calling contexts of the analysed program).
Other processors and OTAWA as a back end are not supported yet.
"""
import argparse
import json
import pathlib
import shutil
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "benchmarks" / "cycles"))
import m0  # noqa: E402
import wcet  # noqa: E402

TRUSTED = ["the Cortex-M0 timing table of m0.py (zero-wait-state memory)",
           "no interrupt is taken while the function runs",
           "the compiler preserves the source loops' iteration counts",
           "the plugin's loop bounds (unverified analysis, or certificates if checked)"]


def default_objdump():
    found = shutil.which("llvm-objdump") or shutil.which("llvm-objdump-18")
    return found or str(pathlib.Path.home() / "miniforge3/envs/crosscheck/bin/llvm-objdump")


def loop_bounds(report, context):
    """source line -> bound of the loop there (None: no bound); the largest if several."""
    out = {}
    for f in report["functions"]:
        for lp in f.get("loops") or []:
            if context and lp.get("in_context") is not None:
                b = lp["in_context"]
            else:
                b = lp["bound"] if lp.get("verified") else None
            line = lp["line"]
            if line in out:
                b = None if out[line] is None or b is None else max(out[line], b)
            out[line] = b
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--report", required=True, help="the plugin's JSON report (--report=FILE)")
    ap.add_argument("--binary", required=True, help="the compiled code (object or ELF, with -g)")
    ap.add_argument("--source", required=True, help="the source file the report describes")
    ap.add_argument("--clock-mhz", type=float, help="clock frequency, for budgets in microseconds")
    ap.add_argument("--context", action="store_true",
                    help="use the loop bounds of the calling contexts (whole program)")
    ap.add_argument("--objdump", default=default_objdump())
    ap.add_argument("--json", help="write the results as JSON")
    a = ap.parse_args(argv)

    report = json.loads(pathlib.Path(a.report).read_text())
    img = m0.load(a.binary)
    lines = wcet.line_table(a.objdump, a.binary, pathlib.Path(a.source).name)
    an = wcet.Analysis(img, lines, loop_bounds(report, a.context))

    rows, failed = [], False
    for f in report["functions"]:
        dc, du = f.get("deadline_cycles"), f.get("deadline_us")
        if dc is None and du is None:
            continue
        sym = f.get("symbol") or f["name"]
        if sym not in img.funcs and f["name"] in img.funcs:
            sym = f["name"]
        row = dict(function=f["name"], deadline_cycles=dc, deadline_us=du, cycles=None, us=None)
        if du is not None and not a.clock_mhz:
            row["verdict"] = "error: a budget in microseconds needs --clock-mhz"
            failed = True
            rows.append(row)
            continue
        cyc = an.function(sym) if sym in img.funcs else None
        if cyc is None:
            why = an.why.get(sym, "not found in the binary" if sym not in img.funcs else "no bound")
            row["verdict"] = f"FAIL: no cycle bound ({why})"
            failed = True
        else:
            row["cycles"] = cyc
            if a.clock_mhz:
                row["us"] = round(cyc / a.clock_mhz, 3)
            over = (dc is not None and cyc > dc) or (du is not None and cyc > du * a.clock_mhz)
            row["verdict"] = "FAIL: budget exceeded" if over else "ok"
            failed = failed or over
        rows.append(row)

    for r in rows:
        budget = " ".join(x for x in (f"{r['deadline_cycles']} cycles" if r["deadline_cycles"] is not None else "",
                                      f"{r['deadline_us']} us" if r["deadline_us"] is not None else "") if x)
        bound = "-" if r["cycles"] is None else f"{r['cycles']} cycles" + (f" = {r['us']} us" if r["us"] is not None else "")
        print(f"{r['verdict'].split(':')[0]:5s} {r['function']}: bound {bound}, budget {budget}"
              + ("" if r["verdict"] == "ok" else f"  [{r['verdict']}]"))
    print("trusted: " + "; ".join(TRUSTED) + ("; loop bounds in context" if a.context else ""))
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(dict(processor="cortex-m0", clock_mhz=a.clock_mhz,
                                                        trusted=TRUSTED, functions=rows), indent=1) + "\n")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
