#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Check CrossCheck's time budgets after compilation, on the binary.

Time is a property of the machine code on a processor, not of the source: the plugin
records `CROSSCHECK_DEADLINE_CYCLES(n)` and `CROSSCHECK_DEADLINE_US(n)` in its report,
together with its loop bounds, and this script checks them on the compiled code:

    crosscheck_link.py --report a.json --source a.c [--report b.json --source b.c ...]
        --binary prog.elf [--processor cortex-m0|stm32f4|stm32h7] [--clock-mhz 48]
        [--context] [--certify [--checker crosscheck-check] [--cycle-certificate F]]
        [--json out.json]

`--report` and `--source` are given in pairs, one per translation unit (the report of the
plugin run on that source file); the binary is an object file or a linked executable
compiled with `-g`, and may contain the code of several of them (a whole program). For
every function of the reports with a time budget, the cycle bound of its code in the
binary is computed from the plugin's loop bounds (binary loops matched with source loops
through the debug line table) and a timing model of the processor; microseconds are cycles
divided by the clock frequency in MHz. The script exits with status 1 if a budget is
exceeded or a function with a budget gets no cycle bound, 2 on a usage error.

Processors (`--processor`):
- `cortex-m0` (default): ARMv6-M, the timing table and analysis of `benchmarks/cycles/m0.py`
  and `wcet.py` (compile with `--target=thumbv6m-none-eabi -mcpu=cortex-m0 -g`, as
  `run_cycles.py` does); an object file, or an executable whose code is below 0x20000000;
  the reports must come from an analysis for the binary's target too (the same `--target`
  and `-mcpu` after `--`): loop bounds that depend on `sizeof(long)` or on the size of
  pointers differ between a 64-bit host and a 32-bit processor;
- `stm32f4` (Cortex-M4) and `stm32h7` (Cortex-M7): OTAWA's `stm32` script, run in the
  Docker image `--otawa-image` without network (`benchmarks/cycles/otawa_flow.py`; the
  image is built by the user, see `run_otawa.py`); the binary must be an executable
  linked at the board's addresses (code in flash from 0x08000000, data from
  0x20000000), otherwise OTAWA assumes its worst memory latency for every access.

With `--certify` (Cortex-M0), the bounds are those of the implicit path enumeration
technique with a certificate on the machine code (`benchmarks/cycles/ipet.py`) that the
verified checker `crosscheck-check` must accept: it decodes the code and builds the
control-flow graphs itself (Lean theorem `Thumb.binary_sound`); the analysis, the graph
construction and the bound computation are then outside the trusted base, the Lean
specification of the processor (decoder, timing table) and the loop bounds are not.

Trusted, and printed with the results: the timing model (zero-wait-state memory and no
interrupt for the Cortex-M0; OTAWA and its processor model for the others), that the
compiler preserves the source loops' iteration counts, and the plugin's loop bounds (for
every call; with `--context`, those of the calling contexts of the analysed program).
"""
import argparse
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "benchmarks" / "cycles"))
import ipet  # noqa: E402
import m0  # noqa: E402
import otawa_flow  # noqa: E402
import wcet  # noqa: E402

TRUSTED_COMMON = ["no interrupt is taken while the function runs",
                  "the compiler preserves the source loops' iteration counts",
                  "the plugin's loop bounds (unverified analysis, or certificates if checked)"]
TRUSTED_M0 = ["the Cortex-M0 timing table of m0.py (zero-wait-state memory)"] + TRUSTED_COMMON
TRUSTED_CERTIFIED = ["the Lean specification of the Cortex-M0 (Thumb.decode: instruction decoding and cycles, "
                     "zero-wait-state memory)",
                     "that the binary is loaded as the checker reads it (its code and function entries are "
                     "checked against the certificate by crosscheck-check --elf; an object is placed by the checker)",
                     "the Lean checker (theorem Thumb.binary_sound)"] + TRUSTED_COMMON


def trusted(processor, certify=False):
    if processor == "cortex-m0":
        return TRUSTED_CERTIFIED if certify else TRUSTED_M0
    return [f"OTAWA and its model of the {otawa_flow.PROCESSORS[processor][1]}"] + TRUSTED_COMMON


def default_objdump():
    found = shutil.which("llvm-objdump") or shutil.which("llvm-objdump-18")
    return found or str(pathlib.Path.home() / "miniforge3/envs/crosscheck/bin/llvm-objdump")


LOOP_ENDS = {}   # (source name, line) -> last line of the loop (`end_line`), for wcet.Analysis


def loop_bounds(reports, context):
    """(source name, line) -> bound of the loop there (None: no bound); the largest if several.
    Also records the loops' last lines in LOOP_ENDS."""
    out = {}
    for name, report in reports:
        for f in report["functions"]:
            for lp in f.get("loops") or []:
                if context and lp.get("in_context") is not None:
                    b = lp["in_context"]
                else:
                    b = lp["bound"] if lp.get("verified") else None
                key = (name, lp["line"])
                LOOP_ENDS[key] = max(LOOP_ENDS.get(key, 0), lp.get("end_line") or lp["line"])
                if key in out:
                    b = None if out[key] is None or b is None else max(out[key], b)
                out[key] = b
    return out


def m0_bounds(a, names, bounds, roots):
    """{symbol: (cycles or None, reason)} with the timing schema of wcet.py, or with
    `--certify` the IPET bounds of ipet.py accepted by the verified checker."""
    img = m0.load(a.binary)
    lines = wcet.line_table(a.objdump, a.binary, names, base=img.base)
    an = wcet.Analysis(img, lines, bounds, LOOP_ENDS)
    res = {}
    if a.certify:
        known = [r for r in roots if r in img.funcs]
        doc, ib, why = ipet.certify(an, known)
        with tempfile.TemporaryDirectory() as d:
            path = pathlib.Path(a.cycle_certificate or pathlib.Path(d) / "cycles.json")
            path.write_text(json.dumps(doc, indent=1) + "\n")
            # the code of the certificate checked against the binary (`--elf`)
            out = subprocess.run([a.checker, "--elf", a.binary, str(path)], capture_output=True,
                                 text=True) if doc["programs"] else None
        ok = out is not None and out.returncode == 0 and "PROGRAM  program: ACCEPTED" in out.stdout
        for sym in roots:
            if sym not in img.funcs:
                res[sym] = (None, "not found in the binary")
            elif sym not in ib:
                res[sym] = (None, "no cycle certificate: " + why.get(sym, "?"))
            elif not ok:
                res[sym] = (None, "the checker rejected the cycle certificate")
            else:
                res[sym] = (ib[sym], None)
        return res
    for sym in roots:
        if sym not in img.funcs:
            res[sym] = (None, "not found in the binary")
            continue
        c = an.function(sym)
        res[sym] = (c, None if c is not None else an.why.get(sym, "no bound"))
    return res


def otawa_bounds(a, names, bounds, roots):
    """{symbol: (cycles or None, reason)} by OTAWA with flow facts from the source bounds."""
    nm = pathlib.Path(a.objdump).with_name(pathlib.Path(a.objdump).name.replace("objdump", "nm"))
    undef = subprocess.run([str(nm), "-u", a.binary], capture_output=True, text=True, check=True).stdout.split()
    undef = [u for u in undef if u not in ("U", "w", "v")]
    if undef:
        # a call to an undefined function, linked anyway, branches into the caller's code
        return {r: (None, "undefined symbols in the executable: " + " ".join(undef[:5])) for r in roots}
    lines = wcet.line_table(a.objdump, a.binary, names)
    with tempfile.TemporaryDirectory() as d:
        work = pathlib.Path(d)
        work.chmod(0o755)
        elf = work / "prog.elf"
        shutil.copyfile(a.binary, elf)
        calls, unsupported = otawa_flow.call_graph(a.objdump, str(elf))
        funcs, _ = otawa_flow.graphs(a.otawa_image, work, elf.name, roots, a.timeout)
        ffx_text, missing = otawa_flow.flow_facts(funcs, lines, bounds, LOOP_ENDS)
        ffx = work / "prog.ffx"
        ffx.write_text(ffx_text)
        for f in (elf, ffx):
            f.chmod(0o644)
        res, run = {}, []
        for r in roots:
            if r not in calls:
                res[r] = (None, "not found in the binary")
                continue
            why = otawa_flow.unsupported_reason(otawa_flow.reachable(calls, r), unsupported, missing, calls)
            if why:
                res[r] = (None, why)
            else:
                run.append(r)
        if run:
            res.update(otawa_flow.wcet(a.otawa_image, work, elf.name, ffx.name, run, a.processor, a.timeout))
    return res


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--report", action="append", required=True,
                    help="the plugin's JSON report (--report=FILE); one per --source")
    ap.add_argument("--source", action="append", required=True,
                    help="the source file the report before it describes")
    ap.add_argument("--binary", required=True, help="the compiled code (object or executable, with -g)")
    ap.add_argument("--processor", default="cortex-m0", choices=["cortex-m0", *otawa_flow.PROCESSORS])
    ap.add_argument("--otawa-image", default="otawa:dev", help="Docker image with OTAWA (other processors)")
    ap.add_argument("--timeout", type=float, default=600, help="seconds per OTAWA run")
    ap.add_argument("--clock-mhz", type=float, help="clock frequency, for budgets in microseconds")
    ap.add_argument("--context", action="store_true",
                    help="use the loop bounds of the calling contexts (whole program)")
    ap.add_argument("--certify", action="store_true",
                    help="cortex-m0: IPET bounds with certificates checked by the verified checker")
    ap.add_argument("--checker", default=str(HERE.parent.parent / "formalization/.lake/build/bin/crosscheck-check"),
                    help="crosscheck-check (with --certify)")
    ap.add_argument("--cycle-certificate", help="keep the cycle certificate in this file (with --certify)")
    ap.add_argument("--objdump", default=default_objdump())
    ap.add_argument("--json", help="write the results as JSON")
    a = ap.parse_args(argv)
    if a.certify and a.processor != "cortex-m0":
        ap.error("--certify is available for the cortex-m0 only")
    if len(a.report) != len(a.source):
        ap.error("give one --source for each --report")
    names = [pathlib.Path(x).name for x in a.source]
    if len(set(names)) != len(names):
        ap.error("two sources with the same file name: the debug lines cannot tell them apart")

    reports = [(n, json.loads(pathlib.Path(r).read_text())) for n, r in zip(names, a.report)]
    bounds = loop_bounds(reports, a.context)
    wanted = []
    for _, report in reports:
        for f in report["functions"]:
            if f.get("deadline_cycles") is not None or f.get("deadline_us") is not None:
                wanted.append(f)
    roots = sorted({f.get("symbol") or f["name"] for f in wanted})
    backend = m0_bounds if a.processor == "cortex-m0" else otawa_bounds
    cyc_of = backend(a, names, bounds, roots) if roots else {}

    rows, failed = [], False
    for f in wanted:
        dc, du = f.get("deadline_cycles"), f.get("deadline_us")
        sym = f.get("symbol") or f["name"]
        row = dict(function=f["name"], deadline_cycles=dc, deadline_us=du, cycles=None, us=None)
        if du is not None and not a.clock_mhz:
            row["verdict"] = "error: a budget in microseconds needs --clock-mhz"
            failed = True
            rows.append(row)
            continue
        cyc, why = cyc_of.get(sym, (None, "not analysed"))
        if cyc is None:
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
    tr = trusted(a.processor, a.certify)
    print(f"processor: {a.processor}{' (certified cycle bounds)' if a.certify else ''}; trusted: " + "; ".join(tr) + ("; loop bounds in context" if a.context else ""))
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(dict(processor=a.processor, clock_mhz=a.clock_mhz,
                                                        trusted=tr, functions=rows), indent=1) + "\n")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
