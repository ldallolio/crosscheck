#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Cycle bounds on a Cortex-M0 for the TACLeBench kernels, from CrossCheck's loop bounds.

For each kernel (the same single-file unit as benchmarks/tacle/run_tacle.py):
1. CrossCheck derives the source loop bounds (in the calling contexts of `main`);
2. the kernel is compiled for the Cortex-M0 (`--target=thumbv6m-none-eabi`, -O1, no loop
   unrolling, no builtins), and every function receives a cycle bound by `wcet.py`;
3. the kernel is run on the interpreter of `m0.py` (it must return 0, its success code),
   and every call of a function with a bound is checked: its cycles must not exceed the
   bound; every binary loop's back-edge traversals per entry must not exceed the source
   bound it was matched with. `--check` fails on a violation.

    python3 benchmarks/cycles/run_cycles.py [--only bsort] [--json out.json] [--check]
"""
import argparse
import json
import pathlib
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "benchmarks/tacle"))
import m0  # noqa: E402
import wcet  # noqa: E402
import run_tacle  # noqa: E402

import shutil

def default_tool(name):
    """`name` from $PATH, else from the conda environment of CLAUDE.md."""
    found = shutil.which(name) or shutil.which(name + "-18")
    return found or str(pathlib.Path.home() / "miniforge3/envs/crosscheck/bin" / name)
# Programs whose result is not checked: fft converts negative floats to `unsigned long`
# (undefined behaviour in C; Arm's conversion saturates to 0, x86's wraps), so it fails its
# own check on Arm. Its cycles are still compared.
EXPECTED_FAILURE = {"fft"}

FLAGS = ["--target=thumbv6m-none-eabi", "-mcpu=cortex-m0", "-mfloat-abi=soft", "-O1", "-g",
         "-fno-unroll-loops", "-ffreestanding", "-fno-builtin", "-fno-unwind-tables",
         "-fno-asynchronous-unwind-tables", "-w", "-std=gnu99"]


def runtime_bounds(tool, work, extra):
    """CrossCheck's loop bounds for runtime.c (integer division)."""
    import subprocess
    report = work / "runtime.json"
    subprocess.run([str(tool), "--all", f"--report={report}", str(HERE / "runtime.c"), "--",
                    "-x", "c", "-std=gnu99", "-w", *extra], capture_output=True, text=True)
    rep = json.loads(report.read_text())
    return {l["line"]: (l["bound"] if l.get("verified") else None)
            for f in rep["functions"] for l in f["loops"]}


def analyse(kernel, work, tool, clang, objdump, extra, rt):
    import subprocess
    r = run_tacle.run_kernel(tool, kernel, work, extra)
    rep = json.loads((work / f"{kernel.name}.json").read_text())
    # the kernel followed by the run-time support (its lines shifted)
    text = (work / f"{kernel.name}.c").read_text(errors="replace")
    if not text.endswith("\n"):
        text += "\n"
    offset = text.count("\n")
    (work / f"{kernel.name}.m0.c").write_text(text + (HERE / "runtime.c").read_text())
    bounds = {line + offset: b for line, b in rt.items()}
    for f in rep["functions"]:
        for l in f["loops"]:
            b = l.get("in_context") if l.get("in_context") is not None else (l["bound"] if l.get("verified") else None)
            if l["line"] in bounds and bounds[l["line"]] is not None and b is not None:
                b = max(b, bounds[l["line"]])
            bounds[l["line"]] = b
    obj = work / f"{kernel.name}.m0.o"
    p = subprocess.run([str(clang), *FLAGS, f"-I{kernel}", "-c", str(work / f"{kernel.name}.m0.c"), "-o", str(obj)],
                       capture_output=True, text=True)
    if p.returncode:
        return dict(kernel=kernel.name, error="compilation failed: " + p.stderr[-300:])
    img = m0.load(str(obj))
    lines = wcet.line_table(str(objdump), str(obj), f"{kernel.name}.m0.c")
    an = wcet.Analysis(img, lines, bounds)
    static = {n: an.function(n) for n in sorted(img.funcs)}
    # run, with the checks
    entry = {a: n for n, (a, _) in img.funcs.items()}
    bodies = {}
    for fn, ls in an.loops.items():
        if static.get(fn) is None:
            continue
        for (h, _lines, N, body) in ls:
            bodies[h] = (body, N, fn)
    count, worst_loop = {}, {}
    stack, observed = [], {}
    viol = []
    mach = m0.Machine(img)

    def hook(i, before, nxt):
        if i is not None and i.kind == "call":
            stack.append((entry.get(i.target), mach.cyc, i.addr + 4))
        elif stack and nxt == stack[-1][2] and (i is None or i.kind == "ret"):
            fn, start, _ = stack.pop()
            if fn is not None:
                observed[fn] = max(observed.get(fn, 0), mach.cyc - start)
        if nxt in bodies and i is not None:
            body, N, fn = bodies[nxt]
            if i.addr in body:
                count[nxt] = count.get(nxt, 0) + 1
                if count[nxt] > N:
                    viol.append(f"loop {nxt:#x} of {fn}: {count[nxt]} back edges > bound {N}")
                worst_loop[nxt] = max(worst_loop.get(nxt, 0), count[nxt])
            else:
                count[nxt] = 0

    mach.on_insn = hook
    t0 = time.monotonic()
    try:
        ret = mach.call("main", max_cycles=2 * 10**9)
        run_error = None
    except m0.Stop as e:
        ret, run_error = None, str(e)
    observed["main"] = mach.cyc
    for fn, c in observed.items():
        if static.get(fn) is not None and c > static[fn]:
            viol.append(f"{fn}: observed {c} cycles > bound {static[fn]}")
    compared = [fn for fn in observed if static.get(fn) is not None and not fn.startswith("__aeabi")]
    ratios = [static[fn] / observed[fn] for fn in compared if observed[fn]]
    own = {n: v for n, v in static.items() if not n.startswith("__aeabi")}  # not runtime.c
    return dict(kernel=kernel.name, functions=len(own),
                bounded=sum(v is not None for v in own.values()),
                main_bound=static.get("main"), main_observed=mach.cyc if ret is not None else None,
                returned=ret, run_error=run_error, compared=len(compared),
                loops_checked=len(worst_loop), violations=viol,
                ratio_main=(static["main"] / mach.cyc) if static.get("main") and ret is not None and mach.cyc else None,
                max_ratio=max(ratios) if ratios else None, min_ratio=min(ratios) if ratios else None,
                why={n: an.why[n] for n in an.why if n in static and static[n] is None},
                seconds=round(time.monotonic() - t0, 1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tool", default=str(ROOT / "clang-plugin/build/crosscheck-tool"))
    ap.add_argument("--cache", default=str(ROOT / "benchmarks/tacle/.cache"))
    ap.add_argument("--extra-arg", action="append", default=[])
    ap.add_argument("--only", action="append")
    ap.add_argument("--clang", default=default_tool("clang"), help="Clang 18 with the ARM target")
    ap.add_argument("--objdump", default=default_tool("llvm-objdump"))
    ap.add_argument("--json")
    ap.add_argument("--check", action="store_true", help="fail on a violation or a wrong result")
    ap.add_argument("--mul-cycles", type=int, default=32, help="MULS cycles (32: small multiplier)")
    a = ap.parse_args()
    m0.MUL_CYCLES = a.mul_cycles
    src = run_tacle.fetch(pathlib.Path(a.cache), run_tacle.REV)
    work = pathlib.Path(a.cache) / "work"
    work.mkdir(parents=True, exist_ok=True)
    kernels = sorted((src / "bench/kernel").iterdir())
    if a.only:
        kernels = [k for k in kernels if k.name in a.only]
    rows = []
    rt = runtime_bounds(a.tool, work, a.extra_arg)
    for k in kernels:
        r = analyse(k, work, a.tool, a.clang, a.objdump, a.extra_arg, rt)
        rows.append(r)
        if "error" in r:
            print(f"{k.name:16s} {r['error']}", file=sys.stderr)
            continue
        mb = r["main_bound"]
        print(f"{k.name:16s} functions={r['functions']} bounded={r['bounded']} main_bound={mb} "
              f"observed={r['main_observed']} ret={r['returned']} compared={r['compared']} "
              f"loops={r['loops_checked']} violations={len(r['violations'])}"
              + (f" run_error={r['run_error']}" if r['run_error'] else ""), file=sys.stderr)
        for v in r["violations"]:
            print("   VIOLATION " + v, file=sys.stderr)
    ok = [r for r in rows if "error" not in r]
    tot = dict(kernels=len(rows), compiled=len(ok), ran=sum(r["returned"] == 0 for r in ok),
               functions=sum(r["functions"] for r in ok), bounded=sum(r["bounded"] for r in ok),
               main_bounded=sum(r["main_bound"] is not None for r in ok),
               compared=sum(r["compared"] for r in ok), loops=sum(r["loops_checked"] for r in ok),
               violations=sum(len(r["violations"]) for r in ok))
    print(json.dumps(tot), file=sys.stderr)
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(dict(total=tot, kernels=rows), indent=2) + "\n")
    wrong = [r["kernel"] for r in ok if r["returned"] != 0 and r["kernel"] not in EXPECTED_FAILURE]
    if wrong:
        print("wrong result or run error: " + ", ".join(wrong), file=sys.stderr)
    if a.check and (tot["violations"] or wrong):
        sys.exit("cycle check failed")


if __name__ == "__main__":
    main()
