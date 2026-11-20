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
4. with `--certify DIR`, the bounded functions also get IPET cycle certificates
   (`ipet.py`, written to DIR/KERNEL.cycles.json), whose bounds are checked against the
   same runs; with `--checker crosscheck-check`, the verified checker must accept them
   (Lean `Cycles.program_sound`), otherwise `--check` fails.

    python3 benchmarks/cycles/run_cycles.py [--only bsort] [--json out.json] [--check]
        [--certify DIR [--checker formalization/.lake/build/bin/crosscheck-check]]
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
import ipet  # noqa: E402
import wcet  # noqa: E402
import stack as stackbound  # noqa: E402
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


def analyse(kernel, work, tool, clang, objdump, extra, rt, certdir=None, checker=None, loops=False, abi=False,
            frame=False, cflags=(), tag=""):
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
    obj = work / f"{kernel.name}.m0{tag}.o"
    p = subprocess.run([str(clang), *FLAGS, *cflags, f"-I{kernel}", "-c", str(work / f"{kernel.name}.m0.c"), "-o", str(obj)],
                       capture_output=True, text=True)
    if p.returncode:
        return dict(kernel=kernel.name, error="compilation failed: " + p.stderr[-300:])
    img = m0.load(str(obj))
    lines = wcet.line_table(str(objdump), str(obj), f"{kernel.name}.m0.c")
    an = wcet.Analysis(img, lines, bounds)
    static = {n: an.function(n) for n in sorted(img.funcs)}
    certified, cert_info = {}, {}
    if certdir:
        # IPET cycle certificates (ipet.py), checked by the verified checker if given
        # (Lean Cycles.program_sound); without a checker they are compared with the runs only
        lstats = {}
        doc, ib, iwhy = ipet.certify(an, sorted(img.funcs), loops=loops, abi=abi, stats=lstats, frame=frame)
        cf = pathlib.Path(certdir) / f"{kernel.name}.cycles.json"
        cf.write_text(json.dumps(doc) + "\n")
        certified = dict(ib)
        accepted, output = None, None
        if checker and doc["programs"]:
            out = subprocess.run([checker, str(cf)], capture_output=True, text=True)
            accepted = out.returncode == 0 and "PROGRAM  program: ACCEPTED" in out.stdout
            output = None if accepted else (out.stdout + out.stderr)[-400:]
        cert_info = dict(accepted=accepted, why=iwhy, checker_output=output, loops=lstats)
    sa = stackbound.StackAnalysis(img)
    sbound = {n: sa.function(n) for n in sorted(img.funcs)}
    # run, with the checks
    entry = {a: n for n, (a, _) in img.funcs.items()}
    bodies = {}
    for fn, ls in an.loops.items():
        if static.get(fn) is None:
            continue
        for (h, _lines, N, body) in ls:
            bodies[h] = (body, N, fn)
    count, worst_loop = {}, {}
    # loops whose bound is certified on the machine code (binloops.py): checked against the runs too
    cbodies, ccount = {}, {}
    for fn, st in (cert_info.get("loops") or {}).items():
        for (h, N, _src) in st["certified"]:
            ctx_loops = an.loops.get(fn, [])
            body = next((b for (hh, _l, _n, b) in ctx_loops if hh == h), None)
            if body is None:
                import binloops
                try:
                    c = binloops.Ctx(an, fn, abi)
                    body = set(next(b for (hh, b, _n) in c.iloops if hh == h))
                except Exception:   # noqa: BLE001
                    body = None
            if body is not None:
                cbodies[h] = (body, N, fn)
    stack, observed = [], {}
    viol = []
    mach = m0.Machine(img)
    # Stack: for each activation, the stack pointer at its entry and the lowest value seen
    # until it returns (its callees included).
    frames, sobserved = [], {}

    def hook(i, before, nxt):
        sp = mach.r[13]
        if frames and sp < frames[-1][1]:
            frames[-1][1] = sp
        if i is not None and i.kind == "call":
            stack.append((entry.get(i.target), mach.cyc, i.addr + 4))
            frames.append([sp, sp])
        elif stack and nxt == stack[-1][2] and (i is None or i.kind == "ret"):
            fn, start, _ = stack.pop()
            at_entry, low = frames.pop()
            if frames and low < frames[-1][1]:
                frames[-1][1] = low
            if fn is not None:
                observed[fn] = max(observed.get(fn, 0), mach.cyc - start)
                sobserved[fn] = max(sobserved.get(fn, 0), at_entry - low)
        if nxt in bodies and i is not None:
            body, N, fn = bodies[nxt]
            if i.addr in body:
                count[nxt] = count.get(nxt, 0) + 1
                if count[nxt] > N:
                    viol.append(f"loop {nxt:#x} of {fn}: {count[nxt]} back edges > bound {N}")
                worst_loop[nxt] = max(worst_loop.get(nxt, 0), count[nxt])
            else:
                count[nxt] = 0
        if nxt in cbodies and i is not None:
            body, N, fn = cbodies[nxt]
            if i.addr in body:
                ccount[nxt] = ccount.get(nxt, 0) + 1
                if ccount[nxt] > N:
                    viol.append(f"loop {nxt:#x} of {fn}: {ccount[nxt]} back edges > certified bound {N}")
            else:
                ccount[nxt] = 0

    mach.on_insn = hook
    t0 = time.monotonic()
    frames.append([img.stack_top, img.stack_top])
    try:
        ret = mach.call("main", max_cycles=2 * 10**9)
        run_error = None
    except m0.Stop as e:
        ret, run_error = None, str(e)
    observed["main"] = mach.cyc
    sobserved["main"] = frames[0][0] - min(f[1] for f in frames)
    sviol = [f"{fn}: observed {s} bytes of stack > bound {sbound[fn]}"
             for fn, s in sobserved.items() if sbound.get(fn) is not None and s > sbound[fn]]
    scompared = [fn for fn in sobserved if sbound.get(fn) is not None and not fn.startswith("__aeabi")]
    sown = {n: v for n, v in sbound.items() if not n.startswith("__aeabi")}
    for fn, c in observed.items():
        if static.get(fn) is not None and c > static[fn]:
            viol.append(f"{fn}: observed {c} cycles > bound {static[fn]}")
        if certified.get(fn) is not None and c > certified[fn]:
            viol.append(f"{fn}: observed {c} cycles > certified bound {certified[fn]}")
    compared = [fn for fn in observed if static.get(fn) is not None and not fn.startswith("__aeabi")]
    ratios = [static[fn] / observed[fn] for fn in compared if observed[fn]]
    own = {n: v for n, v in static.items() if not n.startswith("__aeabi")}  # not runtime.c
    return dict(kernel=kernel.name, functions=len(own),
                bounded=sum(v is not None for v in own.values()),
                bounded_functions={n: v for n, v in own.items() if v is not None},
                main_bound=static.get("main"), main_observed=mach.cyc if ret is not None else None,
                returned=ret, run_error=run_error, compared=len(compared),
                loops_checked=len(worst_loop), violations=viol,
                ratio_main=(static["main"] / mach.cyc) if static.get("main") and ret is not None and mach.cyc else None,
                max_ratio=max(ratios) if ratios else None, min_ratio=min(ratios) if ratios else None,
                why={n: an.why[n] for n in an.why if n in static and static[n] is None},
                stack_bounded=sum(v is not None for v in sown.values()),
                stack_main_bound=sbound.get("main"), stack_main_observed=sobserved.get("main"),
                stack_compared=len(scompared),
                stack_exact=sum(1 for fn in scompared if sobserved[fn] == sbound[fn]),
                stack_violations=sviol,
                stack_why={n: sa.why[n] for n in sa.why if n in sown},
                seconds=round(time.monotonic() - t0, 1),
                **({} if not certdir else dict(
                    certified_functions={n: v for n, v in certified.items() if not n.startswith("__aeabi")},
                    certificates_accepted=cert_info["accepted"],
                    certificate_checker_output=cert_info["checker_output"],
                    not_certified={n: cert_info["why"].get(n, "?") for n in own
                                   if own[n] is not None and n not in certified},
                    certified_compared=sum(1 for fn in compared if certified.get(fn) is not None),
                    loops_certified=sum(len(v["certified"]) for v in (cert_info.get("loops") or {}).values()),
                    loops_not_certified=sum(len(v["other"]) for v in (cert_info.get("loops") or {}).values()),
                    loops_detail={fn: dict(certified=[[h, N, src] for h, N, src in v["certified"]],
                                           other=[[h, w] for h, w in v["other"]])
                                  for fn, v in (cert_info.get("loops") or {}).items()},
                    loops_checked_certified=len(cbodies),
                    certified_main_observed_ratio=(certified["main"] / mach.cyc) if certified.get("main") and ret is not None and mach.cyc else None)))


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
    ap.add_argument("--certify", metavar="DIR",
                    help="also write IPET cycle certificates (KERNEL.cycles.json) into DIR and compare their bounds with the runs")
    ap.add_argument("--checker", help="crosscheck-check, to check the cycle certificates (with --certify)")
    ap.add_argument("--certify-loops", action="store_true",
                    help="with --certify: also certify the loop bounds on the machine code (binloops.py)")
    ap.add_argument("--abi", action="store_true",
                    help="with --certify-loops: assume that callees preserve r4-r7 and SP (AAPCS)")
    ap.add_argument("--frame", action="store_true",
                    help="with --certify-loops: for functions that take no address of their frame, assume "
                         "that stores through other registers and calls do not write it")
    ap.add_argument("--cflag", action="append", default=[],
                    help="an extra compiler flag for the Cortex-M0 build (e.g. -fomit-frame-pointer)")
    ap.add_argument("--tag", default="",
                    help="suffix of the objects (KERNEL.m0TAG.o), so that another build does not replace the default one")
    ap.add_argument("--mul-cycles", type=int, default=32, help="MULS cycles (32: small multiplier)")
    ap.add_argument("--jobs", type=int, default=1,
                    help="kernels analysed in parallel (processes; the largest objects first, "
                         "results printed in the usual order)")
    a = ap.parse_args()
    m0.MUL_CYCLES = a.mul_cycles
    src = run_tacle.fetch(pathlib.Path(a.cache), run_tacle.REV)
    work = pathlib.Path(a.cache) / "work"
    work.mkdir(parents=True, exist_ok=True)
    kernels = sorted((src / "bench/kernel").iterdir())
    if a.only:
        kernels = [k for k in kernels if k.name in a.only]
    rows = []
    if a.certify:
        pathlib.Path(a.certify).mkdir(parents=True, exist_ok=True)
    rt = runtime_bounds(a.tool, work, a.extra_arg)
    args = lambda k: (k, work, a.tool, a.clang, a.objdump, a.extra_arg, rt, a.certify,  # noqa: E731
                      a.checker, a.certify_loops, a.abi, a.frame, a.cflag, a.tag)
    if a.jobs > 1:
        import concurrent.futures
        size = lambda k: sum(f.stat().st_size for f in k.glob("*.c"))  # noqa: E731
        pool = concurrent.futures.ProcessPoolExecutor(a.jobs)
        futs = {k.name: pool.submit(analyse, *args(k)) for k in sorted(kernels, key=size, reverse=True)}
        results = (futs[k.name].result() for k in kernels)
    else:
        results = (analyse(*args(k)) for k in kernels)
    for k, r in zip(kernels, results):
        rows.append(r)
        if "error" in r:
            print(f"{k.name:16s} {r['error']}", file=sys.stderr)
            continue
        mb = r["main_bound"]
        print(f"{k.name:16s} functions={r['functions']} bounded={r['bounded']} main_bound={mb} "
              f"observed={r['main_observed']} ret={r['returned']} compared={r['compared']} "
              f"loops={r['loops_checked']} violations={len(r['violations'])}"
              + (f" run_error={r['run_error']}" if r['run_error'] else ""), file=sys.stderr)
        if a.certify:
            cf = r["certified_functions"]
            print(f"{'':16s} certified: {len(cf)} of {r['bounded']} bounded, accepted={r['certificates_accepted']}, "
                  f"main={cf.get('main')} (schema {r['main_bound']}), "
                  f"lower than the schema: {sum(1 for n, v in cf.items() if v < r['bounded_functions'].get(n, v + 1))}"
                  + (f", loops certified on the code: {r['loops_certified']} of "
                     f"{r['loops_certified'] + r['loops_not_certified']}" if a.certify_loops else ""),
                  file=sys.stderr)
        for v in r["violations"]:
            print("   VIOLATION " + v, file=sys.stderr)
        print(f"{'':16s} stack: bounded={r['stack_bounded']} main_bound={r['stack_main_bound']} "
              f"observed={r['stack_main_observed']} compared={r['stack_compared']} exact={r['stack_exact']} "
              f"violations={len(r['stack_violations'])}", file=sys.stderr)
        for v in r["stack_violations"]:
            print("   STACK VIOLATION " + v, file=sys.stderr)
    ok = [r for r in rows if "error" not in r]
    tot = dict(kernels=len(rows), compiled=len(ok), ran=sum(r["returned"] == 0 for r in ok),
               functions=sum(r["functions"] for r in ok), bounded=sum(r["bounded"] for r in ok),
               main_bounded=sum(r["main_bound"] is not None for r in ok),
               compared=sum(r["compared"] for r in ok), loops=sum(r["loops_checked"] for r in ok),
               violations=sum(len(r["violations"]) for r in ok),
               stack_bounded=sum(r["stack_bounded"] for r in ok),
               stack_main_bounded=sum(r["stack_main_bound"] is not None for r in ok),
               stack_compared=sum(r["stack_compared"] for r in ok),
               stack_exact=sum(r["stack_exact"] for r in ok),
               stack_violations=sum(len(r["stack_violations"]) for r in ok))
    if a.certify:
        cf = [(n, v, r["bounded_functions"].get(n)) for r in ok for n, v in r["certified_functions"].items()]
        tot.update(certified=len(cf), certified_main=sum("main" in r["certified_functions"] for r in ok),
                   certificates_rejected=sum(r["certificates_accepted"] is False for r in ok),
                   certified_compared=sum(r["certified_compared"] for r in ok),
                   certified_below_schema=sum(1 for _, v, s in cf if s is not None and v < s),
                   certified_equal_schema=sum(1 for _, v, s in cf if s is not None and v == s),
                   certified_above_schema=sum(1 for _, v, s in cf if s is not None and v > s),
                   bounded_not_certified=sum(len(r["not_certified"]) for r in ok))
        if a.certify_loops:
            tot.update(loops_certified=sum(r["loops_certified"] for r in ok),
                       loops_not_certified=sum(r["loops_not_certified"] for r in ok))
    print(json.dumps(tot), file=sys.stderr)
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(dict(total=tot, kernels=rows), indent=2) + "\n")
    wrong = [r["kernel"] for r in ok if r["returned"] != 0 and r["kernel"] not in EXPECTED_FAILURE]
    if wrong:
        print("wrong result or run error: " + ", ".join(wrong), file=sys.stderr)
    if a.check and (tot["violations"] or tot["stack_violations"] or wrong or tot.get("certificates_rejected")):
        sys.exit("cycle check failed")


if __name__ == "__main__":
    main()
