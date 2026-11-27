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
import os
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
# own check on Arm. Its cycles are still compared. cjpeg_transupp (sequential) reads
# `cjpeg_transupp_input5_2[65..71]` of an array of 65 (the "lower right corner" loop runs
# with `i == 8` after the loop before it): its expected checksum holds for x86's layout of
# the globals only.
EXPECTED_FAILURE = {"fft", "cjpeg_transupp"}

# Fixes of the work copy (never of the cache): debugging output left in two programs of the
# sequential category at the pinned revision (`printf` of counters, its declaration commented
# out). The binary has no `printf`, so the runs would stop at the call.
SOURCE_FIXES = {
    "anagram": [('printf("1: %d\\n", counter1);', ""), ('printf("2: %d\\n", counter2);', "")],
    "huff_enc": [('printf("%d\\n", counter1);', "")],
}

# the source analysis must use the binary's data model (sizeof(long), pointers: 4 bytes, not
# the host's 8), or a bound computed from sizeof is not the binary's (sha_byte_reverse: 8
# instead of 16 iterations; found on 2026-11-20 by the GCC run, a certified bound exceeded)
SOURCE_TARGET = ["--target=thumbv6m-none-eabi", "-mcpu=cortex-m0", "-mfloat-abi=soft"]
FLAGS = ["--target=thumbv6m-none-eabi", "-mcpu=cortex-m0", "-mfloat-abi=soft", "-O1", "-g",
         "-fno-unroll-loops", "-ffreestanding", "-fno-builtin", "-fno-unwind-tables",
         "-fno-asynchronous-unwind-tables", "-w", "-std=gnu99",
         # a call of an undeclared function is an error since Clang 16; such a function has
         # no code in the binary, so what reaches it stays unbounded
         "-Wno-error=implicit-function-declaration"]
# the same build with GCC (`--gcc IMAGE`: arm-none-eabi-gcc in a Docker image, run without
# network). Switch tables are compiled as branches (GCC's Thumb-1 tables call libgcc helpers,
# `__gnu_thumb1_case_*`, that rewrite the PC), and loops are not replaced by calls of memset
# or memcpy (not in the binary)
GCC_FLAGS = ["-mcpu=cortex-m0", "-mthumb", "-mfloat-abi=soft", "-O1", "-g", "-fno-unroll-loops",
             "-ffreestanding", "-fno-builtin", "-fno-jump-tables", "-fno-tree-loop-distribute-patterns",
             "-fno-unwind-tables", "-fno-asynchronous-unwind-tables", "-w", "-std=gnu99"]


def gcc_command(image, dirs):
    """arm-none-eabi-gcc in `image`, without network, with `dirs` mounted at the same paths."""
    import os
    mounts = [x for d in sorted({str(pathlib.Path(d).resolve()) for d in dirs}) for x in ("-v", f"{d}:{d}")]
    return ["docker", "run", "--rm", "--network", "none", "-u", f"{os.getuid()}:{os.getgid()}",
            *mounts, image, "arm-none-eabi-gcc"]


# compiler-rt's soft-float routines (Apache-2.0 with LLVM exception), at the tag of the Clang
# used here, fetched into the cache (never vendored) and compiled for the Cortex-M0
COMPILER_RT_TAG = "llvmorg-18.1.8"
COMPILER_RT_FILES = [
    "int_lib.h", "int_types.h", "int_endianness.h", "int_util.h", "int_math.h", "fp_lib.h", "fp_mode.h",
    "fp_add_impl.inc", "fp_mul_impl.inc", "fp_div_impl.inc", "fp_extend.h", "fp_extend_impl.inc",
    "fp_trunc.h", "fp_trunc_impl.inc", "fp_fixint_impl.inc", "fp_fixuint_impl.inc",
    "fp_compare_impl.inc", "int_to_fp.h", "int_to_fp_impl.inc", "assembly.h",
    "addsf3.c", "subsf3.c", "mulsf3.c", "divsf3.c", "adddf3.c", "subdf3.c", "muldf3.c", "divdf3.c",
    "comparesf2.c", "comparedf2.c", "fixsfsi.c", "fixunssfsi.c", "fixdfsi.c", "fixunsdfsi.c",
    "floatsisf.c", "floatunsisf.c", "floatsidf.c", "floatunsidf.c", "extendsfdf2.c", "truncdfsf2.c",
    "clzsi2.c", "fp_mode.c", "muldi3.c", "ashldi3.c", "lshrdi3.c", "ashrdi3.c", "arm/aeabi_fcmp.S", "arm/aeabi_dcmp.S"]
COMPILER_RT_FLAGS = ["--target=thumbv6m-none-eabi", "-mcpu=cortex-m0", "-mfloat-abi=soft", "-O2",
                     "-ffreestanding", "-fno-unwind-tables", "-fno-asynchronous-unwind-tables"]


def compiler_rt(cache, clang):
    """The archive of compiler-rt's soft-float routines for the Cortex-M0 (built once)."""
    import subprocess
    import urllib.request
    d = pathlib.Path(cache) / f"compiler-rt-{COMPILER_RT_TAG.removeprefix('llvmorg-')}"
    lib = d / "libclang_rt.builtins-armv6m.a"
    if lib.exists():
        return lib
    base = f"https://raw.githubusercontent.com/llvm/llvm-project/{COMPILER_RT_TAG}/compiler-rt/lib/builtins/"
    for f in COMPILER_RT_FILES:
        out = d / f
        if not out.exists():
            out.parent.mkdir(parents=True, exist_ok=True)
            req = urllib.request.Request(base + f, headers={"User-Agent": "Mozilla/5.0 (generic client)"})
            with urllib.request.urlopen(req, timeout=60) as r:
                out.write_bytes(r.read())
    objs = []
    for f in COMPILER_RT_FILES:
        if f.endswith((".c", ".S")):
            o = d / "obj" / (pathlib.Path(f).stem + ".o")
            o.parent.mkdir(exist_ok=True)
            subprocess.run([str(clang), *COMPILER_RT_FLAGS, f"-I{d}", "-c", str(d / f), "-o", str(o)], check=True)
            objs.append(str(o))
    ar = pathlib.Path(clang).with_name("llvm-ar")
    subprocess.run([str(ar) if ar.exists() else "llvm-ar", "rcs", str(lib), *objs], check=True)
    return lib


def link_command(image, obj, out, lib=None):
    """A relocatable link (`ld -r`) of `obj` with a run-time library, by arm-none-eabi-ld of
    `image` (run without network): the archive members that `obj` needs (floating point,
    ...) are added, as a link with the toolchain would add them; the division routines of
    runtime.c stay (they are defined in `obj`, so the library's are not taken). `lib`: an
    archive (compiler-rt), else the Cortex-M0 libgcc of the image's arm-none-eabi-gcc."""
    import os
    dirs = sorted({str(pathlib.Path(x).parent.resolve()) for x in [obj, out] + ([lib] if lib else [])})
    mounts = [x for d in dirs for x in ("-v", f"{d}:{d}")]
    archive = str(pathlib.Path(lib).resolve()) if lib else \
        "$(arm-none-eabi-gcc -mcpu=cortex-m0 -mthumb -mfloat-abi=soft -print-libgcc-file-name)"
    cmd = (f"arm-none-eabi-ld -r --no-warn-mismatch -o {pathlib.Path(out).resolve()} "
           f"{pathlib.Path(obj).resolve()} {archive}")
    if not image:   # arm-none-eabi-ld (binutils-arm-none-eabi) on this machine; compiler-rt only
        return ["sh", "-c", cmd]
    return ["docker", "run", "--rm", "--network", "none", "-u", f"{os.getuid()}:{os.getgid()}",
            *mounts, image, "sh", "-c", cmd]


def runtime_bounds(tool, work, extra):
    """CrossCheck's loop bounds for runtime.c (integer division)."""
    import subprocess
    report = work / "runtime.json"
    subprocess.run([str(tool), "--all", f"--report={report}", str(HERE / "runtime.c"), "--",
                    "-x", "c", "-std=gnu99", "-w", *extra, *SOURCE_TARGET], capture_output=True, text=True)
    rep = json.loads(report.read_text())
    return {l["line"]: (l["bound"] if l.get("verified") else None)
            for f in rep["functions"] for l in f["loops"]}


def loop_ends(functions, offset=0, ends=None):
    """source loop (its line, plus `offset`) -> its last line (plus `offset`), from a report's
    `end_line` (the largest if several loops share a line)."""
    ends = {} if ends is None else ends
    for f in functions:
        for l in f["loops"]:
            k = l["line"] + offset
            ends[k] = max(ends.get(k, 0), (l.get("end_line") or l["line"]) + offset)
    return ends


def main_blockers(an, certified, why, root="main"):
    """What keeps `root` without a certified cycle bound: the functions reachable from it by
    calls that have no certificate for a reason of their own (a loop without a bound, an
    indirect jump, a recursion, ...), not only because a callee has none, with that reason;
    a call of a routine without code is listed under its name. {} if `root` is certified."""
    if root not in an.img.funcs or root in certified:
        return {}
    addr = {a: n for n, (a, _) in an.img.funcs.items()}
    out, seen, todo = {}, {root}, [root]
    while todo:
        n = todo.pop()
        callees = []
        try:
            _e, blocks, _ = an.cfg(n)
            for il in blocks.values():
                for i in il:
                    if i.kind == "call" and i.target is not None:
                        callees.append(i.target)
        except wcet.Unbounded:
            pass
        for t in callees:
            if t in an.img.undefined:
                out.setdefault(f"{an.img.undefined[t]} (no code)", "called, no code in the binary")
            elif t not in addr:
                out.setdefault(f"{t:#x} (called from {n})", "call to an address that starts no function")
            elif addr[t] not in certified:
                if addr[t] not in seen:
                    seen.add(addr[t])
                    todo.append(addr[t])
        w = why.get(n, "?")
        callee_only = w.startswith("call to ") and ("which has no certificate" in w or
                                                    "which is not bounded" in w or "(no code)" in w)
        if not callee_only:
            out[n] = w
    return out


def analyse(kernel, work, tool, clang, objdump, extra, rt, certdir=None, checker=None, loops=False, abi=False,
            frame=False, cflags=(), tag="", gcc=None, rtlib=None, func_jobs=1, contexts=False):
    import subprocess
    t_all = time.monotonic()
    unit = kernel
    if kernel.name in SOURCE_FIXES:
        unit = run_tacle.Unit(kernel.name, sorted(kernel.glob("*.c")), [kernel],
                              patches=SOURCE_FIXES[kernel.name])
    run_tacle.run_kernel(tool, unit, work, [*extra, *SOURCE_TARGET])
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
    cc = gcc_command(gcc, [work, kernel]) + GCC_FLAGS if gcc else [str(clang), *FLAGS]
    p = subprocess.run([*cc, *cflags, f"-I{kernel}", "-c", str(work / f"{kernel.name}.m0.c"), "-o", str(obj)],
                       capture_output=True, text=True)
    if p.returncode:
        return dict(kernel=kernel.name, error="compilation failed: " + p.stderr[-300:])
    base_funcs = set(m0.load(str(obj)).funcs)
    if rtlib:
        image, lib = rtlib
        linked = work / f"{kernel.name}.m0{tag}.{'crt' if lib else 'lg'}.o"
        p = subprocess.run(link_command(image, obj, linked, lib), capture_output=True, text=True)
        if p.returncode:
            return dict(kernel=kernel.name, error="link with the run-time library failed: " + p.stderr[-300:])
        obj = linked
    img = m0.load(str(obj))
    # the run-time support: runtime.c's division and what the link with a run-time library added
    runtime = {n for n in img.funcs if n.startswith("__aeabi") or n not in base_funcs}
    lines = wcet.line_table(str(objdump), str(obj), f"{kernel.name}.m0.c")
    rt_rep = json.loads((work / "runtime.json").read_text())["functions"]
    ends = loop_ends(rt_rep, offset)
    an = wcet.Analysis(img, lines, bounds, loop_ends(rep["functions"], ends=ends))
    # jumps whose index the loop analysis bounds: with the assumptions of the certificates
    an.jt_opts = (abi, frame)
    static = {n: an.function(n) for n in sorted(img.funcs)}
    certified, cert_info = {}, {}
    if certdir:
        # IPET cycle certificates (ipet.py), checked by the verified checker if given
        # (Lean Cycles.program_sound); without a checker they are compared with the runs only
        lstats = {}
        doc, ib, iwhy = ipet.certify(an, sorted(img.funcs), loops=loops, abi=abi, stats=lstats, frame=frame,
                                      jobs=func_jobs, contexts=contexts)
        cf = pathlib.Path(certdir) / f"{kernel.name}.cycles.json"
        cf.write_text(json.dumps(doc) + "\n")
        certified = dict(ib)
        accepted, output = None, None
        if checker and doc["programs"]:
            # the code of the certificate checked against the object it comes from (`--elf`)
            out = subprocess.run([checker, "--elf", str(obj), str(cf)], capture_output=True, text=True)
            accepted = out.returncode == 0 and "PROGRAM  program: ACCEPTED" in out.stdout
            output = None if accepted else (out.stdout + out.stderr)[-400:]
        cert_info = dict(accepted=accepted, why=iwhy, checker_output=output, loops=lstats)
    sa = stackbound.StackAnalysis(img, jumps=an.jumps)
    sbound = {n: sa.function(n) for n in sorted(img.funcs)}
    # run, with the checks
    entry = {a: n for n, (a, _) in img.funcs.items()}
    bodies = {}
    for fn, ls in an.loops.items():
        if static.get(fn) is None:
            continue
        for (h, _lines, N, body) in ls:
            bodies[h] = (body, N, fn)
    # loops whose bound is certified on the machine code (binloops.py): checked against the runs too
    cbodies = {}
    sbodies = {}    # function -> {header: body} of the binary's loops (binloops.structure)
    for fn, st in (cert_info.get("loops") or {}).items():
        for (h, N, _src) in st["certified"]:
            ctx_loops = an.loops.get(fn, [])
            body = next((b for (hh, _l, _n, b) in ctx_loops if hh == h), None)
            if body is None:
                # the loops of a function without a static bound (the bodies of
                # binloops.Ctx.iloops, from the same structure, computed once per function)
                if fn not in sbodies:
                    import binloops
                    try:
                        _e, blocks, _s, _b, loops, headers, _n = binloops.structure(an, fn)
                        sbodies[fn] = {hh: {i.addr for b in loops[hh] for i in blocks[b]}
                                       for hh in headers}
                    except Exception:   # noqa: BLE001
                        sbodies[fn] = {}
                body = sbodies[fn].get(h)
            if body is not None:
                cbodies[h] = (body, N, fn)
    mach = m0.Machine(img)
    # the observations of the run (m0.Watch; by the C core of m0.py when it is built): the
    # cycles of the longest call of each function; for each activation, the stack pointer
    # at its entry and the lowest value seen until it returns (its callees included); the
    # back edges of each loop, against its bound and its certified bound
    watch = m0.Watch(entry, bodies, cbodies, img.stack_top)
    t0 = time.monotonic()
    try:
        ret = mach.call("main", max_cycles=2 * 10**9, watch=watch)
        run_error = None
    except m0.Stop as e:
        ret, run_error = None, str(e)
    observed, sobserved, frames = watch.observed, watch.sobserved, watch.frames
    worst_loop, viol = watch.worst_loop, watch.viol
    observed["main"] = mach.cyc
    sobserved["main"] = frames[0][0] - min(f[1] for f in frames)
    sviol = [f"{fn}: observed {s} bytes of stack > bound {sbound[fn]}"
             for fn, s in sobserved.items() if sbound.get(fn) is not None and s > sbound[fn]]
    scompared = [fn for fn in sobserved if sbound.get(fn) is not None and fn not in runtime]
    sown = {n: v for n, v in sbound.items() if n not in runtime}
    for fn, c in observed.items():
        if static.get(fn) is not None and c > static[fn]:
            viol.append(f"{fn}: observed {c} cycles > bound {static[fn]}")
        if certified.get(fn) is not None and c > certified[fn]:
            viol.append(f"{fn}: observed {c} cycles > certified bound {certified[fn]}")
    compared = [fn for fn in observed if static.get(fn) is not None and fn not in runtime]
    ratios = [static[fn] / observed[fn] for fn in compared if observed[fn]]
    own = {n: v for n, v in static.items() if n not in runtime}  # not runtime.c
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
                analysis_seconds=round(time.monotonic() - t_all, 1),
                **({} if not certdir else dict(
                    certified_functions={n: v for n, v in certified.items() if n not in runtime},
                    certificates_accepted=cert_info["accepted"],
                    certificate_checker_output=cert_info["checker_output"],
                    not_certified={n: cert_info["why"].get(n, "?") for n in own
                                   if own[n] is not None and n not in certified},
                    # what keeps `main` uncertified (functions with a reason of their own)
                    main_blockers=main_blockers(an, certified, cert_info["why"]),
                    certified_compared=sum(1 for fn in compared if certified.get(fn) is not None),
                    loops_certified=sum(len(v["certified"]) for v in (cert_info.get("loops") or {}).values()),
                    loops_not_certified=sum(len(v["other"]) for v in (cert_info.get("loops") or {}).values()),
                    loops_detail={fn: dict(certified=[[h, N, src] for h, N, src in v["certified"]],
                                           other=[[h, w] for h, w in v["other"]],
                                           seconds=round(v.get("seconds", 0.0), 1),
                                           meter=v.get("meter"))
                                  for fn, v in (cert_info.get("loops") or {}).items()},
                    loops_checked_certified=len(cbodies),
                    # linear programs stopped by the CPU-time limit (binloops.LP_SAFETY_CPU) or
                    # by HiGHS's wall-clock backstop (LP_WALL_SECONDS): the only limits that
                    # count time, not work; and the CPU seconds of the slowest successful
                    # solve (a machine LP_SAFETY_CPU / lp_ok_max_cpu times slower would stop it)
                    lp_safety={fn: v["meter"]["lp_safety"] for fn, v in (cert_info.get("loops") or {}).items()
                               if (v.get("meter") or {}).get("lp_safety")},
                    lp_wall={fn: v["meter"]["lp_wall"] for fn, v in (cert_info.get("loops") or {}).items()
                             if (v.get("meter") or {}).get("lp_wall")},
                    lp_ok_max_cpu=max([(v.get("meter") or {}).get("lp_ok_max_cpu", 0.0)
                                       for v in (cert_info.get("loops") or {}).values()], default=0.0),
                    certified_main_observed_ratio=(certified["main"] / mach.cyc) if certified.get("main") and ret is not None and mach.cyc else None)))


def analyse_guarded(kernel, *args, **kw):
    """`analyse`, with an exception of the analysis reported as the program's error (so that
    one program does not stop the run; `--check` still fails on it)."""
    import traceback
    try:
        return analyse(kernel, *args, **kw)
    except Exception as e:   # noqa: BLE001
        return dict(kernel=kernel.name, error=f"analysis failed: {type(e).__name__}: {e}"[:300],
                    traceback=traceback.format_exc()[-2000:])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tool", default=str(ROOT / "clang-plugin/build/crosscheck-tool"))
    ap.add_argument("--cache", default=str(ROOT / "benchmarks/tacle/.cache"))
    ap.add_argument("--extra-arg", action="append", default=[])
    ap.add_argument("--only", action="append")
    ap.add_argument("--category", action="append",
                    help="TACLeBench category (kernel, sequential, app; repeatable; default kernel)")
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
    ap.add_argument("--contexts", action="store_true",
                    help="with --certify-loops: give the functions with loops a precondition on r0-r3 from "
                         "their calls, proved at every call by the checker (their bounds then hold for the "
                         "calls of the program)")
    ap.add_argument("--amortised", action="store_true",
                    help="with --certify-loops: also look for amortised rows (the back edges of a loop "
                         "bounded per entry of a loop that encloses it; env CROSSCHECK_AMORT=1)")
    ap.add_argument("--cflag", action="append", default=[],
                    help="an extra compiler flag for the Cortex-M0 build (e.g. -fomit-frame-pointer)")
    ap.add_argument("--tag", default="",
                    help="suffix of the objects (KERNEL.m0TAG.o), so that another build does not replace the default one")
    ap.add_argument("--gcc", metavar="IMAGE",
                    help="compile with arm-none-eabi-gcc from this Docker image (run without network) "
                         "instead of Clang; use with --tag, e.g. --tag=.gcc")
    ap.add_argument("--rtlib", choices=["libgcc", "compiler-rt"],
                    help="link each object with a run-time library, so that floating point is "
                         "analysed on its machine code: libgcc (Cortex-M0 multilib of the image's "
                         "arm-none-eabi-gcc) or compiler-rt (fetched at COMPILER_RT_TAG, compiled "
                         "by --clang); the link runs in --link-image")
    ap.add_argument("--link-image", default="armgcc:local", metavar="IMAGE",
                    help="Docker image with arm-none-eabi-ld (and gcc, for libgcc), run without network; "
                         "'' for the arm-none-eabi-ld of this machine (with compiler-rt)")
    ap.add_argument("--mul-cycles", type=int, default=32, help="MULS cycles (32: small multiplier)")
    ap.add_argument("--jobs", type=int, default=1,
                    help="kernels analysed in parallel (processes; the largest objects first, "
                         "results printed in the usual order)")
    ap.add_argument("--func-jobs", type=int, default=1,
                    help="with --certify-loops: the functions of a program whose loops are "
                         "certified in parallel (processes; same certificates as one)")
    a = ap.parse_args()
    m0.MUL_CYCLES = a.mul_cycles
    src = run_tacle.fetch(pathlib.Path(a.cache), run_tacle.REV)
    if a.amortised:
        # the environment reaches the worker processes, whatever their start method
        os.environ["CROSSCHECK_AMORT"] = "1"
        import binloops
        binloops.AMORT = True
    work = pathlib.Path(a.cache) / "work"
    work.mkdir(parents=True, exist_ok=True)
    kernels = [k for cat in (a.category or ["kernel"]) for k in sorted((src / "bench" / cat).iterdir())
               if k.is_dir()]
    if a.only:
        kernels = [k for k in kernels if k.name in a.only]
    rows = []
    if a.certify:
        pathlib.Path(a.certify).mkdir(parents=True, exist_ok=True)
    rt = runtime_bounds(a.tool, work, a.extra_arg)
    rtlib = None if not a.rtlib else (a.link_image, compiler_rt(a.cache, a.clang) if a.rtlib == "compiler-rt" else None)
    args = lambda k: (k, work, a.tool, a.clang, a.objdump, a.extra_arg, rt, a.certify,  # noqa: E731
                      a.checker, a.certify_loops, a.abi, a.frame, a.cflag, a.tag, a.gcc, rtlib,
                      a.func_jobs, a.contexts)
    if a.jobs > 1:
        import concurrent.futures
        size = lambda k: sum(f.stat().st_size for f in k.glob("*.c"))  # noqa: E731
        pool = concurrent.futures.ProcessPoolExecutor(a.jobs)
        futs = {k.name: pool.submit(analyse_guarded, *args(k)) for k in sorted(kernels, key=size, reverse=True)}
        results = (futs[k.name].result() for k in kernels)
    else:
        results = (analyse_guarded(*args(k)) for k in kernels)
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
            for n, w in sorted(r.get("main_blockers", {}).items()):
                print(f"{'':16s} main blocked by {n}: {w}", file=sys.stderr)
        if r.get("lp_safety"):
            import binloops
            print(f"{'':16s} note: {sum(r['lp_safety'].values())} linear programs stopped after "
                  f"{binloops.LP_SAFETY_CPU:g} CPU seconds in {', '.join(sorted(r['lp_safety']))}", file=sys.stderr)
        if r.get("lp_wall"):
            print(f"{'':16s} warning: {sum(r['lp_wall'].values())} linear programs stopped by the "
                  f"wall-clock backstop of HiGHS in {', '.join(sorted(r['lp_wall']))}: their loops may "
                  f"be certified differently on another machine or under another load", file=sys.stderr)
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
                   lp_safety=sum(sum((r.get("lp_safety") or {}).values()) for r in ok),
                   lp_wall=sum(sum((r.get("lp_wall") or {}).values()) for r in ok),
                   lp_ok_max_cpu=max([r.get("lp_ok_max_cpu") or 0.0 for r in ok], default=0.0),
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
    failed = [r["kernel"] for r in rows if "error" in r and r["error"].startswith("analysis failed")]
    if failed:
        print("analysis failed: " + ", ".join(failed), file=sys.stderr)
    if a.check and (failed or tot["violations"] or tot["stack_violations"] or wrong or tot.get("certificates_rejected")):
        sys.exit("cycle check failed")


if __name__ == "__main__":
    main()
