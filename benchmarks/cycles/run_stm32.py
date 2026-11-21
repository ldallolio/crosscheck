#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""CrossCheck's loop bounds on processors whose timing model is OTAWA's (Cortex-M4, M7).

    run_stm32.py [--processor stm32f4|stm32h7]... [--only KERNEL]... [--json OUT]
                 [--m0-json run_cycles.json] [--lld LLD]

For each TACLeBench kernel: CrossCheck bounds the loops of the source (bounds in the calling
contexts of `main`, else for every call, as in run_cycles.py); the kernel is compiled for a
Cortex-M4 with its single-precision FPU (`-mcpu=cortex-m4 -mfloat-abi=hard
-mfpu=fpv4-sp-d16 -O1 -g`, the other flags of run_cycles.py, each function in its own
section) and linked at the addresses of an STM32 (code from 0x08000000, data from
0x20000000); the loops of OTAWA's control-flow graphs are matched with the source loops and
given as flow facts (`otawa_flow.py`, as `crosscheck_link.py --processor` does), and OTAWA
computes the WCET of every function in a container without network.

A function gets no WCET if it reaches a function that calls an undefined symbol (double
precision floating point, `memcpy`...: there is no run-time library; such a call is linked
to the next instruction, so OTAWA's graph would be wrong), if it reaches an indirect call or
jump, a jump table or a branch into another function (`otawa_flow.call_graph`), if a loop
it reaches has no flow fact, or if OTAWA fails. Nothing here is checked against
executions: there is no Cortex-M4/M7 simulator in this repository, and the timing models
are OTAWA's (`otawa_flow.PROCESSORS`). With `--m0-json` (the JSON of run_cycles.py), the
functions are compared with those bounded on the Cortex-M0.
"""
import argparse
import json
import pathlib
import re
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "benchmarks" / "tacle"))
import otawa_flow  # noqa: E402
import run_cycles  # noqa: E402
import run_tacle  # noqa: E402
import wcet  # noqa: E402

FLAGS = ["--target=thumbv7em-none-eabi", "-mcpu=cortex-m4", "-mfloat-abi=hard", "-mfpu=fpv4-sp-d16",
         "-O1", "-g", "-fno-unroll-loops", "-ffreestanding", "-fno-builtin", "-fno-unwind-tables",
         "-fno-asynchronous-unwind-tables", "-ffunction-sections", "-w", "-std=gnu99"]
RELSEC = re.compile(r"^RELOCATION RECORDS FOR \[(?:\.rel)?\.text\.(.+)\]:")
REL = re.compile(r"^[0-9a-f]+ R_ARM_\S+\s+(\S+)")


def default_lld():
    for p in sorted(pathlib.Path.home().glob(".rustup/toolchains/*/lib/rustlib/*/bin/rust-lld")):
        return str(p)
    return run_cycles.default_tool("ld.lld")


def calls_undefined(objdump, obj, undefined):
    """Functions (by section .text.<name>) with a relocation to an undefined symbol."""
    out = subprocess.run([objdump, "-r", obj], capture_output=True, text=True, check=True).stdout
    bad, cur = set(), None
    for line in out.splitlines():
        m = RELSEC.match(line)
        if m:
            cur = m.group(1)
            continue
        if line.startswith("RELOCATION RECORDS"):
            cur = None
        m = REL.match(line)
        if m and cur and m.group(1) in undefined:
            bad.add(cur)
    return bad


def cause(e):
    """The kind of a reason of otawa_flow.unsupported_reason, without names and addresses."""
    if e.startswith("calls an undefined symbol"):
        return "calls an undefined symbol"
    if " is recursive" in e:
        return "recursion"
    if "which has no code" in e:
        return "call of a function without code"
    e = re.sub(r"^[^ :]+: ", "", e)
    return re.sub(r" at (0x)?[0-9a-f]+| \(.*\)|^loop at 0x[0-9a-f]+:? ?", "", e).strip()


def analyse(kernel, work, a):
    name = kernel.name
    run_tacle.run_kernel(a.tool, kernel, work, [*a.extra_arg, *FLAGS[:4]])   # the binary's data model
    rep = json.loads((work / f"{name}.json").read_text())
    src = work / f"{name}.c"
    bounds = {}
    for f in rep["functions"]:
        for lp in f["loops"]:
            b = lp.get("in_context") if lp.get("in_context") is not None else (lp["bound"] if lp.get("verified") else None)
            k = (src.name, lp["line"])
            bounds[k] = b if k not in bounds else (None if b is None or bounds[k] is None else max(b, bounds[k]))
    obj, elf = work / f"{name}.m4.o", work / f"{name}.m4.elf"
    p = subprocess.run([a.clang, *FLAGS, f"-I{kernel}", "-c", str(src), "-o", str(obj)], capture_output=True, text=True)
    if p.returncode:
        return dict(kernel=name, status="compilation failed")
    nm = a.objdump.replace("objdump", "nm")
    undefined = set(subprocess.run([nm, "-u", str(obj)], capture_output=True, text=True).stdout.split()) - {"U", "w"}
    bad = calls_undefined(a.objdump, str(obj), undefined)
    p = subprocess.run([a.lld, "-flavor", "gnu", "-e", "main", "--unresolved-symbols=ignore-all",
                        "--Ttext=0x08000000", "--Tdata=0x20000000", "--Tbss=0x20010000", "-o", str(elf), str(obj)],
                       capture_output=True, text=True)
    if p.returncode:
        return dict(kernel=name, status="not linked: " + p.stderr[-160:])
    elf.chmod(0o644)
    defined = subprocess.run([nm, "--defined-only", str(elf)], capture_output=True, text=True).stdout.split("\n")
    funcs = sorted(l.split()[2] for l in defined if len(l.split()) == 3 and l.split()[1] in "Tt")
    lines = wcet.line_table(a.objdump, str(elf), [src.name])
    ffx = work / f"{name}.m4.ffx"
    ffx.unlink(missing_ok=True)   # OTAWA would load it by itself (the binary's name)
    calls, unsupported = otawa_flow.call_graph(a.objdump, str(elf))
    graphs, _ = otawa_flow.graphs(a.image, work, elf.name, funcs, a.timeout)
    ends = {(src.name, l): e for l, e in run_cycles.loop_ends(rep["functions"]).items()}
    ffx_text, missing = otawa_flow.flow_facts(graphs, lines, bounds, ends)
    ffx.write_text(ffx_text)
    ffx.chmod(0o644)
    row = dict(kernel=name, functions=len(funcs), flow_facts=ffx_text.count("<loop "), results={})
    run = []
    for f in funcs:
        reach = otawa_flow.reachable(calls, f)
        why = (next((f"calls an undefined symbol ({g})" for g in sorted(reach) if g in bad), None)
               or otawa_flow.unsupported_reason(reach, unsupported, missing, calls))
        if why:
            row["results"][f] = dict(error=why)
        else:
            run.append(f)
    for proc in a.processor:
        res = otawa_flow.wcet(a.image, work, elf.name, ffx.name, run, proc, a.timeout) if run else {}
        for f in run:
            c, err = res.get(f, (None, "no result"))
            row["results"].setdefault(f, {})[proc] = c
            if err:
                row["results"][f][proc + "_error"] = err
    row["status"] = "ok"
    return row


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tool", default=str(ROOT / "clang-plugin/build/crosscheck-tool"))
    ap.add_argument("--cache", default=str(ROOT / "benchmarks/tacle/.cache"))
    ap.add_argument("--extra-arg", action="append", default=[])
    ap.add_argument("--only", action="append")
    ap.add_argument("--clang", default=run_cycles.default_tool("clang"))
    ap.add_argument("--objdump", default=run_cycles.default_tool("llvm-objdump"))
    ap.add_argument("--lld", default=default_lld())
    ap.add_argument("--image", default="otawa:dev")
    ap.add_argument("--timeout", type=float, default=300)
    ap.add_argument("--processor", action="append", choices=list(otawa_flow.PROCESSORS))
    ap.add_argument("--m0-json", help="results of run_cycles.py --json, for the comparison")
    ap.add_argument("--json")
    a = ap.parse_args()
    a.processor = a.processor or list(otawa_flow.PROCESSORS)
    src = run_tacle.fetch(pathlib.Path(a.cache), run_tacle.REV)
    work = pathlib.Path(a.cache) / "stm32"
    work.mkdir(parents=True, exist_ok=True)
    work.chmod(0o755)
    kernels = sorted((src / "bench/kernel").iterdir())
    if a.only:
        kernels = [k for k in kernels if k.name in a.only]
    t0 = time.monotonic()
    rows = []
    for k in kernels:
        r = analyse(k, work, a)
        rows.append(r)
        res = r.get("results", {})
        print(f"{r['kernel']:16s} functions={r.get('functions', 0)} facts={r.get('flow_facts', 0)} "
              + " ".join(f"{p}={sum(x.get(p) is not None for x in res.values())}" for p in a.processor)
              + f"  {r['status']}", file=sys.stderr)
    tot = dict(kernels=len(rows), functions=sum(r.get("functions", 0) for r in rows),
               flow_facts=sum(r.get("flow_facts", 0) for r in rows), seconds=round(time.monotonic() - t0))
    for p in a.processor:
        tot[p] = sum(x.get(p) is not None for r in rows for x in r.get("results", {}).values())
        tot[p + "_main"] = sum(r.get("results", {}).get("main", {}).get(p) is not None for r in rows)
    causes = {}
    for r in rows:
        for x in r.get("results", {}).values():
            if "error" in x:
                c = cause(x["error"])
                causes[c] = causes.get(c, 0) + 1
            for p in a.processor:
                if p + "_error" in x:
                    c = p + ": " + ("timeout or no result" if "no result" in x[p + "_error"] else "OTAWA error")
                    causes[c] = causes.get(c, 0) + 1
    tot["not_bounded_by_cause"] = dict(sorted(causes.items(), key=lambda kv: -kv[1]))
    if a.m0_json:
        m0rows = json.loads(pathlib.Path(a.m0_json).read_text())
        m0rows = m0rows.get("kernels", m0rows) if isinstance(m0rows, dict) else m0rows
        m0b = {(r["kernel"], f) for r in m0rows for f in r.get("bounded_functions") or {}}
        p = a.processor[0]
        mine = {(r["kernel"], f) for r in rows for f, x in r.get("results", {}).items() if x.get(p) is not None}
        tot["compared_with_m0"] = dict(m0=len(m0b), both=len(m0b & mine), only_m0=len(m0b - mine),
                                       only_otawa=len(mine - m0b))
    print(json.dumps(tot))
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(dict(total=tot, kernels=rows), indent=1) + "\n")


if __name__ == "__main__":
    main()
