#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Produces every artifact that the slides (docs/slides/slides.md) show, from fir.c, into
out/: the plugin's report and source certificate, the checker's verdicts, the Cortex-M0
object and its disassembly, the timing-schema and certified cycle bounds, the cycle
certificate with loops certified on the machine code, an emulated run, the time-budget
check after compilation, and a tampered certificate that the checker rejects.

    python3 docs/slides/demo/run_demo.py [--tool ...] [--clang ...] [--objdump ...] [--checker ...]

Needs the plugin's crosscheck-tool, Clang 18 with the ARM target, llvm-objdump, the Lean
checker (lake build crosscheck-check) and scipy. Each step's wall time goes to out/times.json.
"""
import argparse
import json
import pathlib
import shutil
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
sys.path.insert(0, str(ROOT / "benchmarks/cycles"))
sys.path.insert(0, str(ROOT / "clang-plugin/scripts"))
import crosscheck_link  # noqa: E402
import ipet  # noqa: E402
import m0  # noqa: E402
import wcet  # noqa: E402

TARGET = ["--target=thumbv6m-none-eabi", "-mcpu=cortex-m0", "-mfloat-abi=soft"]
FLAGS = [*TARGET, "-O1", "-g", "-fno-unroll-loops", "-ffreestanding", "-fno-builtin", "-w", "-std=gnu99"]
TIMES = {}


def tool_default(name):
    env = pathlib.Path.home() / "miniforge3/envs/crosscheck/bin" / name
    return shutil.which(name) or str(env)


def run(step, cmd, out=None, ok=(0,)):
    t = time.monotonic()
    p = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT)   # relative paths in the outputs
    TIMES[step] = round(time.monotonic() - t, 3)
    if out:
        (OUT / out).write_text(p.stdout + p.stderr)
    if p.returncode not in ok:
        sys.exit(f"{step} failed ({p.returncode}):\n{p.stdout}\n{p.stderr}")
    return p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tool", default=str(ROOT / "clang-plugin/build/crosscheck-tool"))
    ap.add_argument("--clang", default=tool_default("clang"))
    ap.add_argument("--objdump", default=tool_default("llvm-objdump"))
    ap.add_argument("--checker", default=str(ROOT / "formalization/.lake/build/bin/crosscheck-check"))
    ap.add_argument("--extra-arg", action="append", default=["--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13"])
    a = ap.parse_args()
    OUT.mkdir(exist_ok=True)
    src, inc = pathlib.Path("docs/slides/demo/fir.c"), pathlib.Path("clang-plugin/include")
    out = OUT.relative_to(ROOT)

    # 1. the plugin, at compile time (unverified): report and source certificate
    run("plugin", [a.tool, "--all", "--summary", f"--report={out / 'report.json'}",
                   f"--opt=certificates={out / 'source-cert.json'}", "--opt=minic", str(src), "--",
                   "-x", "c", f"-I{inc}", *a.extra_arg, *TARGET], out="plugin.txt")
    # the plugin writes absolute paths: keep the artifacts independent of this machine (the
    # paths are labels; the checker reads the certificate's own copy of the source)
    for f in ("report.json", "source-cert.json", "plugin.txt"):
        p = OUT / f
        p.write_text(p.read_text().replace(str(ROOT) + "/", ""))
    # 2. the verified checker on the source certificate (and the mini-C validation)
    run("check source certificate", [a.checker, str(out / "source-cert.json")], out="check-source.txt")
    # 3. the compiler: Cortex-M0 object, and its disassembly with source lines
    run("compile", [a.clang, *FLAGS, f"-ffile-prefix-map={ROOT}=.", f"-I{inc}", "-c", str(src), "-o", str(out / "fir.o")])
    run("disassemble", [a.objdump, "-d", "-l", "--no-show-raw-insn", str(out / "fir.o")], out="fir.s")
    # 4. the binary: timing schema, and IPET certificate with loops certified on the code
    t = time.monotonic()
    rep = json.loads((OUT / "report.json").read_text())   # (OUT: absolute, for this process)
    bounds = crosscheck_link.loop_bounds([(src.name, rep)], context=False)
    img = m0.load(str(OUT / "fir.o"))
    lines = wcet.line_table(a.objdump, str(OUT / "fir.o"), [src.name])
    an = wcet.Analysis(img, lines, bounds, crosscheck_link.LOOP_ENDS)
    schema = {f: an.function(f) for f in ("dot", "fir_peak")}
    stats = {}
    doc, certified, why = ipet.certify(an, ["fir_peak"], loops=True, abi=True, stats=stats)
    (OUT / "cycles-cert.json").write_text(json.dumps(doc, indent=1) + "\n")
    TIMES["binary analysis and cycle certificate (untrusted producer)"] = round(time.monotonic() - t, 3)
    # the certificate's code checked against the object it was made from (--elf)
    run("check cycle certificate", [a.checker, "--elf", str(out / "fir.o"), str(out / "cycles-cert.json")],
        out="check-cycles.txt")
    # 5. an emulated run with the largest block (the kernel's interpreter, same timing table)
    t = time.monotonic()
    mach = m0.Machine(img)
    mach.call("fir_peak", (56,))
    observed = mach.cyc
    mach = m0.Machine(img)
    mach.call("dot", (0,))
    observed_dot = mach.cyc
    TIMES["emulated runs"] = round(time.monotonic() - t, 3)
    # 6. the time budget after compilation (linker step: here the object itself)
    run("time budget", [sys.executable, str(ROOT / "clang-plugin/scripts/crosscheck_link.py"),
                        "--report", str(out / "report.json"), "--source", str(src), "--binary", str(out / "fir.o"),
                        "--clock-mhz", "48", "--certify", "--checker", a.checker], out="budget.txt", ok=(0, 1))
    # 7. a tampered certificate: one cycle less than certified must be rejected
    bad = json.loads(json.dumps(doc))
    f = next(f for f in bad["programs"][0]["functions"] if f["name"] == "fir_peak")
    f["certificate"]["bound"] -= 1
    (OUT / "tampered-cert.json").write_text(json.dumps(bad) + "\n")
    run("check tampered certificate", [a.checker, "--elf", str(out / "fir.o"), str(out / "tampered-cert.json")],
        out="check-tampered.txt", ok=(1,))
    summary = dict(schema=schema, certified=certified, observed_fir_peak_n56=observed, observed_dot=observed_dot,
                   loops=stats, why=why, times=TIMES)
    (OUT / "summary.json").write_text(json.dumps(summary, indent=1, default=str) + "\n")
    (OUT / "times.json").write_text(json.dumps(TIMES, indent=1) + "\n")
    print(json.dumps(summary, indent=1, default=str))


if __name__ == "__main__":
    main()
