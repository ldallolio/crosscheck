#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Cycle counts of the TACLeBench kernels measured on a Cortex-M0 board (STM32F0), compared
with the emulator (benchmarks/cycles/m0.py, the timing table that Thumb.decode also uses)
and with the cycle bounds computed and certified by run_cycles.py on the same objects.

    # 1. the objects and bounds: run_cycles.py --certify DIR --json RUN.json ... (optionally
    #    --gcc IMAGE --tag=.gcc); then, without a board:
    python3 benchmarks/hardware/hw.py build --run RUN.json [--tag .gcc] [--board f091] [--out DIR]
    # 2. with the board connected (ST-Link), for each kernel: flash, read the serial line
    python3 benchmarks/hardware/hw.py measure --out DIR --port /dev/ttyACM0
    # 3. the comparison (also printed by `measure`)
    python3 benchmarks/hardware/hw.py report --out DIR

`build` links each KERNEL.m0TAG.o, unchanged, with stm32f0/startup.c (arm-none-eabi-gcc in a
Docker image, run without network) and records, per kernel, what the emulator predicts for
`main` with the STM32F0's single-cycle multiplier (`MUL_CYCLES = 1`) and the bounds of RUN.json
(computed with the 32-cycle multiplier unless run_cycles.py was given --mul-cycles 1: still upper
bounds). `measure` runs the flash command (default `st-flash --reset write {bin} 0x08000000`)
and reads `CROSSCHECK raw=R empty=E ret=V` from the serial port. The cycles of `main` on the
board are R − E + (emulator cycles of the empty function): the reads of the timer and the call
cancel out. Kernels that call library code (soft-float, memcpy...) run libgcc/newlib code on
the board while the emulator computes these calls natively: their counts are not comparable
and are reported apart. The register addresses of the start-up code come from the reference
manual (RM0091) and were not tried on a board when this script was written.
"""
import argparse
import json
import os
import pathlib
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "benchmarks/cycles"))
import m0  # noqa: E402

WORK = ROOT / "benchmarks/tacle/.cache/work"
BOARDS = {"f091": (256, 32), "f072": (128, 16), "f030r8": (64, 8)}   # flash KB, RAM KB
CFLAGS = ["-mcpu=cortex-m0", "-mthumb", "-mfloat-abi=soft", "-O1", "-g", "-ffreestanding", "-w"]

LD = """ENTRY(Reset_Handler)
MEMORY {{ FLASH (rx) : ORIGIN = 0x08000000, LENGTH = {flash}K
         RAM (rwx) : ORIGIN = 0x20000000, LENGTH = {ram}K }}
_estack = ORIGIN(RAM) + LENGTH(RAM);
SECTIONS {{
  .isr_vector : {{ KEEP(*(.isr_vector)) }} > FLASH
  .text : {{ *(.text .text.*) *(.rodata .rodata.*) . = ALIGN(4); }} > FLASH
  /DISCARD/ : {{ *(.ARM.exidx*) *(.ARM.extab*) }}
  _sidata = LOADADDR(.data);
  .data : {{ _sdata = .; *(.data .data.*) . = ALIGN(4); _edata = .; }} > RAM AT > FLASH
  .bss (NOLOAD) : {{ _sbss = .; *(.bss .bss.* COMMON) . = ALIGN(4); _ebss = .; }} > RAM
  ._stack (NOLOAD) : {{ . = ALIGN(8); . = . + 2048; }} > RAM
}}
"""


def docker(image, dirs, *cmd):
    mounts = [x for d in sorted({str(pathlib.Path(d).resolve()) for d in dirs}) for x in ("-v", f"{d}:{d}")]
    return subprocess.run(["docker", "run", "--rm", "--network", "none", "-u", f"{os.getuid()}:{os.getgid()}",
                           *mounts, image, *cmd], capture_output=True, text=True)


def emulate(obj, fn, mul):
    m0.MUL_CYCLES = mul
    img = m0.load(str(obj))
    mach = m0.Machine(img)
    ret = mach.call(fn, max_cycles=2 * 10**9)
    return mach.cyc, ret - (1 << 32) if ret is not None and ret >= 1 << 31 else ret, sorted(set(img.undefined.values()))


def build(a):
    out = pathlib.Path(a.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    flash, ram = BOARDS[a.board]
    (out / "link.ld").write_text(LD.format(flash=flash, ram=ram))
    p = docker(a.image, [HERE, out], "arm-none-eabi-gcc", *CFLAGS, "-c", str(HERE / "stm32f0/startup.c"),
               "-o", str(out / "startup.o"))
    if p.returncode:
        sys.exit("startup.c: " + p.stderr)
    empty_cycles, _, _ = emulate(out / "startup.o", "empty", 1)
    run = json.load(open(a.run)) if a.run else {"kernels": []}
    bounds = {k["kernel"]: k for k in run["kernels"]}
    manifest = dict(board=a.board, tag=a.tag, empty_emulated=empty_cycles, kernels={})
    for obj in sorted(WORK.glob(f"*.m0{a.tag}.o")):
        name = obj.name[:-len(f".m0{a.tag}.o")]
        if "." in name or (a.only and name not in a.only):
            continue
        k = dict(object=str(obj))
        try:
            k["emulated"], k["ret_emulated"], k["calls"] = emulate(obj, "main", 1)
            k["emulated_mul32"] = emulate(obj, "main", 32)[0]
        except Exception as e:   # noqa: BLE001
            k["emulated"], k["emulator_error"] = None, str(e)
        r = bounds.get(name, {})
        k["bound"] = r.get("main_bound")
        k["certified_bound"] = (r.get("certified_functions") or {}).get("main")
        elf = out / f"{name}.elf"
        p = docker(a.image, [out, WORK], "arm-none-eabi-gcc", "-mcpu=cortex-m0", "-mthumb", "-nostdlib",
                   "-T", str(out / "link.ld"), str(out / "startup.o"), str(obj), "-lc", "-lgcc", "-o", str(elf))
        if p.returncode:
            msg = p.stderr.strip().splitlines()
            k["link_error"] = next((m for m in msg if "overflowed" in m or "undefined reference" in m), msg[-1])[-200:]
        else:
            docker(a.image, [out], "arm-none-eabi-objcopy", "-O", "binary", str(elf), str(out / f"{name}.bin"))
            k["bin"] = str(out / f"{name}.bin")
        manifest["kernels"][name] = k
        print(f"{name:16s} emulated={k.get('emulated')} bound={k['bound']} certified={k['certified_bound']} "
              f"calls={','.join(k.get('calls', [])) or '-'} {k.get('link_error', 'linked')}")
    (out / "manifest.json").write_text(json.dumps(manifest, indent=1) + "\n")


def read_line(port, timeout):
    import termios
    fd = os.open(port, os.O_RDONLY | os.O_NOCTTY | os.O_NONBLOCK)
    try:
        t = termios.tcgetattr(fd)
        t[0] = t[1] = t[3] = 0
        t[2] = termios.CS8 | termios.CREAD | termios.CLOCAL
        t[4] = t[5] = termios.B115200
        termios.tcsetattr(fd, termios.TCSANOW, t)
        termios.tcflush(fd, termios.TCIFLUSH)
        buf, end = b"", time.monotonic() + timeout
        while time.monotonic() < end:
            try:
                buf += os.read(fd, 256)
            except BlockingIOError:
                time.sleep(0.01)
            for line in buf.split(b"\n"):
                if line.startswith(b"CROSSCHECK") and line.endswith(b"\r"):
                    return line.decode().strip()
        return None
    finally:
        os.close(fd)


def measure(a):
    out = pathlib.Path(a.out)
    man = json.load(open(out / "manifest.json"))
    for name, k in man["kernels"].items():
        if "bin" not in k or (a.only and name not in a.only):
            continue
        fl = subprocess.run(a.flash.format(bin=k["bin"]), shell=True, capture_output=True, text=True)
        if fl.returncode:
            k["measure_error"] = "flash: " + (fl.stdout + fl.stderr)[-200:]
            continue
        line = read_line(a.port, a.timeout)
        if line is None or "raw=" not in line:
            k["measure_error"] = f"no result ({line})"
            continue
        f = dict(x.split("=") for x in line.split()[1:])
        k["raw"], k["empty"], k["ret_board"] = int(f["raw"]), int(f["empty"]), int(f["ret"])
        k["board"] = k["raw"] - k["empty"] + man["empty_emulated"]
        print(f"{name:16s} board={k['board']} emulated={k.get('emulated')}")
    (out / "manifest.json").write_text(json.dumps(man, indent=1) + "\n")
    report(a)


def report(a):
    man = json.load(open(pathlib.Path(a.out) / "manifest.json"))
    lib = ("__aeabi_f", "__aeabi_d", "__aeabi_i2", "__aeabi_ui2", "__aeabi_l", "mem", "str")
    rows = []
    for name, k in man["kernels"].items():
        if "board" not in k:
            continue
        own = not any(c.startswith(lib) for c in k.get("calls", []))
        b, e = k["board"], k.get("emulated")
        cb = k.get("certified_bound")
        rows.append((name, b, e, (b - e) if e is not None else None, k.get("bound"), cb,
                     cb is None or b <= cb, k.get("ret_board") == k.get("ret_emulated"), own))
    print(f"{'kernel':16s} {'board':>10s} {'emulated':>10s} {'diff':>7s} {'bound':>10s} {'certified':>10s}  ok  ret  comparable")
    for r in rows:
        print(f"{r[0]:16s} {r[1]:10d} {r[2] if r[2] is not None else '-':>10} {r[3] if r[3] is not None else '-':>7} "
              f"{r[4] if r[4] is not None else '-':>10} {r[5] if r[5] is not None else '-':>10}  "
              f"{'yes' if r[6] else 'NO':3s} {'yes' if r[7] else 'NO':4s} {'yes' if r[8] else 'no (library calls)'}")
    bad = [r[0] for r in rows if not r[6]]
    exact = [r for r in rows if r[8] and r[3] == 0]
    print(f"measured {len(rows)}; above the certified bound: {bad or 'none'}; "
          f"equal to the emulator (own code only): {len(exact)} of {sum(r[8] for r in rows)}")
    if bad:
        sys.exit(1)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("build")
    b.add_argument("--run", help="RUN.json of run_cycles.py --certify (bounds of main)")
    b.add_argument("--tag", default="", help="objects KERNEL.m0TAG.o (e.g. .gcc, .nofp)")
    b.add_argument("--board", default="f091", choices=sorted(BOARDS))
    b.add_argument("--image", default="armgcc:local", help="Docker image with arm-none-eabi-gcc")
    for p in (b, sub.add_parser("measure"), sub.add_parser("report")):
        p.add_argument("--out", default=str(ROOT / "benchmarks/hardware/.build"))
        p.add_argument("--only", action="append")
    m = sub.choices["measure"]
    m.add_argument("--port", default="/dev/ttyACM0")
    m.add_argument("--flash", default="st-flash --reset write {bin} 0x08000000",
                   help="flash command; {bin} is replaced by the image (e.g. openocd -f board/st_nucleo_f0.cfg "
                        "-c 'program {bin} 0x08000000 verify reset exit')")
    m.add_argument("--timeout", type=float, default=60.0, help="seconds to wait for the result line")
    a = ap.parse_args()
    {"build": build, "measure": measure, "report": report}[a.cmd](a)


if __name__ == "__main__":
    main()
