# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""The interpreter of m0.py compared with QEMU on the same machine code.

Each object (a kernel linked with its run-time library, as run_cycles.py leaves it in the
work directory) is laid out by `m0.load` from address 0x400; the same bytes, preceded by
a vector table and a start-up stub (call `main`, then exit through semihosting with its
result), are given to QEMU as a raw image. QEMU executes one instruction per translation
block and logs every block it executes (`-d exec,nochain`), so the number of executions of
every instruction address is known; the interpreter counts the same. The two runs must
return the same result and execute every address the same number of times.

QEMU's only board with Cortex-M0 is the micro:bit (16 KiB of RAM, read-only flash), too
small for the flat image; the MPS2 AN385 board (4 MiB of RAM at address 0) has a Cortex-M3,
which executes the ARMv6-M instructions of this code with the same architectural
semantics. This compares the instruction semantics and the control flow of m0.py, not its
cycle table: QEMU does not model the timing of the processor.

    python3 run_qemu.py [--qemu qemu-system-arm] OBJ...      (exit 1 on a difference)
"""
import argparse
import collections
import pathlib
import struct
import subprocess
import sys
import tempfile

import m0

BASE = 0x400
STACK = 1 << 20     # bytes of stack after the image (m0.load's `ram`)
SEMI_EXIT = 0x20026  # ADP_Stopped_ApplicationExit (SYS_EXIT_EXTENDED)


def startup(main, sp):
    """Vector table and stub below BASE: reset at 0x40 calls `main` and exits with r0; any
    fault exits with code 250."""
    code = bytearray(BASE)
    struct.pack_into("<II", code, 0, sp, 0x40 | 1)
    for k in range(2, 16):
        struct.pack_into("<I", code, 4 * k, 0x60 | 1)
    reset = [0x4B05,    # 0x40 ldr r3, [pc, #20]   (0x58: main | 1)
             0x4798,    # 0x42 blx r3
             0x4602,    # 0x44 mov r2, r0
             0x4905,    # 0x46 ldr r1, [pc, #20]   (0x5c: SEMI_EXIT)
             0xB406,    # 0x48 push {r1, r2}
             0x4669,    # 0x4a mov r1, sp
             0x2020,    # 0x4c movs r0, #0x20     (SYS_EXIT_EXTENDED)
             0xBEAB,    # 0x4e bkpt 0xab
             0xE7FE]    # 0x50 b .
    fault = [0x4903,    # 0x60 ldr r1, [pc, #12]   (0x70: SEMI_EXIT)
             0x22FA,    # 0x62 movs r2, #250
             0xB406, 0x4669, 0x2020, 0xBEAB, 0xE7FE]
    struct.pack_into(f"<{len(reset)}H", code, 0x40, *reset)
    struct.pack_into("<II", code, 0x58, main | 1, SEMI_EXIT)
    struct.pack_into(f"<{len(fault)}H", code, 0x60, *fault)
    struct.pack_into("<I", code, 0x70, SEMI_EXIT)
    return bytes(code)


def interpreter(img):
    """(result, {address: executions}) of `main` on m0.py."""
    mach = m0.Machine(img)
    count = collections.Counter()

    def hook(i, _before, _nxt):
        if i is not None:
            count[i.addr] += 1

    mach.on_insn = hook
    mach.call("main")
    return mach.r[0] & 0xFFFFFFFF, count


def qemu(qemu_bin, raw, timeout):
    """(exit status, {address: executions}) of the image on QEMU."""
    cmd = [qemu_bin, "-M", "mps2-an385", "-nographic", "-monitor", "none", "-serial", "none",
           "-semihosting-config", "enable=on,target=native", "-accel", "tcg,one-insn-per-tb=on",
           "-d", "exec,nochain", "-D", "/dev/stdout", "-kernel", raw]
    count = collections.Counter()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    try:
        for line in p.stdout:
            # "Trace 0: 0x... [<cs_base>/<pc>/<flags>/<cflags>] <symbol>"
            if line.startswith("Trace"):
                count[int(line[line.index("[") + 1:].split("/", 2)[1], 16)] += 1
        status = p.wait(timeout=timeout)
    finally:
        if p.poll() is None:
            p.kill()
    return status, count


def compare(obj, qemu_bin, timeout):
    img = m0.load(str(obj), base=BASE, ram=STACK)
    if img.undefined:
        return f"calls functions without code ({', '.join(sorted(set(img.undefined.values())))})"
    if img.stack_top > 0x400000:
        return "image larger than the 4 MiB of the board"
    # the image before the run (the interpreter writes the data and the stack of `img.mem`)
    image = startup(img.funcs["main"][0], img.stack_top) + bytes(img.mem[BASE:])
    res, mine = interpreter(img)
    with tempfile.TemporaryDirectory() as d:
        raw = pathlib.Path(d) / "image.bin"
        raw.write_bytes(image)
        status, theirs = qemu(qemu_bin, str(raw), timeout)
    theirs = {a: n for a, n in theirs.items() if a >= BASE}
    diff = sorted(a for a in set(mine) | set(theirs) if mine.get(a, 0) != theirs.get(a, 0))
    total = sum(mine.values())
    if status != (res & 0xFF) or diff:
        return (f"DIFFERENT: result {res} (exit status {status}), {len(diff)} addresses executed "
                f"a different number of times" + (f", first {diff[0]:#x}: m0.py "
                f"{mine.get(diff[0], 0)}, QEMU {theirs.get(diff[0], 0)}" if diff else ""))
    return f"same: result {res}, {total} instructions at {len(mine)} addresses"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("objects", nargs="+")
    ap.add_argument("--qemu", default="qemu-system-arm")
    ap.add_argument("--timeout", type=int, default=3600)
    a = ap.parse_args()
    bad = 0
    for obj in a.objects:
        r = compare(obj, a.qemu, a.timeout)
        bad += r.startswith("DIFFERENT")
        print(f"{pathlib.Path(obj).name:28s} {r}", flush=True)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
