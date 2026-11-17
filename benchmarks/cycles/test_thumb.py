#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Differential tests of the Lean decoder and timing table (`Thumb.decode`, run through
`crosscheck-check --decode`).

    python3 benchmarks/cycles/test_thumb.py [--checker crosscheck-check] [--objects DIR] [--objdump llvm-objdump]

1. Exhaustive, against `m0.py` (`decode` and `cycles`, MULS 32 cycles): every 16-bit
   halfword, followed once by `0xF800` (a BL second half) and once by `0x0000`: size,
   kind (`m0.py`'s `indirect` is the Lean `stop`), branch target and cycles must agree.
2. Against llvm-objdump (an independent decoder), on every `*.m0.o` of `--objects` (the
   Cortex-M0 objects of run_cycles.py): for every instruction it prints, the Lean kind and
   size must match its mnemonic, and the branch targets must be equal.
"""
import argparse
import json
import pathlib
import re
import shutil
import struct
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import m0  # noqa: E402

ROOT = HERE.parent.parent
COND = {"beq", "bne", "bhs", "bcs", "blo", "bcc", "bmi", "bpl", "bvs", "bvc", "bhi", "bls",
        "bge", "blt", "bgt", "ble"}
STOP = {"udf", "svc", "bkpt", "wfi", "wfe", "cpsie", "cpsid", "blx", "msr", "mrs", "dmb", "dsb", "isb"}


def decode_lean(checker, halfwords, addrs, mul=32):
    with tempfile.TemporaryDirectory() as d:
        p = pathlib.Path(d) / "dec.json"
        p.write_text(json.dumps(dict(mul_cycles=mul, code=dict(base=0, halfwords=halfwords), addresses=addrs)))
        out = subprocess.run([checker, "--decode", str(p)], capture_output=True, text=True, check=True).stdout
    res = {}
    for line in out.splitlines():
        f = line.split()
        a = int(f[0])
        res[a] = None if f[1] == "none" else (int(f[1]), f[2], None if f[3] == "-" else int(f[3]), int(f[4]), int(f[5]))
    return res


def expected_m0(mem, a):
    i = m0.decode(mem, a)
    kind = "stop" if i.kind in ("indirect", "stop") else i.kind
    if kind in ("cond", "jump", "call") and i.target < 0:
        return (i.size, "stop", None)
    if kind == "stop":
        return (i.size, "stop", None)
    t = i.target if kind in ("cond", "jump", "call") else None
    return (i.size, kind, t, m0.cycles(i, True), m0.cycles(i, False) if kind == "cond" else m0.cycles(i, True))


def exhaustive(checker):
    bad = 0
    for second in (0xF800, 0x0000):
        hws = []
        for h in range(1 << 16):
            hws += [h, second]
        mem = bytearray(struct.pack(f"<{len(hws)}H", *hws))
        addrs = [4 * h for h in range(1 << 16)]
        got = decode_lean(checker, hws, addrs)
        for a in addrs:
            exp = expected_m0(mem, a)
            g = got[a]
            g = g[:2] + (None,) if g and g[1] == "stop" else g
            if g != exp:
                bad += 1
                if bad <= 10:
                    print(f"halfword {a // 4:#06x} (then {second:#06x}): Lean {g}, m0.py {exp}")
    return bad


LINE = re.compile(r"^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+|(?:[0-9a-f]{4} ?){1,2})\s+(\S+)\s*([^@]*)")


def objdump_kind(mn, ops):
    mn = mn.split(".")[0]
    if mn == "b":
        return "jump"
    if mn == "bl":
        return "call"
    if mn in COND:
        return "cond"
    if mn == "bx":
        return "ret" if ops.strip() == "lr" else "stop"
    if mn == "pop":
        return "ret" if "pc" in ops else "seq"
    if mn in STOP:
        return "stop"
    if mn in ("mov", "add") and ops.replace(" ", "").startswith("pc,"):
        return "stop"
    return "seq"


def against_objdump(checker, objdump, objects):
    bad = total = 0
    for o in sorted(pathlib.Path(objects).glob("*.m0.o")):
        out = subprocess.run([objdump, "-d", str(o)], capture_output=True, text=True, check=True).stdout
        mem, insns = {}, []
        for line in out.splitlines():
            m = LINE.match(line)
            if not m:
                continue
            a, raw, mn, ops = int(m.group(1), 16), m.group(2).split(), m.group(3), m.group(4)
            if len(raw[0]) == 2:      # data, in bytes (little endian)
                bs = [int(x, 16) for x in raw]
                for k in range(0, len(bs) - 1, 2):
                    mem[a + k] = bs[k] | (bs[k + 1] << 8)
                continue
            for k, hw in enumerate(raw):
                mem[a + 2 * k] = int(hw, 16)
            insns.append((a, 2 * len(raw), mn, ops))
        if not insns:
            continue
        top = max(mem) + 2
        hws = [mem.get(2 * k, 0) for k in range(top // 2)]
        got = decode_lean(checker, hws, [a for a, *_ in insns])
        for a, size, mn, ops in insns:
            total += 1
            g = got[a]
            kind = objdump_kind(mn, ops)
            ok = g is not None and g[0] == size and g[1] == kind
            if ok and kind in ("cond", "jump", "call"):
                t = re.match(r"\s*(?:0x)?([0-9a-f]+)", ops)
                ok = t is not None and int(t.group(1), 16) == g[2]
            if not ok:
                bad += 1
                if bad <= 10:
                    print(f"{o.name} {a:#x}: objdump {mn} {ops.strip()} (size {size}, {kind}); Lean {g}")
    return bad, total


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--checker", default=str(ROOT / "formalization/.lake/build/bin/crosscheck-check"))
    ap.add_argument("--objects", default=str(ROOT / "benchmarks/tacle/.cache/work"))
    ap.add_argument("--objdump", default=shutil.which("llvm-objdump") or shutil.which("llvm-objdump-18")
                    or str(pathlib.Path.home() / "miniforge3/envs/crosscheck/bin/llvm-objdump"))
    a = ap.parse_args()
    if not pathlib.Path(a.checker).exists():
        print("crosscheck-check not built: skipped")
        return
    bad = exhaustive(a.checker)
    print(f"exhaustive: {2 * (1 << 16)} encodings, {bad} differences with m0.py")
    bad2, total = (0, 0)
    if pathlib.Path(a.objects).is_dir() and any(pathlib.Path(a.objects).glob("*.m0.o")):
        bad2, total = against_objdump(a.checker, a.objdump, a.objects)
        print(f"llvm-objdump: {total} instructions, {bad2} differences")
    else:
        print("no Cortex-M0 objects: the comparison with llvm-objdump is skipped")
    if bad or bad2:
        sys.exit("decoder differences")


if __name__ == "__main__":
    main()
