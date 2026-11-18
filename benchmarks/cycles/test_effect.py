#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Differential test of the Lean data effects (`Thumb.effect`, `valOf`, `flagsAdd`,
`flagsSub`, `condHolds`, run through `crosscheck-check --effect`) against the interpreter
of `m0.py`.

    python3 benchmarks/cycles/test_effect.py [--checker crosscheck-check] [--states 3]

For every 16-bit halfword (followed by 0xF800, a BL second half) and several random states
(small register values, so that loads and stores stay in memory, and random words), the
instruction is executed by `m0.py`; every register that Lean says is kept must be kept,
every value Lean computes must be the one written, and the flags must be kept or equal to
those Lean computes, unless Lean says "any". Instructions that `decode` classifies as
`stop` are skipped (the check refuses them). The fourteen conditions are compared on the
flags of every state. Also with the assumption on callees (`abi`).
"""
import argparse
import json
import pathlib
import random
import struct
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import m0  # noqa: E402

ROOT = HERE.parent.parent
MEM = 1 << 16
BASE = 1 << 20          # the code, above the memory that loads and stores reach
NOWRITE = ("bcond", "b", "bl", "push", "bx", "blx", "nop")


def lean_effects(checker, hws, cases, abi):
    with tempfile.TemporaryDirectory() as d:
        p = pathlib.Path(d) / "eff.json"
        p.write_text(json.dumps(dict(code=dict(base=BASE, halfwords=hws), abi=abi,
                                     cases=[dict(a=a, r=r, f=f) for a, r, f in cases])))
        out = subprocess.run([checker, "--effect", str(p)], capture_output=True, text=True, check=True).stdout
    return [line.split() for line in out.splitlines()]


def run_m0(img, i, r, f):
    """Registers r0-r7 and flags after the instruction, or None (not executable here)."""
    mach = m0.Machine(img)
    mach.r = list(r) + [0] * 5 + [0x8000, 0, 0]
    mach.r[13] = 0x8000
    mach.n, mach.z, mach.c, mach.v = f
    if i.op in NOWRITE:
        return list(r), tuple(f)
    if i.op == "pop":
        out = list(r)
        for k in i.a[0]:
            if k < 8:
                out[k] = None          # any value
        return out, tuple(f)
    try:
        mach.execute(i, i.addr)
    except (m0.Stop, struct.error, IndexError):
        return None
    return [x & 0xFFFFFFFF for x in mach.r[:8]], (mach.n, mach.z, mach.c, mach.v)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--checker", default=str(ROOT / "formalization/.lake/build/bin/crosscheck-check"))
    ap.add_argument("--states", type=int, default=3)
    a = ap.parse_args()
    if not pathlib.Path(a.checker).exists():
        print("crosscheck-check not built: skipped")
        return
    rnd = random.Random(1)
    hws = []
    for h in range(1 << 16):
        hws += [h, 0xF800]
    img = type("I", (), {})()
    img.mem = bytearray(BASE) + bytearray(struct.pack(f"<{len(hws)}H", *hws))
    img.funcs, img.undefined, img.base, img.stack_top = {}, {}, 0, 0x8000
    bad = checked = 0
    for abi in (False, True):
        cases, meta = [], []
        for h in range(1 << 16):
            addr = BASE + 4 * h
            i = m0.decode(img.mem, addr)
            if i.kind in ("stop", "indirect") or i.op in ("unsupported32",):
                continue
            for s in range(a.states):
                if s == 0:
                    r = [rnd.randrange(0, 64) * 4 for _ in range(8)]
                else:
                    r = [rnd.choice([rnd.randrange(1 << 32), rnd.randrange(16), (1 << 32) - 1 - rnd.randrange(16),
                                     (1 << 31) + rnd.randrange(-8, 8)]) for _ in range(8)]
                f = [rnd.randrange(2) for _ in range(4)]
                cases.append((addr, r, f))
                meta.append(i)
        res = lean_effects(a.checker, hws, cases, abi)
        for (addr, r, f), i, line in zip(cases, meta, res):
            regs, fl, conds = line[1:9], line[9], line[10]
            mach = m0.Machine(img)
            mach.n, mach.z, mach.c, mach.v = f
            for cc in range(14):
                if int(conds[cc]) != int(bool(mach.cond(cc))):
                    bad += 1
                    if bad <= 10:
                        print(f"condition {cc} on flags {f}: Lean {conds[cc]}")
            got = run_m0(img, i, r, f)
            if got is None:
                continue
            post, pf = got
            checked += 1
            ok = True
            for k in range(8):
                if regs[k] == "k":
                    ok &= post[k] is not None and post[k] == r[k]
                elif regs[k].startswith("="):
                    ok &= post[k] is not None and post[k] == int(regs[k][1:])
            if fl == "keep":
                ok &= tuple(pf) == tuple(f)
            elif fl != "any":
                ok &= tuple(int(x) for x in fl) == tuple(int(x) for x in pf)
            if i.op == "bl" and any(x != "?" for x in regs[:4]):
                ok = False
            if not ok:
                bad += 1
                if bad <= 10:
                    print(f"{i} (halfword {(addr - BASE) // 4:#06x}) regs {r} flags {f}: m0.py {post} {pf}; Lean {line[1:10]}")
    print(f"effects: {checked} executions compared, {bad} differences")
    if bad:
        sys.exit("effect differences")


if __name__ == "__main__":
    main()
