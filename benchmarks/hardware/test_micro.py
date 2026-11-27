#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""The timing micro-benchmarks of `micro/` against the emulator.

    python3 benchmarks/hardware/test_micro.py [--as arm-none-eabi-gcc] [--checker crosscheck-check]

Each `micro/NAME.S` is a `main` that repeats one timing pattern 50 times and states the
cycles it takes, counted by hand from Table 3-1 of the Cortex-M0 Technical Reference
Manual (`@ expect cycles:`, with `m` the cycles of MULS), and its return value. The
programs are assembled (arm-none-eabi-gcc, skipped if absent) and run by `m0.py` with both
multipliers: its counts must equal the hand counts. With the checker built (and scipy), each
is also certified with loop certificates and checked against its object (`--elf`): the
certified bound must equal the exact count, except where the paths of a loop differ (`bcond`:
the worst path every iteration) and where a write of the PC is not a supported jump
(`pc_writes`: no bound). On a board, `hw.py build --micro` measures the same objects; there
the board decides.
"""
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "cycles"))
import m0  # noqa: E402

AS = os.environ.get("CROSSCHECK_ARM_GCC", "arm-none-eabi-gcc")
CHECKER = os.environ.get("CROSSCHECK_CHECKER",
                         str(HERE.parent.parent / "formalization/.lake/build/bin/crosscheck-check"))
# certified bounds that differ from the exact count (MULS 1 cycle): the worst path of the loop
# every iteration (bcond: 50 x 10 - 2 + 2 + 3); no bound (a MOV PC from ADR)
CERTIFIED = {"bcond": 503, "pc_writes": None}
MICRO = sorted((HERE / "micro").glob("*.S"))


def expected(src, m):
    text = src.read_text()
    cyc = re.search(r"^@ expect cycles: (.+)$", text, re.M).group(1)
    ret = re.search(r"^@ expect ret: (.+)$", text, re.M).group(1)
    ev = lambda e: eval(e, {"__builtins__": {}}, {"m": m})  # noqa: E731  (the files' own arithmetic)
    return ev(cyc), ev(ret)


def assemble(src, out):
    obj = pathlib.Path(out) / (src.stem + ".o")
    subprocess.run([AS, "-mcpu=cortex-m0", "-mthumb", "-c", str(src), "-o", str(obj)], check=True,
                   capture_output=True, text=True)
    return obj


def emulate(obj, mul):
    old = m0.MUL_CYCLES
    m0.MUL_CYCLES = mul
    try:
        mach = m0.Machine(m0.load(str(obj)))
        ret = mach.call("main", max_cycles=10**7)
        return mach.cyc, ret
    finally:
        m0.MUL_CYCLES = old


class Micro(unittest.TestCase):
    def test_files(self):
        self.assertEqual(len(MICRO), 8)
        for src in MICRO:
            text = src.read_text()
            self.assertIn("@ expect cycles:", text, src.name)
            self.assertTrue(text.isascii(), src.name)

    def test_emulator_equals_hand_counts(self):
        if not shutil.which(AS):
            self.skipTest(f"{AS} not found")
        with tempfile.TemporaryDirectory() as d:
            for src in MICRO:
                obj = assemble(src, d)
                for mul in (1, 32):
                    with self.subTest(program=src.stem, mul=mul):
                        cyc, ret = emulate(obj, mul)
                        self.assertEqual((cyc, ret), expected(src, mul))

    def test_certified(self):
        if not shutil.which(AS):
            self.skipTest(f"{AS} not found")
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        import json
        import ipet
        import wcet
        old = m0.MUL_CYCLES
        m0.MUL_CYCLES = 1
        try:
            with tempfile.TemporaryDirectory() as d:
                for src in MICRO:
                    with self.subTest(program=src.stem):
                        obj = assemble(src, d)
                        img = m0.load(str(obj))
                        doc, bounds, _ = ipet.certify(wcet.Analysis(img, {}, {}, {}), ["main"], mul=1,
                                                      loops=True, abi=True)
                        cert = pathlib.Path(d) / (src.stem + ".json")
                        cert.write_text(json.dumps(doc))
                        exact = expected(src, 1)[0]
                        self.assertEqual(bounds.get("main"), CERTIFIED.get(src.stem, exact))
                        if doc["programs"]:
                            r = subprocess.run([CHECKER, "--elf", str(obj), str(cert)], capture_output=True, text=True)
                            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                            self.assertIn("checked against", r.stdout)
        finally:
            m0.MUL_CYCLES = old


if __name__ == "__main__":
    if "--checker" in sys.argv:
        i = sys.argv.index("--checker")
        CHECKER = sys.argv[i + 1]
        del sys.argv[i:i + 2]
    if "--as" in sys.argv:
        i = sys.argv.index("--as")
        AS = sys.argv[i + 1]
        del sys.argv[i:i + 2]
    unittest.main()
