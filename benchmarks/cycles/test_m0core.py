# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""The C core of the interpreter (m0core.c) against m0.py.

* every instruction encoding of a sample, from random registers and flags (addresses in the
  memory half of the time): one instruction by `Machine._step`, by `Machine.execute` alone
  (without the handlers of `m0.FAST`) and by the core must leave the same registers, flags,
  cycles and memory, or raise the same exception;
* a program with a loop, a call and an instruction left to m0.py (ADD r0, PC): the same
  observations (`m0.Watch`), with loop bounds exceeded on purpose;
* the cycle limit;
* the kernels compiled by run_cycles.py, when they are in the cache: their first 10^6
  cycles (whole runs: run_cycles.py gives the same results with CROSSCHECK_M0_CORE=python).

    python3 test_m0core.py [--all]      (--all: every 16-bit encoding)
"""
import glob
import os
import pathlib
import random
import struct
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import m0  # noqa: E402

HERE = pathlib.Path(__file__).resolve().parent
LIB = m0.core()
ALL = "--all" in sys.argv
if ALL:
    sys.argv.remove("--all")


def image(code, at=0x100, size=0x10000):
    img = m0.Image()
    img.mem = bytearray(size)
    img.mem[at:at + len(code)] = code
    img.funcs = {"f": (at, len(code))}
    img.base, img.ro_top, img.stack_top = 0, at + len(code), size - 64
    return img


def bl(at, target):
    off = target - (at + 4)
    s, i1, i2 = (off >> 24) & 1, (off >> 23) & 1, (off >> 22) & 1
    j1, j2 = (1 - i1) ^ s, (1 - i2) ^ s
    return struct.pack("<HH", 0xF000 | (s << 10) | ((off >> 12) & 0x3FF),
                       0xD000 | (j1 << 13) | (j2 << 11) | ((off >> 1) & 0x7FF))


def state(mach):
    return (list(mach.r), (int(mach.n), int(mach.z), int(mach.c), int(mach.v)), mach.cyc, bytes(mach.mem))


def one(code, regs, flags, mode):
    """The state after one instruction at 0x100, or the exception, by m0.py or the core."""
    img = image(code)
    mach = m0.Machine(img)
    mach.r[:] = list(regs)
    mach.n, mach.z, mach.c, mach.v = flags
    saved = m0.FAST
    if mode == "exec":
        m0.FAST = {}        # every instruction by `Machine.execute` (test_effect.py's path)
    try:
        if mode in ("py", "exec"):
            mach._step(0x100, 0)
        else:
            m0._run_core(mach, LIB, 0x100, 0, m0.Watch({}, {}, {}, img.stack_top))
        return ("ok",) + state(mach)
    except m0.Stop as e:   # the cycle limit after the instruction: its state
        return ("stop", str(e)) + state(mach)
    except Exception as e:  # noqa: BLE001
        return ("error", type(e).__name__, str(e))
    finally:
        m0.FAST = saved


@unittest.skipIf(LIB is None, "no C compiler: the core is not built")
class Core(unittest.TestCase):
    def test_instructions(self):
        rnd = random.Random(1)
        hs = range(0x10000) if ALL else rnd.sample(range(0x10000), 6000)
        cases = 0
        for h in hs:
            code = struct.pack("<HH", h, rnd.randrange(0x10000))
            for _ in range(2):
                regs = [rnd.randrange(0x10000) if rnd.random() < 0.5 else rnd.randrange(1 << 32)
                        for _ in range(13)]
                regs += [rnd.randrange(0x400, 0xFF00) & ~3, rnd.randrange(1 << 32) | 1, 0]
                flags = tuple(rnd.randrange(2) for _ in range(4))
                a, b = one(code, regs, flags, "py"), one(code, regs, flags, "c")
                self.assertEqual(a, b, f"{h:#06x} {regs} {flags}")
                self.assertEqual(a, one(code, regs, flags, "exec"), f"{h:#06x} (m0.FAST)")
                cases += 1
        print(f"{cases} single instructions, the same", file=sys.stderr)

    def program(self):
        code = bytearray()
        code += struct.pack("<HH", 0xB510, 0x2405)      # 0x100 push {r4, lr}; movs r4, #5
        code += bl(0x104, 0x110)                         # 0x104 bl g      (loop header)
        code += struct.pack("<HH", 0x3C01, 0xD1FB)      # 0x108 subs r4, #1; bne 0x104
        code += struct.pack("<HH", 0x2000, 0xBD10)      # 0x10c movs r0, #0; pop {r4, pc}
        code += struct.pack("<HH", 0x4478, 0x4770)      # 0x110 g: add r0, pc; bx lr
        img = image(bytes(code))
        img.funcs = {"main": (0x100, 0x10), "g": (0x110, 4)}
        return img

    def watched(self, mode, limit=10**9):
        img = self.program()
        mach = m0.Machine(img)
        entry = {a: n for n, (a, _) in img.funcs.items()}
        body = {0x104, 0x108, 0x10A}
        w = m0.Watch(entry, {0x104: (body, 2, "main")}, {0x104: (body, 3, "main")}, img.stack_top)
        saved = list(m0._CORE)
        m0._CORE[:] = [None if mode == "py" else LIB]
        try:
            ret = mach.call("main", max_cycles=limit, watch=w)
        except m0.Stop as e:
            ret = str(e)
        finally:
            m0._CORE[:] = saved
        return (ret,) + state(mach) + (w.observed, w.sobserved, w.worst_loop, w.viol, w.frames)

    def test_program(self):
        a, b = self.watched("py"), self.watched("c")
        self.assertEqual(a, b)
        self.assertEqual(a[0], 0)
        self.assertEqual(a[8], ["loop 0x104 of main: 3 back edges > bound 2",
                                "loop 0x104 of main: 4 back edges > bound 2",
                                "loop 0x104 of main: 4 back edges > certified bound 3"])
        self.assertEqual(a[7], {0x104: 4})
        self.assertIn("g", a[5])

    def test_cycle_limit(self):
        for limit in (1, 7, 20, 40):
            self.assertEqual(self.watched("py", limit), self.watched("c", limit))

    def test_kernels(self):
        objs = sorted(o for o in glob.glob(str(HERE / "../tacle/.cache/work/*.m0.crt.o"))
                      if ".prof." not in o and ".rt." not in o)
        objs = [o for o in objs if os.path.getsize(o) < 400_000][:12]
        if not objs:
            self.skipTest("no kernel in the cache (run run_cycles.py --rtlib compiler-rt first)")
        for o in objs:
            res = []
            for mode in ("py", "c"):
                img = m0.load(o)
                mach = m0.Machine(img)
                entry = {a: n for n, (a, _) in img.funcs.items()}
                w = m0.Watch(entry, {}, {}, img.stack_top)
                saved = list(m0._CORE)
                m0._CORE[:] = [None if mode == "py" else LIB]
                try:
                    # runs stopped at 10^6 cycles: the state at the limit must agree too
                    ret = mach.call("main", max_cycles=10**6, watch=w)
                except m0.Stop as e:
                    ret = str(e)
                finally:
                    m0._CORE[:] = saved
                res.append((ret,) + state(mach) + (w.observed, w.sobserved, w.frames))
            self.assertEqual(res[0], res[1], o)


if __name__ == "__main__":
    unittest.main()
