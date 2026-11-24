#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Tests of the jumps through a table (`switch`): the producer (jumptable.py, ipet.py,
binloops.py) and the check by crosscheck-check (Lean `ThumbDataCore.jumpOk`, `interiorOk`,
`ThumbData.drun_mrun`).

    python3 -m pytest -q benchmarks/cycles/test_jumptable.py

A function `switch (r0) { 0, 1, 2 }` in the form Clang emits for the Cortex-M0 (byte table
after `ADD PC, r0`) is certified; the checker accepts the certificate, and rejects it when
a target is dropped, the window is moved, the range check is widened without the targets,
or a branch enters the window (then the jump can leave the function: shown on m0.py). The
exact values that the data semantics gives to `ADD rd, PC`, `ADR` and the loads from the
code (`xop`/`xres`), and the address of `ADD PC, rm`/`MOV PC, rm` (`pcWrite`/`pcDestV`), are
compared with m0.py (`crosscheck-check --effect`), on states whose addresses fall in the
code. The checker is skipped if not built.
"""
import copy
import json
import os
import pathlib
import random
import struct
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import ipet  # noqa: E402
import jumptable  # noqa: E402
import m0  # noqa: E402
import wcet  # noqa: E402

CHECKER = os.environ.get("CROSSCHECK_CHECKER",
                         str(HERE.parent.parent / "formalization/.lake/build/bin/crosscheck-check"))

# at 0x100: cmp r0,#2; bhi 0x116; add r0,pc; ldrb r0,[r0,#4]; lsls r0,r0,#1; add pc,r0;
# table (bytes 1, 2, 3, 0); bx lr (case 0 at 0x110, case 1 at 0x112, case 2 at 0x114);
# bx lr (default, 0x116). Worst case: 1 + 1 + 1 + 2 + 1 + 3 + 3 = 12 cycles.
SWITCH = [0x2802, 0xD808, 0x4478, 0x7900, 0x0040, 0x4487, 0x0201, 0x0003,
          0x4770, 0x4770, 0x4770, 0x4770]
TARGETS = [0x110, 0x112, 0x114]
# the same with `bls 0x106` over `b 0x118` (the default), the jump at 0x10c, the cases at 0x112,
# 0x114, 0x116 (Clang's form when the default is out of reach of a conditional branch)
LS = [0x2802, 0xD900, 0xE008, 0x4478, 0x7900, 0x0040, 0x4487, 0x0201, 0x0003,
      0x4770, 0x4770, 0x4770, 0x4770]
LS_TARGETS = [0x112, 0x114, 0x116]
# no CMP: `movs r1, #3; ands r0, r1` bounds the index (Clang's form for `switch (x & 3)`):
# add r0,pc; ldrb r0,[r0,#4]; lsls r0,r0,#1; add pc,r0; table (bytes 1, 2, 3, 4); bx lr at
# 0x110, 0x112, 0x114, 0x116. Worst case: 1 + 1 + 1 + 2 + 1 + 3 + 3 = 12 cycles.
MASK = [0x2103, 0x4008, 0x4478, 0x7900, 0x0040, 0x4487, 0x0201, 0x0403,
        0x4770, 0x4770, 0x4770, 0x4770]
MASK_TARGETS = [0x110, 0x112, 0x114, 0x116]


# no instruction bounds the index, the certified invariant does (Lean `jumpInv`): at 0x100
# cmp r0,#0; beq 0x108; movs r1,#1; b 0x10a; movs r1,#0 (constants on two paths); add r1,pc;
# ldrb r1,[r1,#4]; lsls r1,r1,#1; add pc,r1; table (bytes 0, 1); bx lr at 0x114; movs r0,#5;
# bx lr at 0x116. Worst case 17 cycles.
PATH = [0x2800, 0xD001, 0x2101, 0xE000, 0x2100, 0x4479, 0x7909, 0x0049, 0x448F, 0x0100,
        0x4770, 0x2005, 0x4770]
PATH_TARGETS = [0x114, 0x116]
# a loop on the index: movs r2,#0; lsls r3,r2,#2; adr r1,0x10c; ldr r3,[r1,r3]; mov pc,r3;
# nop; table of addresses 0x115, 0x117; b 0x118 (case 0); movs r0,#7 (case 1); adds r2,#1;
# cmp r2,#2; bne 0x102; bx lr: r3 in 0..4 and a multiple of 4 at 0x106 (Lean `shlCong`)
LOOPSW = [0x2200, 0x0093, 0xA101, 0x58CB, 0x469F, 0x46C0, 0x0115, 0x0000, 0x0117, 0x0000,
          0xE000, 0x2007, 0x3201, 0x2A02, 0xD1F1, 0x4770]
LOOPSW_TARGETS = [0x114, 0x116]


def image(hws):
    mem = bytearray(0x200)
    struct.pack_into(f"<{len(hws)}H", mem, 0x100, *hws)
    return SimpleNamespace(mem=mem, funcs={"f": (0x100, 2 * len(hws))}, undefined={}, base=0, stack_top=0x1F0)


def certify(hws):
    an = wcet.Analysis(image(hws), {}, {})
    return ipet.certify(an, ["f"], mul=32, loops=True)


def check(doc):
    with tempfile.TemporaryDirectory() as d:
        p = pathlib.Path(d) / "c.json"
        p.write_text(json.dumps(doc))
        out = subprocess.run([CHECKER, str(p)], capture_output=True, text=True)
        return out.returncode, out.stdout + out.stderr


def run_from(img, r0):
    """The address the jump goes to, on m0.py, from the entry with r0."""
    class Jumped(Exception):
        pass
    mach = m0.Machine(img)
    seen = []

    def hook(i, _before, nxt):
        if i.kind == "indirect":
            seen.append(nxt)
            raise Jumped()
    mach.on_insn = hook
    try:
        mach.call("f", (r0,), max_cycles=1000)
    except Jumped:
        return seen[0]
    return None


class Producer(unittest.TestCase):
    def test_window_and_targets(self):
        get = jumptable.getter(image(SWITCH))
        self.assertEqual(jumptable.find(get, 0x10A), (0x100, TARGETS, None))

    def test_certificate(self):
        doc, bounds, why = certify(SWITCH)
        self.assertEqual(why, {})
        self.assertEqual(bounds["f"], 12)
        f = doc["programs"][0]["functions"][0]
        self.assertEqual(f["jumps"], [dict(start=0x100, pos=0x10A, targets=TARGETS)])

    def test_mask_form(self):
        # the closest bounding instruction, `ldrb` (255), would leave the function: the
        # `ands` with the mask known from `movs` is taken, the window from the `movs`
        get = jumptable.getter(image(MASK))
        self.assertEqual(jumptable.find(get, 0x10A, within=(0x100, 0x118)), (0x100, MASK_TARGETS, 0x102))
        doc, bounds, why = certify(MASK)
        self.assertEqual(why, {})
        self.assertEqual(bounds["f"], 12)
        self.assertEqual(doc["programs"][0]["functions"][0]["jumps"],
                         [dict(start=0x100, pos=0x10A, targets=MASK_TARGETS, index=0x102)])
        img = image(MASK)
        for r0 in (0, 1, 2, 3, 4, 7, 0xFFFFFFFF, 0x12345678):
            self.assertEqual(run_from(img, r0), MASK_TARGETS[r0 & 3])

    def test_bls_form(self):
        self.assertEqual(jumptable.find(jumptable.getter(image(LS)), 0x10C), (0x100, LS_TARGETS, None))
        doc, bounds, why = certify(LS)
        self.assertEqual(why, {})
        self.assertEqual(bounds["f"], 14)
        img = image(LS)
        for r0 in range(3):
            self.assertEqual(run_from(img, r0), LS_TARGETS[r0])

    def test_no_range_check_no_targets(self):
        # cmp r0,#2 replaced by movs r1,#2: no window from a CMP; the `ldrb` bounds the
        # index by 255, whose targets leave the function; the index is the argument r0, which
        # no invariant bounds: the jump is refused
        hws = list(SWITCH)
        hws[0] = 0x2102
        self.assertIsNone(jumptable.find(jumptable.getter(image(hws)), 0x10A, within=(0x100, 0x118)))
        _doc, _bounds, why = certify(hws)
        self.assertIn("not bounded by the loop analysis", why["f"])

    def test_invariant_paths(self):
        doc, bounds, why = certify(PATH)
        self.assertEqual(why, {})
        self.assertEqual(bounds["f"], 17)
        self.assertEqual(doc["programs"][0]["functions"][0]["jumps"],
                         [dict(start=0x10A, pos=0x110, targets=PATH_TARGETS, index=0x10A, bound=[1, 0, 1])])
        img = image(PATH)
        for r0 in (0, 1, 5, 0xFFFFFFFF):
            self.assertEqual(run_from(img, r0), PATH_TARGETS[0 if r0 == 0 else 1])

    def test_invariant_loop(self):
        doc, bounds, why = certify(LOOPSW)
        self.assertEqual(why, {})
        f = doc["programs"][0]["functions"][0]
        self.assertEqual(f["jumps"], [dict(start=0x104, pos=0x108, targets=LOOPSW_TARGETS, index=0x106,
                                           bound=[3, 0, 4])])
        self.assertEqual(len(f["loops"]), 1)
        mach = m0.Machine(image(LOOPSW))
        mach.call("f", (0,))
        self.assertLessEqual(mach.cyc, bounds["f"])

    def test_m0_follows_the_targets(self):
        img = image(SWITCH)
        for r0 in range(3):
            self.assertEqual(run_from(img, r0), TARGETS[r0])


class Checker(unittest.TestCase):
    def setUp(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        self.doc = certify(SWITCH)[0]

    def f(self, d):
        return d["programs"][0]["functions"][0]

    def assertRejected(self, doc):
        code, out = check(doc)
        self.assertEqual(code, 1, out)
        self.assertIn("PROGRAM  program: REJECTED", out)

    def altered(self, change):
        d = copy.deepcopy(self.doc)
        change(d)
        return d

    def test_accepted(self):
        code, out = check(self.doc)
        self.assertEqual(code, 0, out)
        self.assertIn("ACCEPTED f: at most 12 cycles", out)
        self.assertIn("1 jumps through tables, their targets checked on the code", out)

    def test_bls_accepted_and_target_dropped(self):
        doc = certify(LS)[0]
        code, out = check(doc)
        self.assertEqual(code, 0, out)
        self.assertIn("ACCEPTED f: at most 14 cycles", out)
        doc["programs"][0]["functions"][0]["jumps"][0]["targets"].pop(1)
        self.assertRejected(doc)

    def test_target_dropped(self):
        self.assertRejected(self.altered(lambda d: self.f(d)["jumps"][0]["targets"].pop()))

    def test_window_moved(self):
        def ch(d):
            self.f(d)["jumps"][0]["start"] = 0x102
        self.assertRejected(self.altered(ch))

    def test_range_widened(self):
        # cmp r0,#3: index 3 reads the byte 0, the jump can go to 0x10e (not a target)
        def ch(d):
            d["code"]["halfwords"][0x100 // 2] = 0x2803
        self.assertRejected(self.altered(ch))

    def test_branch_into_the_window(self):
        # bhi to 0x108 (the shift): with r0 > 2 the jump leaves the function on m0.py; the
        # producer still lists the window's targets, the checker refuses (`interiorOk`)
        hws = list(SWITCH)
        hws[1] = 0xD801
        img = image(hws)
        self.assertNotIn(run_from(img, 7), TARGETS + [0x116])
        doc = certify(hws)[0]
        self.assertRejected(doc)

    def test_mask_accepted_and_mutations(self):
        doc = certify(MASK)[0]
        code, out = check(doc)
        self.assertEqual(code, 0, out)
        self.assertIn("ACCEPTED f: at most 12 cycles", out)

        def mutated(change):
            d = copy.deepcopy(doc)
            change(d)
            return d
        # a target dropped
        self.assertRejected(mutated(lambda d: self.f(d)["jumps"][0]["targets"].pop()))
        # the mask widened to 7 in the code: indices 4..7 read the code after the table
        self.assertRejected(mutated(lambda d: d["code"]["halfwords"].__setitem__(0x100 // 2, 0x2107)))
        # the bound at an instruction that bounds nothing (`movs`)
        self.assertRejected(mutated(lambda d: self.f(d)["jumps"][0].__setitem__("index", 0x100)))
        # the window started after the `movs`: the mask is unknown
        self.assertRejected(mutated(lambda d: self.f(d)["jumps"][0].__setitem__("start", 0x102)))
        # the CMP form claimed for the same window (no `index`)
        self.assertRejected(mutated(lambda d: self.f(d)["jumps"][0].pop("index")))

    def test_invariant_accepted_and_mutations(self):
        doc = certify(PATH)[0]
        code, out = check(doc)
        self.assertEqual(code, 0, out)
        self.assertIn("ACCEPTED f: at most 17 cycles", out)

        def mutated(change):
            d = copy.deepcopy(doc)
            change(d)
            return d
        jt = lambda d: self.f(d)["jumps"][0]  # noqa: E731
        # the bound widened: index 2 reads the byte after the table
        self.assertRejected(mutated(lambda d: jt(d).__setitem__("bound", [1, 0, 2])))
        # a lower bound the invariant does not state
        self.assertRejected(mutated(lambda d: jt(d).__setitem__("bound", [1, 1, 1])))
        # no bound: the instruction at the index bounds nothing (`add r1, pc`)
        self.assertRejected(mutated(lambda d: jt(d).pop("bound")))
        # a target dropped
        self.assertRejected(mutated(lambda d: jt(d)["targets"].pop()))
        # a path sets r1 to 2: the invariant r1 <= 1 is no longer proved
        self.assertRejected(mutated(lambda d: d["code"]["halfwords"].__setitem__(0x104 // 2, 0x2102)))

    def test_invariant_loop_accepted_and_congruence(self):
        doc = certify(LOOPSW)[0]
        code, out = check(doc)
        self.assertEqual(code, 0, out)
        self.assertIn("1 loop rows certified", out)
        # without the congruence of r3 at the bounding instruction, the indices 1..3 read
        # unaligned words: the window cannot be evaluated
        f = self.f(doc)
        k = f["nodes"].index(0x106)
        self.assertIn([3, 2, 0], f["cong"][k])
        d = copy.deepcopy(doc)
        self.f(d)["cong"][k] = [x for x in self.f(d)["cong"][k] if x[0] != 3]
        self.assertRejected(d)

    def test_convention_with_jumps(self):
        # with `abi`, the calling convention is checked on the code of a function with a jump
        # (Lean `ThumbConv.convAll`, along `transJ`)
        an = wcet.Analysis(image(SWITCH), {}, {})
        doc = ipet.certify(an, ["f"], mul=32, loops=True, abi=True)[0]
        code, out = check(doc)
        self.assertEqual(code, 0, out)
        self.assertIn("checked on the code of every function", out)

    def test_convention_clobber_through_the_table(self):
        # case 0 branches to `movs r4, #1; bx lr`, reached only through the table: r4 is
        # written and not saved, the convention is not established (the bounds still hold
        # with the assumption)
        hws = list(SWITCH)
        hws[8] = 0xE002                    # b 0x118
        hws += [0x2401, 0x4770]            # movs r4, #1; bx lr
        an = wcet.Analysis(image(hws), {}, {})
        doc = ipet.certify(an, ["f"], mul=32, loops=True, abi=True)[0]
        code, out = check(doc)
        self.assertEqual(code, 0, out)
        self.assertIn("not established on the code of 1 function(s): f", out)

    def test_jumps_need_the_data_check(self):
        # the format without loop certificates does not allow jumps (`checkBinary` without `jt`):
        # the checker takes the data path when a function lists jumps; here the list is moved
        # to an unrelated address, so the graph has a stop instruction without its jump
        def ch(d):
            self.f(d)["jumps"][0]["pos"] = 0x108
        self.assertRejected(self.altered(ch))


class Exact(unittest.TestCase):
    """`xop`/`xres` and `pcWrite`/`pcDestV` of Lean against m0.py."""

    def test_against_m0(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        rnd = random.Random(3)
        BASE = 0x1000
        DATA = 0x1400                     # a table of random halfwords in the code
        insns = []
        for d in range(8):
            insns.append(0x4478 | (d & 7) | ((d >> 3) << 7))        # add rd, pc
            insns.append(0xA000 | (d << 8) | rnd.randrange(256))   # adr rd, #k
            insns.append(0x4680 | (0 << 3) | 7)                    # mov pc, r0 (reported only)
        for _ in range(60):
            t, n, m = rnd.randrange(8), rnd.randrange(8), rnd.randrange(8)
            insns.append(0x6800 | (rnd.randrange(32) << 6) | (n << 3) | t)   # ldr imm
            insns.append(0x8800 | (rnd.randrange(32) << 6) | (n << 3) | t)   # ldrh imm
            insns.append(0x7800 | (rnd.randrange(32) << 6) | (n << 3) | t)   # ldrb imm
            insns.append(0x5800 | (m << 6) | (n << 3) | t)                   # ldr reg
            insns.append(0x5A00 | (m << 6) | (n << 3) | t)                   # ldrh reg
            insns.append(0x5C00 | (m << 6) | (n << 3) | t)                   # ldrb reg
        insns += [0x4487 | (m << 3) for m in range(8)]                         # add pc, rm
        rng = []                         # the bounds of `rngOps`
        for _ in range(40):
            d, m = rnd.randrange(8), rnd.randrange(8)
            rng.append(0x4000 | (m << 3) | d)                                  # ands rd, rm
            rng.append(0x0800 | (rnd.randrange(32) << 6) | (m << 3) | d)      # lsrs rd, rm, #s
            rng.append(0xB2C0 | (m << 3) | d)                                  # uxtb rd, rm
        insns += rng
        insns += [0x4687 | (m << 3) for m in range(8)]                         # mov pc, rm
        data = [rnd.randrange(1 << 16) for _ in range(512)]
        hws = insns + [0] * ((DATA - BASE) // 2 - len(insns)) + data
        mem = bytearray(BASE) + bytearray(struct.pack(f"<{len(hws)}H", *hws))
        img = SimpleNamespace(mem=mem, funcs={}, undefined={}, base=0, stack_top=0x800)
        cases = []
        for k in range(len(insns)):
            a = BASE + 2 * k
            for _ in range(4):
                # registers pointing into the table (aligned for the loads to be defined),
                # small offsets for the register forms
                r = [DATA + 4 * rnd.randrange(100) if rnd.random() < 0.6 else 4 * rnd.randrange(64)
                     for _ in range(8)]
                cases.append((a, r))
        with tempfile.TemporaryDirectory() as dd:
            p = pathlib.Path(dd) / "eff.json"
            p.write_text(json.dumps(dict(code=dict(base=0, halfwords=list(struct.unpack(f"<{len(mem) // 2}H", mem))),
                                         abi=False, cases=[dict(a=a, r=r, f=[0, 0, 0, 0]) for a, r in cases])))
            out = subprocess.run([CHECKER, "--effect", str(p)], capture_output=True, text=True, check=True).stdout
        lines = [line.split() for line in out.splitlines()]
        compared = 0
        for (a, r), line in zip(cases, lines):
            xs, pcs = line[-3], line[-2]
            i = m0.decode(img.mem, a)
            mach = m0.Machine(img)
            mach.r[:8] = list(r)
            if pcs != "-":
                mach.execute(i, a)
                self.assertEqual(int(pcs[1:]), mach.r[15] & ~1 & 0xFFFFFFFF, (hex(a), r, line))
                compared += 1
                continue
            if xs == "-":
                continue
            dst, v = xs[1:].split(",")
            if v == "?":
                continue
            try:
                mach.execute(i, a)
            except (m0.Stop, struct.error, IndexError):
                self.fail(f"m0.py cannot execute {i} where Lean gives a value")
            self.assertEqual(int(v), mach.r[int(dst)] & 0xFFFFFFFF, (hex(a), str(i), r, line))
            compared += 1
        self.assertGreater(compared, 1000)
        # the bounds (`XOk`, `rngOps`): the register written is at most the bound, on m0.py
        bounded = 0
        for (a, r), line in zip(cases, lines):
            if line[-1] == "-":
                continue
            mach = m0.Machine(img)
            mach.r[:8] = list(r)
            try:
                mach.execute(m0.decode(img.mem, a), a)
            except (m0.Stop, struct.error, IndexError):
                continue
            for fact in line[-1].split(";"):
                d, b = fact[1:].split(",")
                self.assertLessEqual(mach.r[int(d)] & 0xFFFFFFFF, int(b), (hex(a), r, line[-1]))
                bounded += 1
        self.assertGreater(bounded, 200)


if __name__ == "__main__":
    if "--checker" in sys.argv:
        i = sys.argv.index("--checker")
        CHECKER = sys.argv[i + 1]
        del sys.argv[i:i + 2]
    unittest.main()
