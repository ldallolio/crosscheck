#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Tests of the loop certificates on machine code (binloops.py) and of their check by
crosscheck-check (`Thumb.checkData`, theorem `ThumbData.data_sound`).

    python3 benchmarks/cycles/test_binloops.py [--checker formalization/.lake/build/bin/crosscheck-check]

A counting loop is certified with no trusted row and the cycle bound of its worst case;
certificates altered in each part (bound, scale, potential, invariant, kind of flags,
multipliers, the code, the assumption on callees) must be rejected; loops whose counter is
set by a literal load, STM/LDM write-back, NEGS or MVNS are certified, and a change of the
value these produce is rejected. The checker is skipped if not built.
"""
import copy
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import binloops  # noqa: E402
import ipet  # noqa: E402
import test_ipet  # noqa: E402

CHECKER = os.environ.get("CROSSCHECK_CHECKER",
                         str(HERE.parent.parent / "formalization/.lake/build/bin/crosscheck-check"))

# f at 0x100: movs r4,#0; bl g; adds r4,#1; cmp r4,#10; blt 0x102; bx lr   g at 0x120: bx lr
# (the counter lives in r4 across the call: certified only if callees preserve r4)
CALLLOOP = {0x100: [0x2400, 0xF000, 0xF80D, 0x3401, 0x2C0A, 0xDBFA, 0x4770], 0x120: [0x4770]}
# the same function saving r4 as the calling convention requires: push {r4,lr}; movs r4,#0;
# L: bl g; adds r4,#1; cmp r4,#10; blt L; pop {r4,pc}   g at 0x120: bx lr
# (the checker establishes the convention on the code of both functions, Lean `ThumbConv`)
SAVELOOP = {0x100: [0xB510, 0x2400, 0xF000, 0xF80C, 0x3401, 0x2C0A, 0xDBFA, 0xBD10], 0x120: [0x4770]}
# f at 0x100: sub sp,#8; movs r0,#0; str r0,[sp,#4]; L: ldr r0,[sp,#4]; cmp r0,#10; bge out;
# adds r0,#1; str r0,[sp,#4]; b L; out: add sp,#8; bx lr   (the counter lives in a stack slot)
STACKLOOP = {0x100: [0xB082, 0x2000, 0x9001, 0x9801, 0x280A, 0xDA02, 0x3001, 0x9001, 0xE7F9, 0xB002, 0x4770]}
# the same with a call in the loop: certified only if callees preserve SP (abi) and do not
# write the caller's frame (frame)
CALLSTACK = {0x100: [0xB082, 0x2000, 0x9001, 0xF000, 0xF81B, 0x9801, 0x3001, 0x9001, 0x280A, 0xDBF8,
                     0xB002, 0x4770], 0x140: [0x4770]}
# the same behind the usual prologue with a frame pointer: push {r7,lr}; add r7,sp,#0;
# mov r8,r8 (replaced by the tests); ...; pop {r7,pc}   (g at 0x146)
FPSTACK = {0x100: [0xB580, 0xAF00, 0x46C0] + CALLSTACK[0x100][:-1] + [0xBD80], 0x146: [0x4770]}

# f at 0x100: movs r0,#0; L: adds r0,#4; cmp r0,#40; bne L; bx lr   (a counter stepped by 4
# that exits on equality: bounded only with the congruence r0 = 0 modulo 4)
STEPLOOP = {0x100: [0x2000, 0x3004, 0x2828, 0xD1FC, 0x4770]}
# f at 0x100: sub sp,#8; movs r1,#0; L: str r1,[sp,#4]; ldr r1,[r0]; ldr r1,[sp,#4];
# adds r1,#1; cmp r1,#10; bne L; add sp,#8; bx lr  (the counter goes from r1 to the frame
# and back: no potential with the same linear part at every instruction)
ROTLOOP = {0x100: [0xB082, 0x2100, 0x9101, 0x6801, 0x9901, 0x3101, 0x290A, 0xD1F9, 0xB002, 0x4770]}

# Exact effects (Lean `Thumb.effect`, 2026-11-19); each counter is set by the instruction
# under test, so the loop is certified only if its value is known:
# f at 0x100: ldr r0,[pc,#4]; L: subs r0,#1; bne L; bx lr; .word 10   (literal pool)
LITLOOP = {0x100: [0x4801, 0x3801, 0xD1FD, 0x4770, 0x000A, 0x0000]}
# f at 0x100: movs r0,#0; L: stm r0!,{r1}; cmp r0,#40; bne L; bx lr   (STM write-back)
STMLOOP = {0x100: [0x2000, 0xC002, 0x2828, 0xD1FC, 0x4770]}
# f at 0x100: movs r1,#0; L: stm r0!,{r1}; adds r1,#1; cmp r1,#10; blt L; bx lr
# (STM writes no register of its list: the counter r1 survives it)
STMKEEP = {0x100: [0x2100, 0xC002, 0x3101, 0x290A, 0xDBFB, 0x4770]}
# f at 0x100: movs r1,#10; negs r1,r1; negs r0,r1; L: subs r0,#1; bne L; bx lr  (r0 = 10)
NEGLOOP = {0x100: [0x210A, 0x4249, 0x4248, 0x3801, 0xD1FD, 0x4770]}
# the same with mvns twice: r1 = 2^32 - 11, r0 = 10
MVNLOOP = {0x100: [0x210A, 0x43C9, 0x43C8, 0x3801, 0xD1FD, 0x4770]}
# f at 0x100: movs r0,#5; lsls r1,r0,#1; L: subs r1,#1; bne L; bx lr  (LSLS: r1 = 10)
SHLLOOP = {0x100: [0x2005, 0x0041, 0x3901, 0xD1FD, 0x4770]}
# movs r3,#9; L: subs r3,r3,#1; adds r2,r3,#1; bcs out; b L; out: bx lr -- `for (i = 9; i >= 0; i--)`
# as Clang compiles it in the division routines: the exit tests the carry of r3 + 1, true only
# once r3 has wrapped to 2^32 - 1 (disjunctive invariant between the subtraction and the branch)
WRAPLOOP = {0x100: [0x2309, 0x1E5B, 0x1C5A, 0xD200, 0xE7FB, 0x4770]}
# movs r3,#15; mvns r3,r3; L: adds r3,#4; bne L; bx lr -- Clang's count from 2^32 - 16 up by 4 to
# zero: leaving needs the wrap-around disjunct and the rounding of the sum fact `r3 + 4 != 2^32`
# with the congruence r3 = 0 (mod 4) (Lean `tightenS`)
WRAPZERO = {0x100: [0x230F, 0x43DB, 0x3304, 0xD1FD, 0x4770]}
EXACT = {"lit": (LITLOOP, 12, 0x102), "stm": (STMLOOP, 10, 0x102), "keep": (STMKEEP, 12, 0x102),
         "neg": (NEGLOOP, 12, 0x106), "mvn": (MVNLOOP, 12, 0x106), "shl": (SHLLOOP, 10, 0x104),
         "wrap": (WRAPLOOP, 12, 0x102)}


def exact_doc(name):
    code, size, h = EXACT[name]
    an = test_ipet.analysis(code, {"f": (0x100, size)}, range(h, h + 4, 2), 10)
    st = {}
    doc, bounds, _ = ipet.certify(an, ["f"], mul=32, loops=True, stats=st)
    return doc, bounds, st


def loop_doc(**kw):
    an = test_ipet.analysis(test_ipet.LOOP, {"f": (0x100, 12)}, range(0x102, 0x10a, 2), 10)
    st = {}
    doc, bounds, why = ipet.certify(an, ["f"], mul=32, loops=True, stats=st, **kw)
    return doc, bounds, st


def callloop_doc(abi):
    an = test_ipet.analysis(CALLLOOP, {"f": (0x100, 14), "g": (0x120, 2)}, range(0x102, 0x10c, 2), 10)
    st = {}
    doc, bounds, why = ipet.certify(an, ["f"], mul=32, loops=True, abi=abi, stats=st)
    return doc, bounds, st


def stack_doc():
    an = test_ipet.analysis(STACKLOOP, {"f": (0x100, 22)}, range(0x106, 0x112, 2), 10)
    st = {}
    doc, bounds, _ = ipet.certify(an, ["f"], mul=32, loops=True, stats=st)
    return doc, bounds, st


def callstack_doc(abi, frame):
    an = test_ipet.analysis(CALLSTACK, {"f": (0x100, 24), "g": (0x140, 2)}, range(0x106, 0x114, 2), 10)
    st = {}
    doc, bounds, _ = ipet.certify(an, ["f"], mul=32, loops=True, abi=abi, frame=frame, stats=st)
    return doc, bounds, st


def fpstack_doc(change=None):
    code = copy.deepcopy(FPSTACK)
    if change:
        code[0x100][2] = change
    an = test_ipet.analysis(code, {"f": (0x100, 30), "g": (0x146, 2)}, range(0x10C, 0x11A, 2), 10)
    st = {}
    doc, bounds, _ = ipet.certify(an, ["f"], mul=32, loops=True, abi=True, frame=True, stats=st)
    return doc, bounds, st


def check(doc):
    with tempfile.TemporaryDirectory() as d:
        p = pathlib.Path(d) / "c.json"
        p.write_text(json.dumps(doc))
        out = subprocess.run([CHECKER, str(p)], capture_output=True, text=True)
        return out.returncode, out.stdout + out.stderr


class Producer(unittest.TestCase):
    def test_counting_loop_certified(self):
        doc, bounds, st = loop_doc()
        self.assertEqual(bounds["f"], 68)                      # the worst case, as with the source bound
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x102, 10)])
        f = doc["programs"][0]["functions"][0]
        self.assertEqual(f["rows"], [])                        # no trusted row
        self.assertEqual(doc["version"], 2)

    def test_mirror_matches_obligation_count(self):
        # the producer's proofs are in the checker's order: one per obligation
        doc, _, _ = loop_doc()
        f = doc["programs"][0]["functions"][0]
        self.assertGreater(len(f["proofs"]), 0)

    def test_call_needs_the_assumption(self):
        _, _, st = callloop_doc(abi=False)
        self.assertEqual(st["f"]["certified"], [])
        _, b, st = callloop_doc(abi=True)
        self.assertEqual([x[0] for x in st["f"]["certified"]], [0x102])

    def test_convention_checked(self):
        # with the assumption on callees, the checker establishes the calling convention on
        # the code (Lean `convAll`, `data_sound_conv`) or reports it as assumed
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        an = test_ipet.analysis(SAVELOOP, {"f": (0x100, 16), "g": (0x120, 2)}, range(0x104, 0x10E, 2), 10)
        st = {}
        doc, _, _ = ipet.certify(an, ["f"], mul=32, loops=True, abi=True, stats=st)
        self.assertEqual([x[0] for x in st["f"]["certified"]], [0x104])
        code, out = check(doc)
        self.assertEqual(code, 0, out)
        self.assertIn("checked on the code of every function", out)
        # f writes r4 without saving it: accepted, with the convention assumed and f named
        doc, _, _ = callloop_doc(abi=True)
        code, out = check(doc)
        self.assertEqual(code, 0, out)
        self.assertIn("not established on the code of 1 function(s): f", out)


def step_doc(code=STEPLOOP):
    an = test_ipet.analysis(code, {"f": (0x100, 10)}, range(0x102, 0x108, 2), 10)
    st = {}
    doc, bounds, _ = ipet.certify(an, ["f"], mul=32, loops=True, stats=st)
    return doc, bounds, st


def rot_doc(code=ROTLOOP):
    an = test_ipet.analysis(code, {"f": (0x100, 20)}, range(0x104, 0x110, 2), 10)
    st = {}
    doc, bounds, _ = ipet.certify(an, ["f"], mul=32, loops=True, stats=st)
    return doc, bounds, st


class PotentialsPerInstruction(unittest.TestCase):
    def test_needs_the_linear_program(self):
        try:
            binloops.LP = False
            _, b, st = rot_doc()
            self.assertEqual(st["f"]["certified"], [])
            self.assertEqual(b["f"], 125)                     # with the trusted source row
        finally:
            binloops.LP = True
        doc, b, st = rot_doc()
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x104, 9)])   # back edges
        self.assertEqual(b["f"], 114)
        f = doc["programs"][0]["functions"][0]
        self.assertEqual(f["rows"], [])
        pots = f["loops"][0]["pot"]
        self.assertGreater(len({tuple(map(tuple, p["sv"])) for p in pots}), 1)   # several linear parts

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        doc, _, _ = rot_doc()
        code, out = check(doc)
        self.assertEqual(code, 0, out)

        def rejected(change):
            d = copy.deepcopy(doc)
            change(d["programs"][0]["functions"][0]["loops"][0], d)
            code, out = check(d)
            self.assertEqual(code, 1, out)

        rejected(lambda lc, d: lc.update(bound=8))                              # one back edge too few
        rejected(lambda lc, d: lc["pot"].__setitem__(1, lc["pot"][0]))          # the header's potential everywhere
        rejected(lambda lc, d: lc["pot"][2].update(c=lc["pot"][2]["c"] - 1))    # a constant too small
        # the loop's own store removed (str r1,[sp,#4] -> mov r8,r8): the counter never advances
        rejected(lambda lc, d: d["code"]["halfwords"].__setitem__(0x104 // 2, 0x46C0))


class Congruence(unittest.TestCase):
    def test_needs_congruences(self):
        try:
            binloops.CONG = False
            _, b, st = step_doc()
            self.assertEqual(st["f"]["certified"], [])
        finally:
            binloops.CONG = True
        doc, b, st = step_doc()
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x102, 9)])   # back edges
        self.assertEqual(b["f"], 52)                          # the worst case: 10 iterations
        f = doc["programs"][0]["functions"][0]
        self.assertEqual(f["rows"], [])
        self.assertIn([0, 2, 0], f["cong"][1])                # r0 = 0 modulo 4 at the header

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        doc, _, _ = step_doc()
        code, out = check(doc)
        self.assertEqual(code, 0, out)

        def rejected(change):
            d = copy.deepcopy(doc)
            change(d["programs"][0]["functions"][0], d)
            code, out = check(d)
            self.assertEqual(code, 1, out)

        rejected(lambda f, d: f.update(cong=[]))                                 # no congruence
        rejected(lambda f, d: f["cong"][1].__setitem__(0, [0, 2, 2]))            # a wrong residue
        rejected(lambda f, d: f["cong"].__setitem__(0, [[0, 2, 0]]))             # one at the entry
        rejected(lambda f, d: f["cong"][1].append([1, 33, 0]))                   # exponent above 32
        rejected(lambda f, d: f["cong"][1].append([12, 1, 0]))                   # not a variable of a state
        # step 3 instead of 4: the counter never equals 40 before it wraps
        rejected(lambda f, d: d["code"]["halfwords"].__setitem__(0x102 // 2, 0x3003))


class Stack(unittest.TestCase):
    def test_counter_in_a_stack_slot(self):
        doc, bounds, st = stack_doc()
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x106, 10)])
        f = doc["programs"][0]["functions"][0]
        self.assertEqual(f["slots"], [4])
        self.assertEqual(f["sp"][0], 0)
        self.assertEqual(f["sp"][3], -8)

    def test_call_needs_both_assumptions(self):
        for abi, frame, ok in ((False, False, False), (True, False, False), (True, True, True)):
            _, _, st = callstack_doc(abi, frame)
            self.assertEqual(bool(st["f"]["certified"]), ok, (abi, frame))

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        doc, _, _ = stack_doc()
        code, out = check(doc)
        self.assertEqual(code, 0, out)
        self.assertIn("1 words of the frame tracked", out)

        def rejected(change):
            d = copy.deepcopy(doc)
            change(d["programs"][0]["functions"][0], d)
            code, out = check(d)
            self.assertEqual(code, 1, out)

        rejected(lambda f, d: f.update(slots=[8]))                       # another word of the frame
        rejected(lambda f, d: f["sp"].__setitem__(3, -4))                 # a wrong offset of SP
        rejected(lambda f, d: f["sp"].__setitem__(0, -8))                 # the entry is not at offset 0
        # the store of the incremented counter goes to another word: the loop no longer ends
        rejected(lambda f, d: d["code"]["halfwords"].__setitem__(0x10E // 2, 0x9002))

    def test_frame_assumption(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        doc, _, st = callstack_doc(True, True)
        self.assertEqual(check(doc)[0], 0)
        d = copy.deepcopy(doc)
        for f in d["programs"][0]["functions"]:
            f["frame"] = False
        self.assertEqual(check(d)[0], 1)
        # an address of the frame in a register (add r1, sp, #0) forbids the assumption
        d = copy.deepcopy(doc)
        d["code"]["halfwords"][0x102 // 2] = 0xA900
        self.assertEqual(check(d)[0], 1)


class FramePointer(unittest.TestCase):
    """`add r7, sp, #imm` puts an address of the frame in r7: the assumption `frame` may still
    be used if r7 is read only as the base address of loads (Lean `Thumb.frameUseOk`)."""

    def test_producer(self):
        _, _, st = fpstack_doc()
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x10C, 9)])
        _, _, st = fpstack_doc(0x6839)          # ldr r1, [r7, #0]: a load through r7
        self.assertTrue(st["f"]["certified"])
        for h in (0x4639, 0x6039, 0x1C39):      # mov r1, r7; str r1, [r7, #0]; adds r1, r7, #0
            _, _, st = fpstack_doc(h)
            self.assertFalse(st["f"]["certified"], hex(h))

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        # the replaced instruction takes 1 cycle (mov r8, r8) or 2 (ldr r1, [r7, #0]); each
        # replacement keeps the cycles, so that only the use of r7 can make the check fail
        for base, ok, bad in ((None, [0x46B0], [0x46B8, 0x44B8]),
                              (0x6839, [0x6031, 0x6839], [0x6039, 0x603F, 0xC701])):
            doc, _, _ = fpstack_doc(base)
            self.assertEqual(check(doc)[0], 0, check(doc)[1])
            # ok: mov r8, r6; str r1, [r6]; ldr r1, [r7]; bad: mov r8, r7; add r8, r7;
            # str r1, [r7]; str r7, [r7]; stm r7!, {r0}
            for h in ok + bad:
                d = copy.deepcopy(doc)
                d["code"]["halfwords"][0x104 // 2] = h
                self.assertEqual(check(d)[0], 0 if h in ok else 1, hex(h))
            d = copy.deepcopy(doc)
            for f in d["programs"][0]["functions"]:
                f["frame"] = False
            self.assertEqual(check(d)[0], 1)


class ExactEffects(unittest.TestCase):
    """Literal loads, STM/LDM write-back, NEGS, MVNS and LSLS have exact effects: the loops whose
    counter they set are certified, and a change of the value they produce is rejected."""

    def test_producer(self):
        for name, (_code, _size, h) in EXACT.items():
            doc, _, st = exact_doc(name)
            self.assertEqual([x[:2] for x in st["f"]["certified"]], [(h, 9)], name)
            self.assertEqual(doc["programs"][0]["functions"][0]["rows"], [], name)

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        # (program, halfword index, replacement with the same cycles, accepted?)
        cases = [
            ("lit", 4, 0x000B, False),      # the literal is 11: 11 iterations
            ("lit", 5, 0x0001, False),      # the literal is 2^16 + 10
            ("lit", 0, 0x48FF, False),      # a literal beyond the code: any value
            ("stm", 1, 0xC802, True),       # ldm r0!,{r1}: the base still advances by 4
            ("stm", 1, 0xC801, False),      # ldm r0!,{r0}: the base is loaded, any value
            ("keep", 1, 0xC802, False),     # ldm r0!,{r1}: the counter is loaded
            ("neg", 0, 0x210B, False),      # movs r1,#11: r0 = 11
            ("neg", 2, 0x4008, False),      # ands r0,r1: any value
            ("mvn", 0, 0x210B, False),      # r0 = 11
            ("mvn", 2, 0x4248, False),      # negs r0,r1: r0 = 11 (r1 = 2^32 - 11)
            ("shl", 1, 0x0081, False),      # lsls r1,r0,#2: r1 = 20
            ("shl", 0, 0x2006, False),      # movs r0,#6: r1 = 12
            ("shl", 1, 0x07C1, False),      # lsls r1,r0,#31: overflow, any value
            ("shl", 1, 0x0841, False),      # lsrs r1,r0,#1: any value
            ("shl", 1, 0x0001, False),      # lsls r1,r0,#0 (movs r1,r0): r1 = 5, odd
        ]
        docs = {name: exact_doc(name)[0] for name in EXACT}
        for name, doc in docs.items():
            self.assertEqual(check(doc)[0], 0, (name, check(doc)[1]))
        for name, k, h, ok in cases:
            d = copy.deepcopy(docs[name])
            d["code"]["halfwords"][0x100 // 2 + k] = h
            self.assertEqual(check(d)[0], 0 if ok else 1, (name, k, hex(h)))


# f at 0x100: L: lsrs r0,r0,#8; bne L; bx lr -- `while (x >>= 8)`, as in bitcount's table counts:
# at most 3 transitions back to the header for a 32-bit x, but no affine potential: certified
# with the potential floor(log2 psi), psi = r0 at the header, 256 r0 after the shift (Lean
# `potGoals`), from the exact effect of LSRS (r0 = floor(r0 / 2^8)) and its flags (Z)
LOGLOOP = {0x100: [0x0A00, 0xD1FD, 0x4770]}


def log_doc():
    an = test_ipet.analysis(LOGLOOP, {"f": (0x100, 6)}, range(0x100, 0x104, 2), 10)
    st = {}
    doc, bounds, _ = ipet.certify(an, ["f"], mul=32, loops=True, stats=st)
    return doc, bounds, st


class LogPotentials(unittest.TestCase):
    """A loop that shifts its counter right until zero gets a logarithmic potential; the
    checker rejects it when the shift is smaller, the shift goes left, the scale or the bound
    are changed, or the potential is read as affine."""

    def test_producer(self):
        doc, _, st = log_doc()
        lc = doc["programs"][0]["functions"][0]["loops"][0]
        self.assertTrue(lc.get("log"))
        self.assertEqual((lc["scale"], lc["bound"]), (8, 31))
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x100, 4)])
        self.assertEqual(doc["programs"][0]["functions"][0]["rows"], [])

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        doc = log_doc()[0]
        self.assertEqual(check(doc)[0], 0, check(doc)[1])
        lp = lambda d: d["programs"][0]["functions"][0]["loops"][0]  # noqa: E731
        for k, h in ((0, 0x0900),       # lsrs r0,r0,#4: halved 4 times per iteration only
                     (0, 0x0200),       # lsls r0,r0,#8: grows
                     (0, 0x1000)):      # asrs r0,r0,#0 (by 32): r0 = 0 or 2^32 - 1, never back
            d = copy.deepcopy(doc)
            d["code"]["halfwords"][0x100 // 2 + k] = h
            self.assertEqual(check(d)[0], 1, hex(h))
        for change in (lambda d: lp(d).update(bound=30), lambda d: lp(d).update(scale=9),
                       lambda d: lp(d).pop("log"), lambda d: lp(d)["pot"][0].update(c=-1)):
            d = copy.deepcopy(doc)
            change(d)
            self.assertEqual(check(d)[0], 1)


# i = j = 0; while (i < 100) { while (j <= 99 && a[j] != 0) j++; i++; }: the inner loop
# runs up to 100 times per entry, but up to 100 times in all, since j is never reset
AMLOOP = {0x100: [0x2100, 0x2200, 0x2964, 0xD208, 0x2A63, 0xD804, 0x5C83, 0x2B00, 0xD001, 0x3201,
                  0xE7F8, 0x3101, 0xE7F4, 0x4770]}


def am_doc(amort=True):
    an = test_ipet.analysis(AMLOOP, {"f": (0x100, 28)}, range(0x100, 0x11C, 2), 1000)
    st = {}
    saved, binloops.AMORT = binloops.AMORT, amort
    try:
        doc, bounds, _ = ipet.certify(an, ["f"], mul=32, loops=True, stats=st)
    finally:
        binloops.AMORT = saved
    return doc, bounds, st


class Amortised(unittest.TestCase):
    """A nest whose inner loop continues its counter: the amortised row bounds its back edges
    per entry of the outer loop (`outer`), so the function's bound is not the product; the
    checker rejects a smaller bound, another enclosing loop, a part of it left out, or the row
    read as an ordinary one."""

    def test_producer(self):
        doc, bounds, st = am_doc()
        loops = doc["programs"][0]["functions"][0]["loops"]
        am = [lc for lc in loops if "outer" in lc]
        self.assertEqual([(lc["header"], lc["outer"]["header"], lc["bound"] // lc["scale"]) for lc in am],
                         [(0x108, 0x104, 100)])
        self.assertEqual(sorted(x[:2] for x in st["f"]["certified"]), [(0x104, 100), (0x108, 100)])
        self.assertLess(bounds["f"], 3000)
        self.assertGreater(am_doc(False)[1]["f"], 100_000)

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        doc = am_doc()[0]
        self.assertEqual(check(doc)[0], 0, check(doc)[1])
        am = lambda d: next(lc for lc in d["programs"][0]["functions"][0]["loops"] if "outer" in lc)  # noqa: E731
        for name, change in (("bound", lambda d: am(d).update(bound=am(d)["scale"] * 99)),
                             ("outer header", lambda d: am(d)["outer"].update(header=0x108)),
                             ("outer body", lambda d: am(d)["outer"]["body"].remove(0x116)),
                             ("ordinary", lambda d: am(d).pop("outer"))):
            d = copy.deepcopy(doc)
            change(d)
            self.assertEqual(check(d)[0], 1, name)


# TACLeBench's binarysearch_binary_search as Clang compiles it for the Cortex-M0 (-O1), moved to
# 0x100: low = 0, up = 14; while (low <= up) { mid = (low + up) >> 1; if (data[mid].key == x)
# { up = low - 1; ... } else if (data[mid].key > x) up = mid - 1; else low = mid + 1; }. The
# range up - low + 1 halves at each pass: a logarithmic potential; `up = low - 1` wraps around
# when low = 0 and joins the other paths before the test, so the potentials differ between the
# disjuncts of the invariant there (`pot_alt`); found by the richer analysis (`rich`)
BSEARCH = {0x100: [0xB5F0, 0xAF03, 0xB081, 0x2200, 0x43D1, 0x9100, 0x240E, 0x4B0B, 0xE005, 0x1999,
                   0x6849, 0x9100, 0x1E54, 0x42A2, 0xDC0A, 0x1915, 0x106D, 0x00EE, 0x5999, 0x4281,
                   0xD0F3, 0xDD01, 0x1E6C, 0xE7F4, 0x1C6A, 0xE7F2, 0x9800, 0xB001, 0xBDF0, 0x46C0,
                   0x02EC, 0x0000]}


def bs_doc(rich=True):
    an = test_ipet.analysis(BSEARCH, {"f": (0x100, 60)}, range(0x112, 0x134, 2), 15)
    st = {}
    saved, binloops.RICH = binloops.RICH, rich
    try:
        doc, bounds, _ = ipet.certify(an, ["f"], mul=32, loops=True, stats=st, abi=True, frame=True)
    finally:
        binloops.RICH = saved
    return doc, bounds, st


class BinarySearch(unittest.TestCase):
    """Binary search: 3 back edges (four passes over 15 entries), certified with a logarithmic
    potential per disjunct of the invariant; the checker rejects a smaller bound, the
    potentials of the wrap-around disjuncts left out, and the potential read as affine."""

    def test_producer(self):
        doc, _, st = bs_doc()
        fn = doc["programs"][0]["functions"][0]
        lc = fn["loops"][0]
        self.assertTrue(lc.get("log"))
        self.assertTrue(any(lc.get("pot_alt", [])))
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x11E, 3)])
        self.assertEqual(fn["rows"], [])
        self.assertEqual(bs_doc(False)[2]["f"]["certified"], [])

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        doc = bs_doc()[0]
        self.assertEqual(check(doc)[0], 0, check(doc)[1])
        lp = lambda d: d["programs"][0]["functions"][0]["loops"][0]  # noqa: E731
        for name, change in (("bound", lambda d: lp(d).update(bound=lp(d)["scale"] * 2)),
                             ("pot_alt", lambda d: lp(d).pop("pot_alt")),
                             ("affine", lambda d: lp(d).pop("log"))):
            d = copy.deepcopy(doc)
            change(d)
            self.assertEqual(check(d)[0], 1, name)
        # the code: the halving replaced by a decrement of 1 (asrs r5, r5, #1 -> subs r5, r5, #1)
        d = copy.deepcopy(doc)
        d["code"]["halfwords"][0x100 // 2 + 16] = 0x1E6D
        self.assertEqual(check(d)[0], 1, "subs")


# A loop closed by a far branch: push {r4, lr}; movs r4, #3; L: subs r4, r4, #1; beq out; bl L
# (Clang's long branch where `B` cannot reach; here within reach, as a small test); out: pop
# {r4, pc}. The `BL` is a jump to its target inside the function, listed as such (`"far":
# true`, Lean `JT.far`), not a call; its effect in the data semantics is that of a call (r0-r3
# any; r4-r7 kept with `abi`), hence the counter in r4.
FARLOOP = {0x100: [0xB510, 0x2403, 0x1E64, 0xD001, 0xF7FF, 0xFFFC, 0xBD10]}


def far_doc():
    an = test_ipet.analysis(FARLOOP, {"f": (0x100, 14)}, range(0x104, 0x10C, 2), 3)
    st = {}
    doc, bounds, why = ipet.certify(an, ["f"], mul=32, loops=True, stats=st, abi=True)
    return doc, bounds, why, st


class FarBranches(unittest.TestCase):
    """A `BL` to an address inside its function is a branch: the function gets a cycle bound
    and its loop a certified bound; the checker rejects the certificate without the far
    branch listed (a call of no function), or when the link register, which the far branch
    writes, is read after the entry (`BX LR`, `MOV r0, LR`)."""

    def test_producer(self):
        doc, bounds, why, st = far_doc()
        self.assertEqual(why, {})
        fn = doc["programs"][0]["functions"][0]
        self.assertEqual(fn["jumps"], [dict(start=0x108, pos=0x108, targets=[], far=True)])
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x104, 2)])
        # push {r4, lr} 3 + movs 1 + 2 x (subs 1 + beq 1 + bl 4) + subs 1 + beq taken 3
        # + pop {r4, pc} 6
        self.assertEqual(bounds["f"], 3 + 1 + 2 * 6 + 1 + 3 + 6)

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        doc = far_doc()[0]
        self.assertEqual(check(doc)[0], 0, check(doc)[1])
        fn = lambda d: d["programs"][0]["functions"][0]  # noqa: E731
        d = copy.deepcopy(doc)
        del fn(d)["jumps"]
        self.assertEqual(check(d)[0], 1, "not listed")
        for k, h in ((6, 0x4770),      # the return as bx lr: would return after the bl
                     (2, 0x4670)):     # mov r0, lr in the loop
            d = copy.deepcopy(doc)
            d["code"]["halfwords"][0x100 // 2 + k] = h
            self.assertEqual(check(d)[0], 1, hex(h))


# Counters in the high registers, as GCC writes them for the Cortex-M0: movs r0, #0; mov r8,
# r0; movs r1, #10; mov r9, r1; L: movs r2, #1; add r8, r2; cmp r8, r9; bne L; bx lr (Lean
# `effect`: MOV, ADD and CMP on r0-r12, variables `rv`). HICALL: the same loop with a call
# in it (push {lr}; ...; L: bl g; ...; pop {pc}): r8 and r9 survive the call under the
# assumption on callees (the AAPCS: r4-r11), r12 does not.
HILOOP = {0x100: [0x2000, 0x4680, 0x210A, 0x4689, 0x2201, 0x4490, 0x45C8, 0xD1FB, 0x4770]}
HICALL = {0x100: [0xB500, 0x2000, 0x4680, 0x210A, 0x4689, 0xF000, 0xF809, 0x2201, 0x4490, 0x45C8,
                  0xD1F9, 0xBD00], 0x120: [0x4770]}


def hi_doc(code=HILOOP, call=False):
    if call:
        an = test_ipet.analysis(code, {"f": (0x100, 24), "g": (0x120, 2)}, range(0x10A, 0x116, 2), 10)
    else:
        an = test_ipet.analysis(code, {"f": (0x100, 18)}, range(0x108, 0x110, 2), 10)
    st = {}
    doc, bounds, why = ipet.certify(an, ["f"], mul=32, loops=True, stats=st, abi=True)
    return doc, bounds, st


class HighRegisters(unittest.TestCase):
    """Loop counters in r8-r12: certified, also across a call for r8-r11 (callees preserve
    them under the assumption); the checker rejects a smaller bound and the code changed to
    compare with a register that holds nothing known, and the producer certifies no loop
    whose counter is r12 across a call."""

    def test_producer(self):
        doc, bounds, st = hi_doc()
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x108, 9)])
        # 4 + 10 x (movs, add, cmp) + 9 x bne taken 3 + bne not taken 1 + bx lr 3
        self.assertEqual(bounds["f"], 4 + 30 + 27 + 1 + 3)
        self.assertEqual(doc["programs"][0]["functions"][0]["rows"], [])
        _, _, st = hi_doc(HICALL, True)
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x10A, 9)])
        r12 = {0x100: [0xB500, 0x2000, 0x4684, 0x210A, 0x4689, 0xF000, 0xF809, 0x2201, 0x4494, 0x45CC,
                       0xD1F9, 0xBD00], 0x120: [0x4770]}
        _, _, st = hi_doc(r12, True)
        self.assertEqual(st["f"]["certified"], [])

    def test_used_registers(self):
        """`hi_regs`: no register for `mov r8, r8` or for r12 made any value by a call (a
        column of no use changed the vertex HiGHS returned: mpeg2 7 -> 8); r12 counts once
        it is read."""
        eff = lambda h, abi=True: binloops.effect(abi, lambda a: h, 0)  # noqa: E731
        self.assertEqual(binloops.hi_regs(eff(0x46C0)), set())          # mov r8, r8
        self.assertEqual(binloops.hi_regs(eff(0xF000)), set())          # bl (first half)
        self.assertEqual(binloops.hi_regs(eff(0xF000, False)), set())
        self.assertEqual(binloops.hi_regs(eff(0x4680)), {8})            # mov r8, r0
        self.assertEqual(binloops.hi_regs(eff(0x4660)), {12})           # mov r0, r12
        self.assertEqual(binloops.hi_regs(eff(0x45CC)), {9, 12})        # cmp r12, r9

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        for code, call in ((HILOOP, False), (HICALL, True)):
            doc = hi_doc(code, call)[0]
            self.assertEqual(check(doc)[0], 0, check(doc)[1])
            fn = lambda d: next(f for f in d["programs"][0]["functions"] if f["name"] == "f")  # noqa: E731
            d = copy.deepcopy(doc)
            fn(d)["loops"][0]["bound"] -= 1
            self.assertEqual(check(d)[0], 1, "bound")
            k = 6 if not call else 9          # cmp r8, r9 -> cmp r8, r10
            d = copy.deepcopy(doc)
            d["code"]["halfwords"][0x100 // 2 + k] = 0x45D0
            self.assertEqual(check(d)[0], 1, "cmp r8, r10")
            d = copy.deepcopy(doc)
            d["code"]["halfwords"][0x100 // 2 + 3 + (1 if call else 0)] = 0x468A    # mov r10, r1
            self.assertEqual(check(d)[0], 1, "mov r10, r1")
        # the counter in r12, which a call may change: the certificate of r8 on that code
        doc = hi_doc(HICALL, True)[0]
        for k, h in ((2, 0x4684), (8, 0x4494), (9, 0x45CC)):
            doc["code"]["halfwords"][0x100 // 2 + k] = h
        self.assertEqual(check(doc)[0], 1, "r12 across a call")


class CongruencesExact(unittest.TestCase):
    """The congruences are those of the checker's effects, also in the producer's retry that
    gives shifts any value (`lit_any`): there N and Z of `lsls r2, r0, #3` were taken as those
    of 0, and the checker rejected the claimed `g1 = 0 mod 2^32` (TACLeBench's `matrix1`
    without frame pointers, both assumptions, 2026-11-26)."""

    def test_lit_any(self):
        # movs r0, #125; L: lsls r2, r0, #3; beq out; subs r0, #1; b L; out: bx lr
        code = {0x100: [0x207D, 0x00C2, 0xD001, 0x3801, 0xE7FB, 0x4770]}
        an = test_ipet.analysis(code, {"f": (0x100, 12)}, range(0x102, 0x10A, 2), 200)
        cs = []
        for lit_any in (False, True):
            ctx = binloops.Ctx(an, "f", True, True, lit_any)
            cs.append(binloops.congruences(ctx))
        self.assertEqual(cs[0], cs[1])
        self.assertNotIn(8, cs[1][0x104])


class Disjunctions(unittest.TestCase):
    """A counter that exits on its wrap-around: the invariant between the subtraction and the
    branch is a disjunction (no wrap-around, or the counter is 2^32 - 1); the certificate
    lists it (`alt`) with the disjunct each case lands in (`pick`)."""

    def test_producer(self):
        doc, _, st = exact_doc("wrap")
        fn = doc["programs"][0]["functions"][0]
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x102, 9)])
        self.assertTrue(any(fn["alt"]) and any(fn["pick"]))

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        doc = exact_doc("wrap")[0]
        self.assertEqual(check(doc)[0], 0, check(doc)[1])
        fn = lambda d: d["programs"][0]["functions"][0]  # noqa: E731
        # the code: one more iteration, a step of 2 (wraps to 2^32 - 2), the opposite exit
        for k, h in ((0, 0x230A), (1, 0x1E9B), (3, 0xD300)):
            d = copy.deepcopy(doc)
            d["code"]["halfwords"][0x100 // 2 + k] = h
            self.assertEqual(check(d)[0], 1, (k, hex(h)))
        # the certificate: no alternatives, no targets, a disjunct changed, a target changed
        d = copy.deepcopy(doc)
        del fn(d)["alt"]
        self.assertEqual(check(d)[0], 1, "alt removed")
        d = copy.deepcopy(doc)
        del fn(d)["pick"]
        self.assertEqual(check(d)[0], 1, "pick removed")
        d = copy.deepcopy(doc)
        changed = 0
        for disj in (x for alts in fn(d)["alt"] for x in alts):
            for g in disj:
                if g["sv"] == [[3, -1]]:        # r3 >= 2^32 - 1 becomes r3 >= 2^32 - 2
                    g["c"] -= 1
                    changed += 1
        self.assertGreater(changed, 0)
        self.assertEqual(check(d)[0], 1, "disjunct changed")
        d = copy.deepcopy(doc)
        k = next(i for i, x in enumerate(fn(d)["pick"]) if x)
        fn(d)["pick"][k][0][4] = 0
        self.assertEqual(check(d)[0], 1, "target changed")


def wrapzero_doc(code=WRAPZERO):
    an = test_ipet.analysis(code, {"f": (0x100, 10)}, range(0x104, 0x108, 2), 10)
    st = {}
    doc, bounds, _ = ipet.certify(an, ["f"], mul=32, loops=True, stats=st)
    return doc, bounds, st


class WrapToZero(unittest.TestCase):
    """A counter stepped by 4 from 2^32 - 16 that leaves when it wraps around to zero: the
    case of the wrap-around that continues the loop is excluded by rounding the fact on the
    sum of the flags' operands with their congruence (`tightenS`)."""

    def test_producer(self):
        doc, _, st = wrapzero_doc()
        self.assertEqual([x[:2] for x in st["f"]["certified"]], [(0x104, 3)])

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        doc = wrapzero_doc()[0]
        self.assertEqual(check(doc)[0], 0, check(doc)[1])
        fn = lambda d: d["programs"][0]["functions"][0]  # noqa: E731
        # from 2^32 - 15 the counter never reaches zero; a step of 3 breaks the congruence
        for k, h in ((0, 0x230E), (2, 0x3303)):
            d = copy.deepcopy(doc)
            d["code"]["halfwords"][0x100 // 2 + k] = h
            self.assertEqual(check(d)[0], 1, (k, hex(h)))
        d = copy.deepcopy(doc)
        fn(d)["cong"] = [[] for _ in fn(d)["cong"]]
        self.assertEqual(check(d)[0], 1, "congruences removed")


class LinearPrograms(unittest.TestCase):
    """`binloops.highs_lp` gives linprog's answers, and its CPU-time limit stops a solve
    that is then charged its full iteration limit."""

    def programs(self):
        import numpy as np
        from scipy.sparse import random as sprandom
        rnd = np.random.default_rng(3)
        for k in range(40):
            m, me, n = int(rnd.integers(1, 30)), int(rnd.integers(0, 6)), int(rnd.integers(2, 40))
            A = sprandom(m, n, density=0.3, random_state=k, format="csr") * 10 - \
                sprandom(m, n, density=0.2, random_state=k + 100, format="csr") * 10
            E = sprandom(me, n, density=0.4, random_state=k + 200, format="csr")
            b = rnd.uniform(-5, 20, m)
            beq = E @ rnd.uniform(0, 3, n)
            c = rnd.uniform(-1, 2, n)
            bounds = [(0, None) if j % 3 else (None if j % 2 else -4, 7) for j in range(n)]
            yield c, A, b, E, beq, bounds

    def test_same_answers_as_linprog(self):
        import numpy as np
        from scipy.optimize import linprog
        statuses = set()
        for c, A, b, E, beq, bounds in self.programs():
            for meth, solver in (("highs-ds", "simplex"), ("highs-ipm", "ipm"), ("highs", None)):
                for presolve in (True, False):
                    ref = linprog(c, A_ub=A, b_ub=b, A_eq=E, b_eq=beq, bounds=bounds, method=meth,
                                  options={"presolve": presolve, "maxiter": 500})
                    got = binloops.highs_lp(c, A, b, E, beq, bounds, solver, presolve, 500)
                    statuses.add(ref.status)
                    self.assertEqual((ref.status, ref.nit), (got.status, got.nit), meth)
                    if ref.status == 0:
                        self.assertTrue(np.array_equal(ref.x, got.x), meth)
        self.assertTrue({0, 2} <= statuses, statuses)     # optimal and infeasible ones

    def test_cpu_limit(self):
        c, A, b, E, beq, bounds = next(iter(self.programs()))
        saved = binloops.LP_SAFETY_CPU
        binloops.LP_SAFETY_CPU = -1.0       # every callback stops the solve
        try:
            res = binloops.highs_lp(c, A, b, E, beq, bounds, "simplex", False, 500)
        finally:
            binloops.LP_SAFETY_CPU = saved
        self.assertEqual((res.status, res.interrupted, res.x), (1, True, None))
        binloops._meter_reset()
        size = binloops.lp_size(A, E)
        binloops._meter_lp(res, 0.0, size)
        m = binloops.METER
        self.assertEqual((m["lp_safety"], m["lp_limited"], m["lp_iters"]), (1, 1, binloops.lp_maxiter(size)))
        binloops._meter_reset()


class ForgetGrowing(unittest.TestCase):
    """`forget_growing` (after HARD_VISITS widenings of a head): only the variables that
    cover the growing entries lose their constraints; the bounds of a stable counter stay
    (until 2026-11-25 a growing entry on the zero node's row dropped every upper bound, and
    7 copy loops of `powerwindow_main` were left uncertified)."""

    def test_pointer_forgotten_counter_kept(self):
        Zd = binloops.Zones(0)
        old = Zd.top()
        Z = Zd.Z
        # r2 in [1, 977]; r0 in [0, 1000], r0 - r2 <= 1000
        old[2][Z], old[Z][2] = 977, -1
        old[0][Z], old[0][2] = 1000, 1000
        old = Zd.close(old)
        new = [row[:] for row in old]
        new[0][Z] += 1          # the pointer creeps up
        new[0][2] += 1
        out = binloops.forget_growing(old, new)
        self.assertEqual(Zd.lohi(out, 2), (1, 977))
        self.assertEqual(out[0][Z], binloops.INF)
        self.assertEqual(out[0][2], binloops.INF)
        self.assertEqual(Zd.close([row[:] for row in out]), out)    # still closed
        self.assertTrue(all(out[i][j] >= old[i][j] for i in range(Zd.n) for j in range(Zd.n)))


# f at 0x100: push {lr}; movs r0, #10; bl g; pop {pc}
# g at 0x120: movs r1, #0; L: cmp r1, r0; bge out; adds r1, #1; b L; out: bx lr
CTXCALL = {0x100: [0xB500, 0x200A, 0xF000, 0xF80C, 0xBD00],
           0x120: [0x2100, 0x4281, 0xDA01, 0x3101, 0xE7FB, 0x4770]}


def ctx_doc(contexts=True, code=CTXCALL):
    an = test_ipet.analysis(code, {"f": (0x100, 10), "g": (0x120, 12)}, [], 10)
    st = {}
    doc, bounds, _ = ipet.certify(an, ["f"], mul=32, loops=True, abi=True, stats=st, contexts=contexts)
    return doc, bounds, st


class Contexts(unittest.TestCase):
    """Preconditions on the arguments (`--contexts`, Lean `DFun.pre`, `callObs`): `g` counts up
    to its argument `r0`, which its only caller sets to 10."""

    def fn(self, doc, name):
        return next(f for f in doc["programs"][0]["functions"] if f["name"] == name)

    def test_bound_from_the_call(self):
        _, b, st = ctx_doc(contexts=False)
        self.assertEqual(st["g"]["certified"][0][1], 4294967295)   # r0 unknown: up to 2^32 - 1
        doc, b, st = ctx_doc()
        self.assertEqual(st["g"]["certified"][0][1], 10)
        self.assertEqual((b["g"], b["f"]), (68, 80))
        self.assertEqual(self.fn(doc, "g")["pre"], [{"sv": [[0, 1]], "c": -10}, {"sv": [[0, -1]], "c": 10}])
        self.assertTrue(self.fn(doc, "f")["call_proofs"])

    def test_checker(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        doc, _, _ = ctx_doc()
        code, out = check(doc)
        self.assertEqual(code, 0, out)
        self.assertIn("1 function(s) with a precondition on their arguments", out)
        # must be rejected: the proofs at the call removed; a precondition that the call does
        # not establish (r0 <= 9, the caller passes 10); the precondition removed (the bound of
        # g needs it); the caller's argument changed in the code (movs r0, #20)
        bad = copy.deepcopy(doc)
        del self.fn(bad, "f")["call_proofs"]
        self.assertEqual(check(bad)[0], 1)
        bad = copy.deepcopy(doc)
        self.fn(bad, "g")["pre"][0]["c"] = -9
        self.assertEqual(check(bad)[0], 1)
        bad = copy.deepcopy(doc)
        del self.fn(bad, "g")["pre"]
        self.assertEqual(check(bad)[0], 1)
        bad = copy.deepcopy(doc)
        hw = bad["code"]["halfwords"]
        hw[0x102 // 2] = 0x2014
        self.assertEqual(check(bad)[0], 1)


class Checker(unittest.TestCase):
    def setUp(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        self.doc, self.bounds, _ = loop_doc()

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
        self.assertIn("1 loop rows certified on the machine code, 0 trusted", out)

    def test_bound_lowered(self):
        def ch(d):
            self.f(d)["loops"][0]["bound"] -= 1
        self.assertRejected(self.altered(ch))

    def test_scale_raised(self):
        def ch(d):
            self.f(d)["loops"][0]["scale"] += 1
        self.assertRejected(self.altered(ch))

    def test_potential_changed(self):
        def ch(d):
            self.f(d)["loops"][0]["pot"][0]["c"] -= 1
        self.assertRejected(self.altered(ch))

    def test_invariant_tightened(self):
        # r0 ≤ 10 at the header becomes r0 ≤ 9
        def ch(d):
            inv = self.f(d)["inv"][1]
            inv[0]["c"] += 1
        self.assertRejected(self.altered(ch))

    def test_kind_changed(self):
        def ch(d):
            k = self.f(d)["kinds"]
            k[2] = "add" if k[2] == "sub" else "sub"
        self.assertRejected(self.altered(ch))

    def test_multiplier_changed(self):
        def ch(d):
            for p in self.f(d)["proofs"]:
                if p[1]:
                    p[1][0][1] += 1
                    p[0] = 1
                    break
        d = self.altered(ch)
        # a changed multiplier may still prove the obligation; changing all of them may not
        for p in self.f(d)["proofs"]:
            p[1] = []
        self.assertRejected(d)

    def test_proof_missing(self):
        self.assertRejected(self.altered(lambda d: self.f(d)["proofs"].pop()))

    def test_counter_decremented_in_the_code(self):
        # adds r0, #1 becomes subs r0, #1: the loop no longer terminates
        def ch(d):
            hw = d["code"]["halfwords"]
            hw[hw.index(0x3001)] = 0x3801
        self.assertRejected(self.altered(ch))

    def test_limit_raised_in_the_code(self):
        # cmp r0, #10 becomes cmp r0, #20
        def ch(d):
            hw = d["code"]["halfwords"]
            hw[hw.index(0x280A)] = 0x2814
        self.assertRejected(self.altered(ch))

    def test_assumption_on_callees_removed(self):
        doc, _, st = callloop_doc(abi=True)
        self.assertEqual(check(doc)[0], 0)
        d = copy.deepcopy(doc)
        d["abi"] = False
        self.assertRejected(d)


if __name__ == "__main__":
    if "--checker" in sys.argv:
        i = sys.argv.index("--checker")
        CHECKER = sys.argv[i + 1]
        del sys.argv[i:i + 2]
    unittest.main()
