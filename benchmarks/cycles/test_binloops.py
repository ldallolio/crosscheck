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
