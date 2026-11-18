#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Tests of the loop certificates on machine code (binloops.py) and of their check by
crosscheck-check (`Thumb.checkData`, theorem `ThumbData.data_sound`).

    python3 benchmarks/cycles/test_binloops.py [--checker formalization/.lake/build/bin/crosscheck-check]

A counting loop is certified with no trusted row and the cycle bound of its worst case;
certificates altered in each part (bound, scale, potential, invariant, kind of flags,
multipliers, the code, the assumption on callees) must be rejected. The checker is skipped
if not built.
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
