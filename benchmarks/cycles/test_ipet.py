#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Tests of the cycle certificates on machine code (ipet.py) and of their check by
crosscheck-check.

    python3 benchmarks/cycles/test_ipet.py [--checker formalization/.lake/build/bin/crosscheck-check]

Machine code with a loop of known worst case is certified (the bound must be exactly the
worst case); certificates altered in each part (code, instruction list, rows, potentials,
multipliers, bound, callees) must be rejected by the checker, which is skipped if not
built. Also a certificate of the graph format (`crosscheck-cycles`), accepted and rejected.
"""
import copy
import json
import os
import pathlib
import struct
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import ipet  # noqa: E402
import wcet  # noqa: E402

CHECKER = os.environ.get("CROSSCHECK_CHECKER",
                         str(HERE.parent.parent / "formalization/.lake/build/bin/crosscheck-check"))

# f at 0x100: movs r0,#0; cmp r0,#10; bge 0x10a; adds r0,#1; b 0x102; bx lr  (loop on line 5)
LOOP = {0x100: [0x2000, 0x280A, 0xDA01, 0x3001, 0xE7FB, 0x4770]}
# f at 0x100: bl g; cmp r0,#10; bge 0x10c; adds r0,#1; b 0x104; bx lr   g at 0x120: bx lr
CALL = {0x100: [0xF000, 0xF80E, 0x280A, 0xDA01, 0x3001, 0xE7FB, 0x4770], 0x120: [0x4770]}


def image(code, funcs):
    mem = bytearray(0x200)
    for a, hws in code.items():
        struct.pack_into(f"<{len(hws)}H", mem, a, *hws)
    return SimpleNamespace(mem=mem, funcs=funcs, undefined={}, base=0)


def analysis(code, funcs, lines, bound):
    return wcet.Analysis(image(code, funcs), {a: 5 for a in lines}, {5: bound})


def loop_doc(bound=10):
    return ipet.certify(analysis(LOOP, {"f": (0x100, 12)}, range(0x102, 0x10a, 2), bound), ["f"], mul=32)


def call_doc():
    return ipet.certify(analysis(CALL, {"f": (0x100, 14), "g": (0x120, 2)}, range(0x104, 0x10c, 2), 10),
                        ["f"], mul=32)


def check(doc):
    with tempfile.TemporaryDirectory() as d:
        p = pathlib.Path(d) / "c.json"
        p.write_text(json.dumps(doc))
        out = subprocess.run([CHECKER, str(p)], capture_output=True, text=True)
        return out.returncode, out.stdout + out.stderr


class Certify(unittest.TestCase):
    def test_loop_bound_is_the_worst_case(self):
        # movs 1 + 10 * (cmp 1 + bge not taken 1 + adds 1 + b 3) + cmp 1 + bge taken 3 + bx lr 3
        doc, bounds, why = loop_doc()
        self.assertEqual(why, {})
        self.assertEqual(bounds["f"], 1 + 10 * 6 + 4 + 3)
        self.assertEqual(doc["programs"][0]["functions"][0]["nodes"], list(range(0x100, 0x10c, 2)))

    def test_no_loop_bound_no_certificate(self):
        doc, bounds, why = loop_doc(None)
        self.assertNotIn("f", bounds)
        self.assertIn("without a bound", why["f"])

    def test_call_adds_the_callee_bound(self):
        doc, bounds, why = call_doc()
        self.assertEqual(bounds["g"], 3)
        self.assertEqual(bounds["f"], 4 + 3 + 10 * 6 + 4 + 3)    # bl (4) + g (3) instead of movs
        self.assertEqual([f["name"] for f in doc["programs"][0]["functions"]], ["g", "f"])

    def test_positive_cycle_has_no_potentials(self):
        edges = [(0, 1, 1, []), (1, 0, 1, []), (1, 2, 0, [])]
        self.assertIsNone(ipet.potentials([0, 1, 2], edges, 2, [1, 1, 0]))
        self.assertEqual(ipet.potentials([0, 1, 2], edges, 2, [1, -1, 0]), {0: 1, 1: 0, 2: 0})


class Checker(unittest.TestCase):
    def setUp(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        self.doc, self.bounds, _ = call_doc()

    def f(self, d):
        return d["programs"][0]["functions"][1]

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
        self.assertIn(f"ACCEPTED f: at most {self.bounds['f']} cycles", out)

    def test_bound_below_worst_case(self):
        self.assertRejected(self.altered(lambda d: self.f(d)["certificate"].update(bound=self.bounds["f"] - 1)))

    def test_callee_bound_below_its_worst_case(self):
        def ch(d):
            c = d["programs"][0]["functions"][0]["certificate"]
            c["bound"] -= 1
            c["pot"][0] -= 1
        self.assertRejected(self.altered(ch))

    def test_potential_changed(self):
        for k in range(len(self.f(self.doc)["certificate"]["pot"]) - 1):
            def ch(d, k=k):
                self.f(d)["certificate"]["pot"][k] -= 1
            self.assertRejected(self.altered(ch))

    def test_multiplier_lowered(self):
        def ch(d):
            self.f(d)["certificate"]["mult"][0] -= 1
        self.assertRejected(self.altered(ch))

    def test_loop_row_removed(self):
        self.assertRejected(self.altered(lambda d: self.f(d).update(rows=[])))

    def test_slower_instruction_in_the_code(self):
        # adds r0, #1 (1 cycle) replaced by muls r0, r1, r0 (32 cycles)
        def ch(d):
            hw = d["code"]["halfwords"]
            hw[hw.index(0x3001)] = 0x4348
        self.assertRejected(self.altered(ch))

    def test_indirect_branch_in_the_code(self):
        # b 0x104 replaced by bx r0: the graph cannot be built
        def ch(d):
            hw = d["code"]["halfwords"]
            hw[hw.index(0xE7FB)] = 0x4700
        self.assertRejected(self.altered(ch))

    def test_instruction_missing_from_the_list(self):
        self.assertRejected(self.altered(lambda d: self.f(d)["nodes"].pop(2)))

    def test_callee_missing(self):
        self.assertRejected(self.altered(lambda d: d["programs"][0]["functions"].pop(0)))

    def test_scale_zero(self):
        self.assertRejected(self.altered(lambda d: self.f(d)["certificate"].update(scale=0)))


class GraphFormat(unittest.TestCase):
    """The graph format: the graph is given, not built (Lean Cycles.program_sound)."""
    DOC = {"format": "crosscheck-cycles", "version": 1, "programs": [{"name": "p", "functions": [
        {"name": "f", "entry": 0, "exit": 3,
         "edges": [{"src": 0, "dst": 1, "w": 2}, {"src": 1, "dst": 2, "w": 1},
                   {"src": 2, "dst": 1, "w": 5}, {"src": 1, "dst": 3, "w": 3}],
         "rows": [{"coef": [[2, 1], [0, -10]], "rhs": 0}],
         "certificate": {"scale": 1, "pot": [65, 3, 2, 0], "mult": [6], "bound": 65}}]}]}

    def setUp(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")

    def test_accepted_and_tight(self):
        self.assertEqual(check(self.DOC)[0], 0)
        d = copy.deepcopy(self.DOC)
        d["programs"][0]["functions"][0]["certificate"].update(bound=64, pot=[64, 3, 2, 0])
        self.assertEqual(check(d)[0], 1)

    def test_unknown_callee(self):
        d = copy.deepcopy(self.DOC)
        d["programs"][0]["functions"][0]["edges"][0]["calls"] = ["h"]
        self.assertEqual(check(d)[0], 2)


if __name__ == "__main__":
    if "--checker" in sys.argv:
        i = sys.argv.index("--checker")
        CHECKER = sys.argv[i + 1]
        del sys.argv[i:i + 2]
    unittest.main()
