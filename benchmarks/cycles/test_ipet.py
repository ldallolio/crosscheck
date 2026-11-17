#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Tests of the IPET cycle certificates (ipet.py) and of their check by crosscheck-check.

    python3 benchmarks/cycles/test_ipet.py [--checker formalization/.lake/build/bin/crosscheck-check]

A function with a loop of known worst case is certified (the bound must be exactly the
worst case); certificates altered in each part must be rejected by the checker (skipped if
the checker is not built).
"""
import copy
import json
import os
import pathlib
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


def insn(addr, kind, op, target=None, nregs=0, a=((),)):
    return SimpleNamespace(addr=addr, size=2, kind=kind, op=op, target=target, nregs=nregs, a=a)


class FakeAnalysis(wcet.Analysis):
    """A function `f` at 0x100: `x = ...; while (test) { body }` with the loop on line 5:
    B0 add | B1 cmp; bcond -> B3 | B2 add; b -> B1 | B3 pop {r4, pc}."""

    def __init__(self, bound, calls_g=False):
        img = SimpleNamespace(funcs={"f": (0x100, 14), "g": (0x200, 2)}, undefined={})
        super().__init__(img, {0x102: 5, 0x104: 5, 0x106: 5, 0x108: 5}, {5: bound})
        self.calls_g = calls_g

    def cfg(self, name):
        if name == "g":
            return 0x200, {0x200: [insn(0x200, "ret", "bx")]}, {0x200: []}
        b0 = [insn(0x100, "call", "bl", target=0x200)] if self.calls_g else [insn(0x100, "seq", "add")]
        blocks = {0x100: b0,
                  0x102: [insn(0x102, "seq", "cmp"), insn(0x104, "cond", "bcond", target=0x10a)],
                  0x106: [insn(0x106, "seq", "add"), insn(0x108, "jump", "b", target=0x102)],
                  0x10a: [insn(0x10a, "ret", "pop", nregs=2, a=((4, 15),))]}
        succ = {0x100: [0x102], 0x102: [0x10a, 0x106], 0x106: [0x102], 0x10a: []}
        return 0x100, blocks, succ


def check(doc):
    with tempfile.TemporaryDirectory() as d:
        p = pathlib.Path(d) / "c.json"
        p.write_text(json.dumps(doc))
        out = subprocess.run([CHECKER, str(p)], capture_output=True, text=True)
        return out.returncode, out.stdout + out.stderr


class Certify(unittest.TestCase):
    def test_loop_bound_is_the_worst_case(self):
        # 1 (add) + 10 * (cmp + bcond not taken = 2, add + b = 4) + (cmp + bcond taken = 4)
        # + pop {r4, pc} (4 + 2) = 71
        doc, bounds, why = ipet.certify(FakeAnalysis(10), ["f"])
        self.assertEqual(why, {})
        self.assertEqual(bounds["f"], 1 + 10 * 6 + 4 + 6)

    def test_no_loop_bound_no_certificate(self):
        doc, bounds, why = ipet.certify(FakeAnalysis(None), ["f"])
        self.assertNotIn("f", bounds)
        self.assertIn("without a bound", why["f"])

    def test_call_adds_the_callee_bound(self):
        doc, bounds, why = ipet.certify(FakeAnalysis(10, calls_g=True), ["f"])
        self.assertEqual(bounds["g"], 3)
        # bl (4) + g (3) instead of add (1)
        self.assertEqual(bounds["f"], 4 + 3 + 10 * 6 + 4 + 6)
        self.assertEqual(doc["programs"][0]["functions"][0]["name"], "g")

    def test_positive_cycle_has_no_potentials(self):
        edges = [(0, 1, 1, []), (1, 0, 1, []), (1, 2, 0, [])]
        self.assertIsNone(ipet.potentials([0, 1, 2], edges, 2, [1, 1, 0]))
        self.assertEqual(ipet.potentials([0, 1, 2], edges, 2, [1, -1, 0]), {0: 1, 1: 0, 2: 0})


class Checker(unittest.TestCase):
    def setUp(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        self.doc, self.bounds, _ = ipet.certify(FakeAnalysis(10, calls_g=True), ["f"])
        self.g, self.f = self.doc["programs"][0]["functions"]

    def assertRejected(self, doc, status=1):
        code, out = check(doc)
        self.assertEqual(code, status, out)
        if status == 1:
            self.assertIn("PROGRAM  program: REJECTED", out)

    def test_accepted(self):
        code, out = check(self.doc)
        self.assertEqual(code, 0, out)
        self.assertIn(f"ACCEPTED f: at most {self.bounds['f']} cycles", out)

    def test_bound_below_worst_case(self):
        d = copy.deepcopy(self.doc)
        d["programs"][0]["functions"][1]["certificate"]["bound"] -= 1
        self.assertRejected(d)

    def test_callee_bound_below_its_worst_case(self):
        d = copy.deepcopy(self.doc)
        d["programs"][0]["functions"][0]["certificate"]["bound"] -= 1
        d["programs"][0]["functions"][0]["certificate"]["pot"][0] -= 1
        self.assertRejected(d)

    def test_potential_changed(self):
        for k in range(len(self.f["certificate"]["pot"]) - 1):
            d = copy.deepcopy(self.doc)
            d["programs"][0]["functions"][1]["certificate"]["pot"][k] -= 1
            self.assertRejected(d)

    def test_multiplier_lowered(self):
        d = copy.deepcopy(self.doc)
        d["programs"][0]["functions"][1]["certificate"]["mult"][0] -= 1
        self.assertRejected(d)

    def test_loop_row_removed(self):
        d = copy.deepcopy(self.doc)
        d["programs"][0]["functions"][1]["rows"] = []
        self.assertRejected(d)

    def test_edge_weight_raised(self):
        d = copy.deepcopy(self.doc)
        d["programs"][0]["functions"][1]["edges"][0]["w"] += 1
        self.assertRejected(d)

    def test_graph_is_trusted_a_dropped_call_is_accepted(self):
        # the graph is trusted: without the call it is cheaper, and the same certificate holds
        d = copy.deepcopy(self.doc)
        del d["programs"][0]["functions"][1]["edges"][0]["calls"]
        self.assertEqual(check(d)[0], 0)

    def test_unknown_callee(self):
        d = copy.deepcopy(self.doc)
        d["programs"][0]["functions"][1]["edges"][0]["calls"] = ["h"]
        self.assertRejected(d, status=2)

    def test_scale_zero(self):
        d = copy.deepcopy(self.doc)
        d["programs"][0]["functions"][1]["certificate"]["scale"] = 0
        self.assertRejected(d)


if __name__ == "__main__":
    if "--checker" in sys.argv:
        i = sys.argv.index("--checker")
        CHECKER = sys.argv[i + 1]
        del sys.argv[i:i + 2]
    unittest.main()
