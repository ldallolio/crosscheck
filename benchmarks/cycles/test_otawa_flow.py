#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Tests of otawa_flow.py without OTAWA: loops of a block graph, matching with source
lines, and the call graph with what makes a function unsupported (must be refused)."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import otawa_flow as o  # noqa: E402

DIS = """
08000000 <leaf>:
 8000000:      	movs	r0, #0x0
 8000002:      	bx	lr
 8000004:      	bmi	0x8000010 <caller+0x4> @ imm = #0x8
0800000c <caller>:
 800000c:      	push	{r7, lr}
 800000e:      	bl	0x8000000 <leaf>        @ imm = #-0x12
 8000012:      	b.w	0x8000000 <leaf>
 8000016:      	pop	{r7, pc}
08000018 <indirect>:
 8000018:      	blx	r3
 800001a:      	bx	lr
0800001c <table>:
 800001c:      	tbb	[pc, r0]
08000020 <into>:
 8000020:      	bne	0x800000e <caller+0x2>
08000024 <undef>:
 8000024:      	bl	0x8000028 <undef+0x4>   @ imm = #0x0
 8000028:      	bx	lr
0800002c <rec>:
 800002c:      	bl	0x800002c <rec>
 8000030:      	ldr	pc, [sp], #4
08000034 <user>:
 8000034:      	blx	0x8000018 <indirect>
"""
END = {"leaf": 0x8000004, "caller": 0x8000018, "indirect": 0x800001c, "table": 0x8000020,
       "into": 0x8000024, "undef": 0x800002c, "rec": 0x8000034, "user": 0x8000038}


class CallGraph(unittest.TestCase):
    def setUp(self):
        self.calls, self.bad = o.parse_calls(DIS, END)

    def test_calls_and_tail_calls(self):
        self.assertEqual(self.calls["caller"], {"leaf"})
        self.assertNotIn("caller", self.bad)
        self.assertNotIn("leaf", self.bad)   # the padding after `bx lr` is not its code

    def test_refused(self):
        for f in ("indirect", "table", "into", "undef", "rec"):
            self.assertIn(f, self.bad, f)
        self.assertEqual(self.calls["user"], {"indirect"})

    def test_reasons(self):
        r = lambda f: o.unsupported_reason(o.reachable(self.calls, f), self.bad, {}, self.calls)
        self.assertIsNone(r("caller"))
        self.assertIn("indirect", r("user"))
        self.calls["a"], self.calls["b"] = {"b"}, {"a"}
        self.assertIn("recursive", r("a"))
        self.calls["c"] = {"missing"}
        self.assertIn("no code", r("c"))


class Loops(unittest.TestCase):
    # entry 0 -> header 1 <-> body 2 (latch), 1 -> exit 3; a call (synthetic block 9) in 2
    BLOCKS = {0: (0x100, 0x104, [1]), 1: (0x106, 0x10a, [2, 3]), 2: (0x10c, 0x110, [9]),
              4: (0x114, 0x116, [1]), 3: (0x118, 0x11a, [])}

    def test_natural_loop_through_a_call(self):
        loops = o.natural_loops(self.BLOCKS)
        self.assertEqual(set(loops), {0x106})
        body, latches = loops[0x106]
        self.assertEqual(body, {1, 2, 4})
        self.assertEqual(latches, {4})

    def test_flow_fact_from_the_loop_lines(self):
        lines = {0x106: ("a.c", 3), 0x10c: ("a.c", 4), 0x116: ("a.c", 3)}
        ffx, missing = o.flow_facts({"f": (self.BLOCKS, {0x106})}, lines, {("a.c", 3): 9})
        self.assertIn('<loop label="f" offset="0x6" maxcount="10"/>', ffx)
        self.assertEqual(missing, {})

    def test_no_fact_without_a_bound_or_a_line(self):
        lines = {0x106: ("a.c", 3), 0x116: ("a.c", 3)}
        ffx, missing = o.flow_facts({"f": (self.BLOCKS, {0x106})}, lines, {("a.c", 3): None})
        self.assertNotIn("<loop ", ffx)
        self.assertIn("without a bound", missing["f"])
        ffx, missing = o.flow_facts({"f": (self.BLOCKS, {0x106})}, {}, {("a.c", 3): 9})
        self.assertIn("matches no source loop", missing["f"])

    def test_innermost_line_range(self):
        # the loop's code carries the line of an inner source loop (5, lines 5-6) and lines of
        # the outer one (3, lines 3-8): only the outer range holds them all (wcet.Analysis.match)
        lines = {0x106: ("a.c", 5), 0x10c: ("a.c", 7), 0x116: ("a.c", 3), 0x100: ("a.c", 1)}
        bounds, ends = {("a.c", 3): 9, ("a.c", 5): 2}, {("a.c", 3): 8, ("a.c", 5): 6}
        ffx, missing = o.flow_facts({"f": (self.BLOCKS, {0x106})}, lines, bounds, ends)
        self.assertIn('maxcount="10"', ffx)
        self.assertEqual(missing, {})

    def test_header_without_back_edge(self):
        _, missing = o.flow_facts({"f": (self.BLOCKS, {0x118})}, {}, {})
        self.assertIn("no back edge", missing["f"])


if __name__ == "__main__":
    unittest.main()
