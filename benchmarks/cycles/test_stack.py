# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Tests of `stack.py`: the stack pointer restored from the frame pointer, registers kept
across calls only when the callee preserves them on its code, and the cases that must
get no bound. Each bound is also compared with a run on `m0.py`."""
import struct
import unittest
from types import SimpleNamespace

import m0
import stack

F, G = 0x100, 0x140


def bl(at, target):
    off = target - (at + 4)
    imm = off & ((1 << 25) - 1)
    s, i1, i2 = (imm >> 24) & 1, (imm >> 23) & 1, (imm >> 22) & 1
    j1, j2 = (1 - i1) ^ s, (1 - i2) ^ s
    return [0xF000 | (s << 10) | ((imm >> 12) & 0x3FF), 0xD000 | (j1 << 13) | (j2 << 11) | ((imm >> 1) & 0x7FF)]


def frame_fn(body=()):
    """push {r4-r7,lr}; add r7,sp,#12; sub sp,#16; <body>; bl g; subs r6,r7,#7; subs r6,#5;
    mov sp,r6; pop {r4-r7,pc}: the stack pointer restored from the frame pointer, as Clang
    does for frames reserved by `add sp, r`."""
    hws = [0xB5F0, 0xAF03, 0xB084] + list(body)
    hws += bl(F + 2 * len(hws), G)
    return hws + [0x1FFE, 0x3E05, 0x46B5, 0xBDF0]


SAVES_R7 = [0xB580, 0x2700, 0xBD80]     # push {r7,lr}; movs r7,#0; pop {r7,pc}
CLOBBERS_R7 = [0x2700, 0x4770]          # movs r7,#0; bx lr
LEAVES_R7 = [0x2000, 0x4770]            # movs r0,#0; bx lr


def image(f, g):
    mem = bytearray(0x400)
    struct.pack_into(f"<{len(f)}H", mem, F, *f)
    struct.pack_into(f"<{len(g)}H", mem, G, *g)
    return SimpleNamespace(mem=mem, funcs={"f": (F, 2 * len(f)), "g": (G, 2 * len(g))},
                           undefined={}, base=0, stack_top=0x3F0)


def observed(img):
    """Largest depth of the stack pointer below its entry value in a run of f."""
    mach = m0.Machine(img)
    low = []

    def hook(_i, _before, _nxt):
        low.append(mach.r[13])
    mach.on_insn = hook
    mach.call("f", (0,), max_cycles=1000)
    return img.stack_top - min(low), mach.r[13]


class FramePointer(unittest.TestCase):
    def bound(self, f, g):
        sa = stack.StackAnalysis(image(f, g))
        return sa.function("f"), sa.why.get("f")

    def test_restored_from_frame_pointer(self):
        for g, gstack in ((SAVES_R7, 8), (LEAVES_R7, 0)):
            b, why = self.bound(frame_fn(), g)
            self.assertEqual(b, 36 + gstack, why)
            obs, sp = observed(image(frame_fn(), g))
            self.assertEqual(sp, image(frame_fn(), g).stack_top)  # returned with SP restored
            self.assertLessEqual(obs, b)

    def test_callee_clobbers_frame_pointer(self):
        b, why = self.bound(frame_fn(), CLOBBERS_R7)
        self.assertIsNone(b)
        self.assertIn("writes the stack pointer", why)

    def test_frame_pointer_changed(self):
        # adds r7,#4 before the call: r6 is then the entry SP minus 16, the pop leaves 4
        # bytes: refused (no single depth at the return)
        b, why = self.bound(frame_fn([0x3704]), SAVES_R7)
        self.assertIsNone(b)

    def test_frame_pointer_overwritten(self):
        # movs r7,#0 before the call: unknown, refused
        b, why = self.bound(frame_fn([0x2700]), SAVES_R7)
        self.assertIsNone(b)
        self.assertIn("writes the stack pointer", why)

    def test_join_of_different_values(self):
        # cmp r0,#0; beq +0; adds r7,#4 (fall-through only) ... two values reach the join
        b, why = self.bound(frame_fn([0x2800, 0xD000, 0x3704]), SAVES_R7)
        self.assertIsNone(b)
        self.assertIn("writes the stack pointer", why)


if __name__ == "__main__":
    unittest.main()
