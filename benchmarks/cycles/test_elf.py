#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Tests of `crosscheck-check --elf` (Lean `ImperativeOptimization.Elf`): the code of a
certificate on machine code checked against the ELF file it was made from.

    python3 benchmarks/cycles/test_elf.py [--checker formalization/.lake/build/bin/crosscheck-check]

The ELF files are written here, without a linker: an executable at the address of a
microcontroller's flash (0x08000000) with a loop, and a relocatable object with a call
through `R_ARM_THM_CALL` and literal words through `R_ARM_ABS32`, one of them to an undefined
symbol (a stub of `m0.load`). The certificates made by ipet.py from them must be accepted with
`--elf`; a byte of the code changed, a function symbol moved, a function renamed, another
file, an unsupported relocation and a non-Arm file must be refused. The checker is skipped if
not built.
"""
import json
import os
import pathlib
import struct
import subprocess
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import ipet  # noqa: E402
import m0  # noqa: E402
import wcet  # noqa: E402

CHECKER = os.environ.get("CROSSCHECK_CHECKER",
                         str(HERE.parent.parent / "formalization/.lake/build/bin/crosscheck-check"))

FLASH = 0x08000000
# f: movs r0,#0; cmp r0,#10; bge +2; adds r0,#1; b -10; bx lr  (10 iterations)
LOOP = [0x2000, 0x280A, 0xDA01, 0x3001, 0xE7FB, 0x4770]
# f: bl h; bx lr; h: bx lr; (pad); .word h; .word u   (u undefined)
REL_CODE = [0xF000, 0xF800, 0x4770, 0x4770, 0, 0, 0, 0]


def elf(etype, text, addr, syms, rels=(), machine=40):
    """A 32-bit little-endian Arm ELF file: section `.text` (at `addr`), a symbol table
    `syms` = [(name, value, size, info, shndx)], and for `rels` = [(offset, type, symbol
    index)] a section `.rel.text`."""
    strtab = b"\0" + b"".join(n.encode() + b"\0" for n, *_ in syms)
    offs, k = [], 1
    for n, *_ in syms:
        offs.append(k)
        k += len(n) + 1
    symtab = bytes(16) + b"".join(struct.pack("<IIIBBH", o, v, s, i, 0, x)
                                  for o, (_, v, s, i, x) in zip(offs, syms))
    rel = b"".join(struct.pack("<II", o, (y << 8) | t) for o, t, y in rels)
    names = [b"", b".text", b".symtab", b".strtab", b".shstrtab"] + ([b".rel.text"] if rels else [])
    shstr = b"\0".join(names) + b"\0"
    name_off = [shstr.index(n + b"\0") if n else 0 for n in names]
    body = [text, symtab, strtab, shstr] + ([rel] if rels else [])
    pos, data = 52, b""
    file_offs = []
    for b in body:
        pad = (-pos) % 4
        data += b"\0" * pad
        pos += pad
        file_offs.append(pos)
        data += b
        pos += len(b)
    pad = (-pos) % 4
    data += b"\0" * pad
    shoff = pos + pad
    sh = [bytes(40),
          struct.pack("<IIIIIIIIII", name_off[1], 1, 6, addr, file_offs[0], len(text), 0, 0, 4, 0),
          struct.pack("<IIIIIIIIII", name_off[2], 2, 0, 0, file_offs[1], len(symtab), 3, 1, 4, 16),
          struct.pack("<IIIIIIIIII", name_off[3], 3, 0, 0, file_offs[2], len(strtab), 0, 0, 1, 0),
          struct.pack("<IIIIIIIIII", name_off[4], 3, 0, 0, file_offs[3], len(shstr), 0, 0, 1, 0)]
    if rels:
        sh.append(struct.pack("<IIIIIIIIII", name_off[5], 9, 0, 0, file_offs[4], len(rel), 2, 1, 4, 8))
    head = (b"\x7fELF" + bytes([1, 1, 1]) + bytes(9)
            + struct.pack("<HHIIIIIHHHHHH", etype, machine, 1, addr, 0, shoff, 0x05000000, 52, 0, 0, 40, len(sh), 4))
    return head + data + b"".join(sh)


def exec_file():
    text = struct.pack(f"<{len(LOOP)}H", *LOOP)
    return elf(2, text, FLASH, [("f", FLASH | 1, len(text), 0x12, 1)])


def rel_file(rtype=2):
    text = struct.pack(f"<{len(REL_CODE)}H", *REL_CODE)
    syms = [("f", 1, 6, 0x12, 1), ("h", 7, 2, 0x12, 1), ("u", 0, 0, 0x10, 0)]
    return elf(1, text, 0, syms, [(0, 10, 2), (8, rtype, 2), (12, 2, 3)])


def certificate(path, loops):
    img = m0.load(str(path))
    an = wcet.Analysis(img, {}, {}, {})
    doc, bounds, why = ipet.certify(an, ["f"], mul=32, loops=loops, abi=True)
    return img, doc, bounds, why


def run(elf_path, doc):
    with tempfile.TemporaryDirectory() as d:
        p = pathlib.Path(d) / "c.json"
        p.write_text(json.dumps(doc))
        out = subprocess.run([CHECKER, "--elf", str(elf_path), str(p)], capture_output=True, text=True)
        return out.returncode, out.stdout + out.stderr


class Producer(unittest.TestCase):
    def test_loaders(self):
        """m0.load reads the files: the executable at its address, the object linked from 0
        with its relocations (the BL to h, the words of h and of u's stub)."""
        with tempfile.TemporaryDirectory() as d:
            e = pathlib.Path(d) / "x.elf"
            e.write_bytes(exec_file())
            img = m0.load(str(e))
            self.assertEqual((img.base, img.funcs["f"][0]), (FLASH, 0))
            r = pathlib.Path(d) / "x.o"
            r.write_bytes(rel_file())
            img = m0.load(str(r))
            self.assertEqual(img.funcs, {"f": (0, 6), "h": (6, 2)})
            self.assertEqual(struct.unpack_from("<HH", img.mem, 0), (0xF000, 0xF801))   # bl h
            self.assertEqual(struct.unpack_from("<I", img.mem, 8)[0], 7)               # h | 1
            self.assertEqual(struct.unpack_from("<I", img.mem, 12)[0], 16)             # u's stub

    def test_executable_loop_certified(self):
        """Loop certificates of an executable linked away from 0 carry its addresses
        (`ipet.rebase_loops`; before 2026-11-27 the checker rejected them)."""
        with tempfile.TemporaryDirectory() as d:
            e = pathlib.Path(d) / "x.elf"
            e.write_bytes(exec_file())
            _, doc, bounds, why = certificate(e, True)
            f = doc["programs"][0]["functions"][0]
            self.assertEqual(f["entry"], FLASH)
            self.assertEqual([l["header"] for l in f["loops"]], [FLASH + 2])
            # movs 1, 10 x (cmp 1, bge not taken 1, adds 1, b 3), cmp 1, bge taken 3, bx lr 3
            self.assertEqual(bounds["f"], 1 + 10 * 6 + 1 + 3 + 3)


class Checker(unittest.TestCase):
    def setUp(self):
        if not pathlib.Path(CHECKER).exists():
            self.skipTest("crosscheck-check not built")
        self.d = tempfile.TemporaryDirectory()
        self.dir = pathlib.Path(self.d.name)
        self.exe = self.dir / "x.elf"
        self.exe.write_bytes(exec_file())
        self.obj = self.dir / "x.o"
        self.obj.write_bytes(rel_file())

    def tearDown(self):
        self.d.cleanup()

    def test_accepted(self):
        for path, loops in ((self.exe, True), (self.obj, False)):
            doc = certificate(path, loops)[1]
            st, out = run(path, doc)
            self.assertEqual(st, 0, out)
            self.assertIn(f"the code and the function entries checked against {path}", out)

    def test_rejected(self):
        doc = certificate(self.exe, True)[1]
        # one byte of the code changed in the file (cmp r0, #10 -> cmp r0, #11)
        data = bytearray(exec_file())
        k = data.index(struct.pack("<H", 0x280A))
        data[k] = 0x0B
        bad = self.dir / "bad.elf"
        bad.write_bytes(bytes(data))
        st, out = run(bad, doc)
        self.assertEqual(st, 1, out)
        self.assertIn("the halfword at", out)
        # the function symbol moved
        bad.write_bytes(elf(2, struct.pack(f"<{len(LOOP)}H", *LOOP), FLASH, [("f", (FLASH + 2) | 1, 10, 0x12, 1)]))
        st, out = run(bad, doc)
        self.assertEqual(st, 1, out)
        self.assertIn("function f: entry", out)
        # the function renamed in the certificate
        renamed = json.loads(json.dumps(doc))
        renamed["programs"][0]["functions"][0]["name"] = "g"
        st, out = run(self.exe, renamed)
        self.assertEqual(st, 1, out)
        self.assertIn("no function symbol g", out)
        # another file: the object, whose code starts at 0
        st, out = run(self.obj, doc)
        self.assertEqual(st, 1, out)
        # the object with an unsupported relocation (R_ARM_REL32), and a non-Arm file
        bad.write_bytes(rel_file(rtype=3))
        st, out = run(bad, doc)
        self.assertEqual(st, 2, out)
        self.assertIn("unsupported relocation type 3", out)
        bad.write_bytes(elf(2, struct.pack(f"<{len(LOOP)}H", *LOOP), FLASH, [("f", FLASH | 1, 12, 0x12, 1)], machine=62))
        st, out = run(bad, doc)
        self.assertEqual(st, 2, out)
        self.assertIn("not an Arm ELF file", out)


if __name__ == "__main__":
    if "--checker" in sys.argv:
        i = sys.argv.index("--checker")
        CHECKER = sys.argv[i + 1]
        del sys.argv[i:i + 2]
    unittest.main()
