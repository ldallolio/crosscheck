#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Self-test of the Cortex-M0 interpreter (m0.py): the functions of selftest.c (with the
division run-time of runtime.c) are compiled for the Cortex-M0 at -O0 and -O1 and run on
many inputs; their results are compared with the C semantics, computed here. Before that,
the timing function `m0.cycles` is compared, row by row, with the instruction summary of
the Arm Cortex-M0 Technical Reference Manual (`TIMING` below)."""
import pathlib
import random
import shutil
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import m0  # noqa: E402

CLANG = (shutil.which("clang") or shutil.which("clang-18")
         or str(pathlib.Path.home() / "miniforge3/envs/crosscheck/bin/clang"))
M = 0xFFFFFFFF


def s32(x):
    return m0.sx(x, 32)


def cdiv(a, b):
    q = abs(a) // abs(b) * (1 if (a >= 0) == (b >= 0) else -1)
    return q, a - q * b


def lim32(x):
    return s32(x & M)


SPEC = {
    "t_asr": (2, lambda a, b: s32(a) >> (b & 31)),
    "t_lsr": (2, lambda a, b: a >> (b & 31)),
    "t_lsl": (2, lambda a, b: (a << (b & 31)) & M),
    "t_mul": (2, lambda a, b: lim32(s32(a) * s32(b))),
    "t_lt": (2, lambda a, b: int(s32(a) < s32(b))),
    "t_le": (2, lambda a, b: int(s32(a) <= s32(b))),
    "t_ult": (2, lambda a, b: int(a < b)),
    "t_ugt": (2, lambda a, b: int(a > b)),
    "t_sxtb": (1, lambda a: m0.sx(a, 8)),
    "t_sxth": (1, lambda a: m0.sx(a, 16)),
    "t_uxtb": (1, lambda a: a & 0xFF),
    "t_rev": (1, lambda a: int.from_bytes(a.to_bytes(4, "little"), "big")),
    "t_asr3": (1, lambda a: s32(a) >> 13),
    "t_neg": (1, lambda a: lim32(-s32(a))),
    "t_bic": (2, lambda a, b: s32(a & ~b & M)),
    "t_div": (2, lambda a, b: lim32(cdiv(s32(a), s32(b))[0]) if b else 0),
    "t_mod": (2, lambda a, b: lim32(cdiv(s32(a), s32(b))[1]) if b else 0),
    "t_udiv": (2, lambda a, b: a // b if b else 0),
}


def t_loop(n):
    s = 0
    for i in range(n & 63):
        s = lim32(s + i * i - (s >> 2))
    return s


def t_fft(l, k, p0, p1):
    l, k, p0, p1 = map(s32, (l, k, p0, p1))
    tmpr = lim32(lim32(l * p0) - lim32(k * p1))
    tmpi = lim32(lim32(l * p1) + lim32(k * p0))
    tmpr >>= 13
    tmpi >>= 13
    return s32((tmpr ^ (tmpi << 3)) & M)


def t_bitrev(seed):
    seed = s32(seed)
    buf = [lim32(seed + 7 * i) for i in range(64)]
    j, n = 0, 64
    for i in range(0, n - 1, 2):
        if j > i:
            buf[i], buf[j] = buf[j], buf[i]
            buf[i + 1], buf[j + 1] = buf[j + 1], buf[i + 1]
        m = 32
        while m >= 2 and j >= m:
            j -= m
            m >>= 1
        j += m
    s = 0
    for x in buf:
        s = lim32(s * 31 + x)
    return s


# Table 3-1 ("Cortex-M0 instruction summary") of the Arm Cortex-M0 Technical Reference
# Manual, revision r0p0 (Arm DDI 0432C), one encoding per row: (assembler, encoding,
# cycles). "mul" stands for `MUL_CYCLES` (1 or 32, note a of the table); a conditional
# branch is (taken, not taken) = (3, 1) (note d); N is the number of registers, the PC
# included for POP with PC (notes b and c).
TIMING = [
    ("movs r1, #5", 0x2105, 1), ("movs r0, r1", 0x0008, 1), ("mov r0, r1", 0x4608, 1),
    ("mov pc, r0", 0x4687, 3),
    ("adds r0, r1, #1", 0x1C48, 1), ("adds r0, r1, r2", 0x1888, 1), ("add r0, r1", 0x4408, 1),
    ("add pc, r0", 0x4487, 3), ("adds r0, #1", 0x3001, 1), ("adcs r0, r1", 0x4148, 1),
    ("add sp, #4", 0xB001, 1), ("add r0, sp, #4", 0xA801, 1), ("adr r0, .+8", 0xA001, 1),
    ("subs r0, r1, r2", 0x1A88, 1), ("subs r0, r1, #1", 0x1E48, 1), ("subs r0, #1", 0x3801, 1),
    ("sbcs r0, r1", 0x4188, 1), ("sub sp, #4", 0xB081, 1), ("rsbs r0, r1, #0", 0x4248, 1),
    ("muls r0, r1", 0x4348, "mul"),
    ("cmp r0, r1", 0x4288, 1), ("cmn r0, r1", 0x42C8, 1), ("cmp r0, #5", 0x2805, 1),
    ("ands r0, r1", 0x4008, 1), ("eors r0, r1", 0x4048, 1), ("orrs r0, r1", 0x4308, 1),
    ("bics r0, r1", 0x4388, 1), ("mvns r0, r1", 0x43C8, 1), ("tst r0, r1", 0x4208, 1),
    ("lsls r0, r1, #1", 0x0048, 1), ("lsls r0, r1", 0x4088, 1), ("lsrs r0, r1, #1", 0x0848, 1),
    ("lsrs r0, r1", 0x40C8, 1), ("asrs r0, r1, #1", 0x1048, 1), ("asrs r0, r1", 0x4108, 1),
    ("rors r0, r1", 0x41C8, 1),
    ("ldr r0, [r1]", 0x6808, 2), ("ldrh r0, [r1]", 0x8808, 2), ("ldrb r0, [r1]", 0x7808, 2),
    ("ldr r0, [r1, r2]", 0x5888, 2), ("ldrh r0, [r1, r2]", 0x5A88, 2),
    ("ldrsh r0, [r1, r2]", 0x5E88, 2), ("ldrb r0, [r1, r2]", 0x5C88, 2),
    ("ldrsb r0, [r1, r2]", 0x5688, 2), ("ldr r0, [pc, #0]", 0x4800, 2),
    ("ldr r0, [sp, #0]", 0x9800, 2),
    ("ldm r1!, {r2, r3}", 0xC90C, 3), ("ldm r0, {r0, r1, r2}", 0xC807, 4),
    ("str r0, [r1]", 0x6008, 2), ("strh r0, [r1]", 0x8008, 2), ("strb r0, [r1]", 0x7008, 2),
    ("str r0, [r1, r2]", 0x5088, 2), ("strh r0, [r1, r2]", 0x5288, 2),
    ("strb r0, [r1, r2]", 0x5488, 2), ("str r0, [sp, #0]", 0x9000, 2),
    ("stm r1!, {r2, r3}", 0xC10C, 3),
    ("push {r4, r5}", 0xB430, 3), ("push {r4, lr}", 0xB510, 3),
    ("pop {r4, r5}", 0xBC30, 3), ("pop {r4, pc}", 0xBD10, 6), ("pop {pc}", 0xBD00, 5),
    ("beq .", 0xD0FE, (3, 1)), ("b .", 0xE7FE, 3), ("bx lr", 0x4770, 3), ("blx r0", 0x4780, 3),
    ("sxth r0, r1", 0xB208, 1), ("sxtb r0, r1", 0xB248, 1), ("uxth r0, r1", 0xB288, 1),
    ("uxtb r0, r1", 0xB2C8, 1),
    ("rev r0, r1", 0xBA08, 1), ("rev16 r0, r1", 0xBA48, 1), ("revsh r0, r1", 0xBAC8, 1),
    ("nop", 0xBF00, 1), ("yield", 0xBF10, 1), ("sev", 0xBF40, 1),
]
# Rows without a cycle count that a bound could use (SVC and BKPT: "depends on core and
# debug configuration"; WFE, WFI: plus the time spent waiting), and those that are not
# decoded (CPS, and the 32-bit MRS, MSR, ISB, DMB, DSB: 4 cycles each): the decoder must
# stop on them, so that a function containing one gets no bound.
NO_BOUND = [("svc 0", 0xDF00), ("bkpt 0", 0xBE00), ("wfe", 0xBF20), ("wfi", 0xBF30),
            ("cpsid i", 0xB672), ("cpsie i", 0xB662)]
NO_BOUND32 = [("mrs r0, primask", 0xF3EF, 0x8010), ("msr primask, r0", 0xF380, 0x8810),
              ("isb", 0xF3BF, 0x8F6F), ("dmb", 0xF3BF, 0x8F5F), ("dsb", 0xF3BF, 0x8F4F)]


def timing_table():
    """Compares `m0.cycles` with the manual's table; returns the number of mismatches."""
    import struct
    bad = 0
    for asm, enc, want in TIMING:
        i = m0.decode(struct.pack("<HH", enc, 0), 0)
        if want == "mul":
            got, want = m0.cycles(i), m0.MUL_CYCLES
            ok = got == want and want in (1, 32)
        elif isinstance(want, tuple):
            got = (m0.cycles(i, True), m0.cycles(i, False))
            ok = got == want
        else:
            got = m0.cycles(i)
            ok = got == want and m0.cycles(i, False) == want
        if i.kind == "stop" or not ok:
            print(f"timing: {asm}: expected {want}, got {got} ({i!r}, {i.kind})", file=sys.stderr)
            bad += 1
    i = m0.decode(struct.pack("<HH", 0xF000, 0xF800), 0)  # bl .+4
    if i.kind != "call" or m0.cycles(i) != 4:
        print(f"timing: bl: expected 4, got {m0.cycles(i)}", file=sys.stderr)
        bad += 1
    for asm, enc in NO_BOUND:
        i = m0.decode(struct.pack("<HH", enc, 0), 0)
        if i.kind != "stop":
            print(f"timing: {asm} must stop the decoder, got {i!r}", file=sys.stderr)
            bad += 1
    for asm, h1, h2 in NO_BOUND32:
        i = m0.decode(struct.pack("<HH", h1, h2), 0)
        if i.kind != "stop":
            print(f"timing: {asm} must stop the decoder, got {i!r}", file=sys.stderr)
            bad += 1
    print(f"timing table: {len(TIMING) + 1 + len(NO_BOUND) + len(NO_BOUND32)} rows, {bad} mismatch(es)")
    return bad


def main():
    if timing_table():
        sys.exit(1)
    work = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / ".work"
    work.mkdir(exist_ok=True)
    src = work / "selftest_all.c"
    src.write_text((HERE / "selftest.c").read_text() + (HERE / "runtime.c").read_text())
    rnd = random.Random(1)
    edge = [0, 1, 2, 31, 32, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFF8000, 0x1234, 13]
    vals = lambda: rnd.choice(edge) if rnd.random() < 0.3 else rnd.getrandbits(32)
    bad = 0
    for opt in ("-O0", "-O1"):
        obj = work / f"selftest{opt}.o"
        subprocess.run([CLANG, "--target=thumbv6m-none-eabi", "-mcpu=cortex-m0", "-mfloat-abi=soft", opt,
                        "-ffreestanding", "-fno-builtin", "-fno-unwind-tables", "-fno-asynchronous-unwind-tables",
                        "-w", "-c", str(src), "-o", str(obj)], check=True)
        img = m0.load(str(obj))
        for name, (arity, f) in list(SPEC.items()) + [("t_loop", (1, t_loop)), ("t_fft", (4, t_fft)), ("t_bitrev", (1, t_bitrev))]:
            for _ in range(300):
                args = [vals() for _ in range(arity)]
                if name == "t_fft":
                    args = [rnd.randrange(-8192, 8193) & M, rnd.randrange(-8192, 8193) & M,
                            rnd.randrange(-40000, 40000) & M, rnd.randrange(-40000, 40000) & M]
                got = m0.Machine(img).call(name, args)
                exp = f(*args) & M
                if got != exp:
                    bad += 1
                    if bad < 15:
                        print(f"{opt} {name}{tuple(hex(a) for a in args)}: got {got:#x}, expected {exp:#x}")
        for name, f in (("t_add64", lambda a, b: a + b), ("t_sub64", lambda a, b: a - b)):
            for _ in range(300):
                a, b = rnd.getrandbits(64), rnd.getrandbits(64)
                m = m0.Machine(img)
                m.call(name, [a & M, a >> 32, b & M, b >> 32])
                got = m.r[0] | (m.r[1] << 32)
                if got != f(a, b) & ((1 << 64) - 1):
                    bad += 1
                    if bad < 15:
                        print(f"{opt} {name}: got {got:#x}")
        for _ in range(300):
            a, b = vals(), vals()
            m = m0.Machine(img)
            m.call("t_mul64", [a, b])
            got = m.r[0] | (m.r[1] << 32)
            if got != (s32(a) * s32(b)) & ((1 << 64) - 1):
                bad += 1
                if bad < 15:
                    print(f"{opt} t_mul64({a:#x},{b:#x}): got {got:#x}")
    print("self-test:", "OK" if not bad else f"{bad} mismatches")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
