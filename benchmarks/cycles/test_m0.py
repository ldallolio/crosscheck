#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Self-test of the Cortex-M0 interpreter (m0.py): the functions of selftest.c (with the
division run-time of runtime.c) are compiled for the Cortex-M0 at -O0 and -O1 and run on
many inputs; their results are compared with the C semantics, computed here."""
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


def main():
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
