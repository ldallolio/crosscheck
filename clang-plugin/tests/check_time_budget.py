#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Time budgets after compilation: compiles tests/c/time_budget.c for a Cortex-M0, runs
the plugin (report) and scripts/crosscheck_link.py at 48 MHz; every ok_* function must
meet its budget and every no_* function must fail it. Then, if an LLVM linker is found
(ld.lld, or the rust-lld of a Rust toolchain), the same for a program of two files,
time_budget_lib.c and time_budget_main.c, linked into an executable at the addresses of a
microcontroller (two reports, one binary). With the Lean checker built and scipy, the
first file is also checked with certified cycle bounds (--certify).
Usage: check_time_budget.py TOOL CLANG INCLUDE [extra clang args...]"""
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
FLAGS = ["--target=thumbv6m-none-eabi", "-mcpu=cortex-m0", "-mfloat-abi=soft", "-O1", "-g",
         "-fno-unroll-loops", "-ffreestanding", "-fno-builtin", "-w", "-std=gnu99"]


def lld():
    found = shutil.which("ld.lld") or shutil.which("ld.lld-18")
    if found:
        return found
    rust = sorted(pathlib.Path.home().glob(".rustup/toolchains/*/lib/rustlib/*/bin/rust-lld"))
    return str(rust[0]) if rust else None


def check(rows, status, n):
    bad = [r["function"] for r in rows if (r["function"].startswith("ok_")) != (r["verdict"] == "ok")]
    if bad or status != 1 or len(rows) != n:
        sys.exit(f"unexpected verdicts: {bad}, status {status}, {len(rows)} functions")


def certified(src, rep, obj, d, rows):
    """The same with --certify: IPET bounds accepted by the verified checker, the same
    verdicts, at most the timing schema's bounds; skipped without the checker or scipy."""
    checker = HERE.parent.parent / "formalization/.lake/build/bin/crosscheck-check"
    try:
        import scipy  # noqa: F401
    except ImportError:
        print("no scipy: the certified bounds are not checked")
        return
    if not checker.exists():
        print("crosscheck-check not built: the certified bounds are not checked")
        return
    out, cert = d / "oc.json", d / "cycles.json"
    p = subprocess.run([sys.executable, str(HERE.parent / "scripts" / "crosscheck_link.py"),
                        "--report", str(rep), "--binary", str(obj), "--source", str(src), "--clock-mhz", "48",
                        "--certify", "--checker", str(checker), "--cycle-certificate", str(cert),
                        "--json", str(out)], capture_output=True, text=True)
    print(p.stdout, p.stderr)
    crows = json.loads(out.read_text())["functions"]
    check(crows, p.returncode, 3)
    schema = {r["function"]: r["cycles"] for r in rows}
    if not all(r["cycles"] is not None and r["cycles"] <= schema[r["function"]] for r in crows):
        sys.exit("a certified bound is missing or above the timing schema's bound")
    # a certificate claiming one cycle less must be rejected
    doc = json.loads(cert.read_text())
    doc["programs"][0]["functions"][-1]["certificate"]["bound"] -= 1
    cert.write_text(json.dumps(doc))
    if subprocess.run([str(checker), str(cert)], capture_output=True).returncode != 1:
        sys.exit("a certificate with a lower bound was not rejected")


def two_files(tool, clang, inc, extra, linker, d):
    srcs = [HERE / "c" / "time_budget_lib.c", HERE / "c" / "time_budget_main.c"]
    args, objs = [], []
    for s in srcs:
        rep, obj = d / (s.stem + ".json"), d / (s.stem + ".o")
        subprocess.run([tool, "--all", f"--report={rep}", str(s), "--", "-x", "c", f"-I{inc}", *extra],
                       capture_output=True, text=True)
        subprocess.run([clang, *FLAGS, f"-I{inc}", "-c", str(s), "-o", str(obj)], check=True)
        args += ["--report", str(rep), "--source", str(s)]
        objs.append(str(obj))
    elf, out = d / "prog.elf", d / "o2.json"
    subprocess.run([linker, *(["-flavor", "gnu"] if "rust-lld" in linker else []), "-e", "ok_frame",
                    "--Ttext=0x08000000", "--Tdata=0x20000000", "--Tbss=0x20001000", "-o", str(elf), *objs],
                   check=True)
    p = subprocess.run([sys.executable, str(HERE.parent / "scripts" / "crosscheck_link.py"), *args,
                        "--binary", str(elf), "--clock-mhz", "48", "--json", str(out)],
                       capture_output=True, text=True)
    print(p.stdout, p.stderr)
    rows = json.loads(out.read_text())["functions"]
    check(rows, p.returncode, 2)
    if not all(r["cycles"] for r in rows):
        sys.exit("no cycle bound across the two files")


def main():
    tool, clang, inc, *extra = sys.argv[1:]
    src = HERE / "c" / "time_budget.c"
    with tempfile.TemporaryDirectory() as d:
        d = pathlib.Path(d)
        rep, obj, out = d / "r.json", d / "t.o", d / "o.json"
        subprocess.run([tool, "--all", f"--report={rep}", str(src), "--", "-x", "c", f"-I{inc}", *extra],
                       capture_output=True, text=True)
        subprocess.run([clang, *FLAGS, f"-I{inc}", "-c", str(src), "-o", str(obj)], check=True)
        p = subprocess.run([sys.executable, str(HERE.parent / "scripts" / "crosscheck_link.py"),
                            "--report", str(rep), "--binary", str(obj), "--source", str(src),
                            "--clock-mhz", "48", "--json", str(out)], capture_output=True, text=True)
        print(p.stdout, p.stderr)
        rows = json.loads(out.read_text())["functions"]
        check(rows, p.returncode, 3)
        certified(src, rep, obj, d, rows)
        linker = lld()
        if linker:
            two_files(tool, clang, inc, extra, linker, d)
        else:
            print("no LLVM linker: the program of two files is not checked")
    print("time budgets: as expected")


if __name__ == "__main__":
    main()
