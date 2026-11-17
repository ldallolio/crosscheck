#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Time budgets after compilation: compiles tests/c/time_budget.c for a Cortex-M0, runs
the plugin (report) and scripts/crosscheck_link.py at 48 MHz; every ok_* function must
meet its budget and every no_* function must fail it.
Usage: check_time_budget.py TOOL CLANG INCLUDE [extra clang args...]"""
import json
import pathlib
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
FLAGS = ["--target=thumbv6m-none-eabi", "-mcpu=cortex-m0", "-mfloat-abi=soft", "-O1", "-g",
         "-fno-unroll-loops", "-ffreestanding", "-fno-builtin", "-w", "-std=gnu99"]


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
        bad = [r["function"] for r in rows
               if (r["function"].startswith("ok_")) != (r["verdict"] == "ok")]
        if bad or p.returncode != 1 or len(rows) != 3:
            sys.exit(f"unexpected verdicts: {bad}, status {p.returncode}, {len(rows)} functions")
    print("time budgets: as expected")


if __name__ == "__main__":
    main()
