#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Bound the functions of a Rust file: MIR -> C (mir2c.py) -> crosscheck-tool, and, with
--checker, check the certificates.

    python3 frontends/rust/crosscheck_rust.py file.rs [--out DIR] [--checker crosscheck-check] \
        [-- extra clang flags]
"""
import argparse
import json
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import mir2c  # noqa: E402


def main():
    argv = sys.argv[1:]
    extra = argv[argv.index("--") + 1:] if "--" in argv else []
    argv = argv[:argv.index("--")] if "--" in argv else argv
    ap = argparse.ArgumentParser()
    ap.add_argument("source")
    ap.add_argument("--out", default=".")
    ap.add_argument("--rustc", default="rustc")
    ap.add_argument("--tool", default=str(HERE.parent.parent / "clang-plugin/build/crosscheck-tool"))
    ap.add_argument("--checker")
    a = ap.parse_args(argv)
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    stem = pathlib.Path(a.source).stem
    mir, c = out / f"{stem}.mir", out / f"{stem}.c"
    subprocess.run([a.rustc, "--crate-type=lib", "--emit=mir", "-O", "-C", "overflow-checks=on",
                    "-C", "panic=abort", "-o", str(mir), a.source], check=True)
    code, report = mir2c.translate(mir.read_text())
    c.write_text(code)
    rep, cert = out / f"{stem}.report.json", out / f"{stem}.certificates.json"
    subprocess.run([a.tool, "--all", f"--report={rep}", f"--opt=certificates={cert}", "--opt=minic", str(c),
                    "--", "-x", "c", "-std=c99", *extra], capture_output=True, text=True)
    funs = {f["name"]: f for f in json.loads(rep.read_text())["functions"]}
    for name, why in report:
        if why:
            print(f"SKIP  {name}: not translated ({why})")
            continue
        f = funs.get(name)
        if f is None:
            continue
        b = f"{f['wcet']} units" if f["wcet"] is not None else "no bound"
        print(f"{'OK  ' if f['ok'] else 'FAIL'}  {name}: {b}; certificate: {f['certificate']}")
    if a.checker:
        print(subprocess.run([a.checker, str(cert)], capture_output=True, text=True).stdout, end="")
    print(f"(C translation: {c}; report: {rep})")


if __name__ == "__main__":
    main()
