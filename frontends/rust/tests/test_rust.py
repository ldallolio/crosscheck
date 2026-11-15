#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Tests of the Rust front-end.

    python3 frontends/rust/tests/test_rust.py [--tool crosscheck-tool] [--checker crosscheck-check]

1. Differential test of the translation: every translated function of
   `examples/kernels.rs` (except `rejected_*`, which may not terminate) is run on the
   same inputs as Rust (with overflow checks; panics caught) and as the generated C
   (compiled by the host's cc); the results, and the contents of `&mut` slices, must
   agree whenever Rust does not panic.
2. Analysis: every `rejected_*` function must have no bound; the functions of `EXPECTED`
   must be bounded; with --checker, every certificate must be accepted.
"""
import argparse
import json
import pathlib
import random
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
FRONT = HERE.parent
sys.path.insert(0, str(FRONT))
import mir2c  # noqa: E402

EXPECTED = {"fir", "sat_sum", "bubble", "steps_down", "table", "twice"}
RANGE = {"i8": (-2**7, 2**7 - 1), "i16": (-2**15, 2**15 - 1), "i32": (-2**31, 2**31 - 1),
         "i64": (-2**63, 2**63 - 1), "isize": (-2**63, 2**63 - 1), "u8": (0, 255), "u16": (0, 2**16 - 1),
         "u32": (0, 2**32 - 1), "u64": (0, 2**64 - 1), "usize": (0, 2**64 - 1), "bool": (0, 1)}


def value(rnd, ty):
    lo, hi = RANGE[ty]
    pool = [v for v in (0, 1, 2, 3, 5, 7, 10, 31, 100, 255, 999, 1000, 7000, 10000, -1, -7, -100, lo, hi)
            if lo <= v <= hi]
    return rnd.choice(pool) if rnd.random() < 0.5 else rnd.randint(max(lo, -3000), min(hi, 12000))


def rust_lit(v, ty):
    if ty == "bool":
        return "true" if v else "false"
    return f"{v}{ty}" if v >= 0 else f"({v}{ty})"


def c_lit(v, ty):
    if ty in ("i64", "isize") and v == -2**63:
        return "INT64_MIN"
    return f"(({mir2c.INT[ty]}){v}{'ull' if ty in ('u64', 'usize') else 'll'})"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tool", default=str(FRONT.parent.parent / "clang-plugin/build/crosscheck-tool"))
    ap.add_argument("--checker")
    ap.add_argument("--rustc", default="rustc")
    ap.add_argument("--cc", default="cc")
    ap.add_argument("--extra-arg", action="append", default=[])
    ap.add_argument("--cases", type=int, default=60)
    a = ap.parse_args()
    src = FRONT / "examples/kernels.rs"
    bad = []
    with tempfile.TemporaryDirectory() as d:
        d = pathlib.Path(d)
        mir = d / "k.mir"
        subprocess.run([a.rustc, "--crate-type=lib", "--emit=mir", "-O", "-C", "overflow-checks=on",
                        "-C", "panic=abort", "-o", str(mir), str(src)], check=True)
        code, report = mir2c.translate(mir.read_text())
        (d / "k.c").write_text(code)
        fns = {f.name: f for f in mir2c.parse(mir.read_text())[0]}
        ok = [n for n, why in report if why is None and n in fns and not n.startswith("rejected_")]
        rnd = random.Random(7)
        rmain, cmain = [], []
        for n in ok:
            f = fns[n]
            for case in range(a.cases):
                rargs, cargs, rpre, cpre, outs = [], [], [], [], []
                for k, (loc, ty) in enumerate(f.params):
                    el = mir2c.slice_elem(ty)
                    if el:
                        xs = [value(rnd, el) for _ in range(rnd.randint(0, 40))]
                        nm = f"a{k}"
                        mut = ty.startswith("&mut")
                        rpre.append(f"let {'mut ' if mut else ''}{nm}: Vec<{el}> = vec![{', '.join(rust_lit(x, el) for x in xs)}];")
                        cpre.append(f"{mir2c.INT[el]} {nm}[{max(1, len(xs))}] = {{{', '.join(c_lit(x, el) for x in xs) or '0'}}};")
                        rargs.append(f"&mut {nm}[..]" if mut else f"&{nm}[..]")
                        cargs += [nm, f"{len(xs)}ull"]
                        if mut:
                            outs.append((nm, len(xs)))
                    else:
                        v = value(rnd, ty)
                        rargs.append(rust_lit(v, ty))
                        cargs.append(c_lit(v, ty))
                tag = f"{n}#{case}"
                rprint = " ".join(f'print!(" {{:?}}", {o});' for o, _ in outs)
                rmain.append(f"""    {{ {' '.join(rpre)}
      let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{ let v = k::{n}({', '.join(rargs)}); {rprint.replace('print!(" {:?}", ', 'print!(" {:?}", &') if False else ''} v }}));
      match r {{ Ok(v) => {{ print!("{tag} {{}}", v as i128); {rprint} println!(); }} Err(_) => println!("{tag} panic") }} }}""")
                cprint = " ".join(f'printf(" ["); for (int q = 0; q < {ln}; q++) printf(q ? ", %lld" : "%lld", (long long){o}[q]); printf("]");' for o, ln in outs)
                ret_fmt = '"%llu"' if f.ret in ("u64", "usize") else '"%lld"'
                cast = "(unsigned long long)" if f.ret in ("u64", "usize") else "(long long)"
                cmain.append(f"""  {{ {' '.join(cpre)} long long v = 0; printf("{tag} "); printf({ret_fmt}, {cast}{n}({', '.join(cargs)})); {cprint} printf("\\n"); }}""")
        (d / "main.rs").write_text(f'#[path = "{src}"]\n#[allow(dead_code)]\nmod k;\nfn main() {{\n    std::panic::set_hook(Box::new(|_| {{}}));\n' + "\n".join(rmain) + "\n}\n")
        (d / "main.c").write_text('#include <stdio.h>\n#include <stdint.h>\n#include "k.c"\nint main(void) {\n' + "\n".join(cmain) + "\n  return 0;\n}\n")
        subprocess.run([a.rustc, "-O", "-C", "overflow-checks=on", "-o", str(d / "ref"), str(d / "main.rs")], check=True,
                       capture_output=True)
        subprocess.run([a.cc, "-O1", "-w", "-std=gnu99", "-o", str(d / "gen"), str(d / "main.c")], check=True)
        rout = subprocess.run([str(d / "ref")], capture_output=True, text=True, timeout=600).stdout.splitlines()
        cout = subprocess.run([str(d / "gen")], capture_output=True, text=True, timeout=600).stdout.splitlines()
        cmap = dict(l.split(" ", 1) for l in cout)
        compared = panics = 0
        for l in rout:
            tag, val = l.split(" ", 1)
            if val == "panic":
                panics += 1
                continue
            compared += 1
            if cmap.get(tag) != val.replace(", ", ", "):
                bad.append(f"{tag}: Rust {val}, C {cmap.get(tag)}")
        print(f"differential: {compared} runs compared ({len(ok)} functions), {panics} Rust panics skipped, "
              f"{len(bad)} mismatches")
        # analysis
        rep = d / "rep.json"
        cert = d / "cert.json"
        subprocess.run([a.tool, "--all", f"--report={rep}", f"--opt=certificates={cert}", "--opt=minic",
                        str(d / "k.c"), "--", "-x", "c", "-std=c99", *a.extra_arg], capture_output=True, text=True)
        r = json.loads(rep.read_text())
        for f in r["functions"]:
            bounded = f["wcet"] is not None
            print(f"  {f['name']:20s} {'bound ' + str(f['wcet']) if bounded else 'no bound'}; {f['certificate']}")
            if f["name"].startswith("rejected_") and bounded:
                bad.append(f"{f['name']} must not be bounded")
            if f["name"] in EXPECTED and not bounded:
                bad.append(f"{f['name']} should be bounded")
        if a.checker:
            out = subprocess.run([a.checker, str(cert)], capture_output=True, text=True).stdout
            print("  checker: " + ", ".join(f"{k} {out.count(k)}" for k in ("ACCEPTED", "REJECTED", "VALIDATED")))
            if "REJECTED" in out:
                bad.append("a certificate was rejected")
    for b in bad[:20]:
        print("FAIL " + b)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
