#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""CrossCheck's loop bounds used by a WCET analyser: OTAWA on the Cortex-M0 binaries.

    run_otawa.py --lld LLD [--image otawa:dev] [--only KERNEL]... [--matching wcet|otawa]
                 [--check] [--json OUT]

For each TACLeBench kernel:

1. CrossCheck bounds the loops of the source (as in run_cycles.py: the bounds in the
   calling contexts of the program, and those of runtime.c);
2. the kernel is compiled for the Cortex-M0 with the flags of run_cycles.py and linked
   into an executable (`--lld`: an LLVM linker, e.g. the `rust-lld` of a Rust toolchain;
   no library is linked, so a kernel that calls an undefined function is skipped);
3. the loops of the binary are matched to the source loops by debug lines (wcet.py), and
   each bound is written as an FFX flow fact for the loop header, by function label and
   offset: `<loop label="f" offset="0x16" maxcount="N+1"/>`. A source bound N is a number
   of executions of the body; OTAWA's `maxcount` bounds the executions of the loop header
   per entry of the loop, which is at most N + 1 (the last one leaves the loop);
4. OTAWA computes the WCET of each function by IPET from these flow facts alone, in a
   container without network, with one of two timings (`--timing`):
   - `instructions` (default): `owcet`, script `trivial`, one time unit per instruction,
     so that its result is a number of executed instructions;
   - `m0`: the program `otawa/m0time.cpp`, compiled against OTAWA in the same image, which
     gives each basic block of OTAWA's graphs the Cortex-M0 cycles of its instructions,
     taken from the timing table of m0.py (`<kernel>.times`: function label, offset,
     cycles; a conditional branch is charged as taken). The Cortex-M0 has no cache and
     fixed instruction times, so a block's time is that sum; the result is in cycles;
5. the program is run by the interpreter of m0.py, which counts the instructions of every
   call.

Steps 4 and 5 are done for every function of the kernel that has a bound in the timing
schema of wcet.py (the others call a function without a bound or without code, or contain
a loop without a bound), `main` included. `--check` fails if a bound of OTAWA is below the
instructions executed by a call of that function (a wrong flow fact, loop matching or
reading of `maxcount`), or if OTAWA gives no result for one of these functions.

With `--matching otawa`, step 3 uses the loops of OTAWA's own control-flow graphs instead
(`otawa_flow.py`, the matching of `crosscheck_link.py --processor stm32f4/stm32h7`), and a
function is not given to OTAWA if that matching refuses it; `--check` then tests that
matching against the runs.

Source-line flow facts (`--opt=flowfacts=FILE`, FFX with `source` and `line`) are what
the plugin exports; on optimised code OTAWA cannot always place them (inlined and rotated
loops), which is why this script places them from the binary's control-flow graph.

OTAWA is not distributed with this repository. The image is built by the user from
https://github.com/statinf-otawa/otawa-project (`docker build . --target otawa-dev -t
otawa:dev`); `--owcet-path` is the directory of `owcet` inside it.
"""
import argparse
import json
import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "benchmarks" / "tacle"))
import m0  # noqa: E402
import otawa_flow  # noqa: E402
import run_cycles  # noqa: E402
import run_tacle  # noqa: E402
import wcet  # noqa: E402


def instruction_times(img):
    """(function, address, Cortex-M0 cycles) of every instruction reachable from the entry
    of each function, a conditional branch counted as taken (`m0.cycles`)."""
    out = []
    for fn, (entry, size) in sorted(img.funcs.items()):
        seen, todo = set(), [entry]
        while todo:
            ad = todo.pop()
            if ad in seen or not (entry <= ad < entry + max(size, 2)):
                continue
            seen.add(ad)
            try:
                i = m0.decode(img.mem, ad)
            except Exception:
                continue
            out.append((fn, ad, m0.cycles(i, True)))
            if i.kind in ("cond", "jump") and i.target is not None:
                todo.append(i.target)
            if i.kind in ("cond", "seq", "call"):
                todo.append(ad + i.size)
    return out


def analyse(kernel, work, a, rt):
    name = kernel.name
    run_tacle.run_kernel(a.tool, kernel, work, a.extra_arg)
    rep = json.loads((work / f"{name}.json").read_text())
    text = (work / f"{name}.c").read_text(errors="replace")
    if not text.endswith("\n"):
        text += "\n"
    offset = text.count("\n")
    src = work / f"{name}.m0.c"
    src.write_text(text + (HERE / "runtime.c").read_text())
    bounds = {line + offset: b for line, b in rt.items()}
    for f in rep["functions"]:
        for l in f["loops"]:
            b = l.get("in_context") if l.get("in_context") is not None else (l["bound"] if l.get("verified") else None)
            if l["line"] in bounds and bounds[l["line"]] is not None and b is not None:
                b = max(b, bounds[l["line"]])
            bounds[l["line"]] = b
    obj = work / f"{name}.m0.o"
    p = subprocess.run([a.clang, *run_cycles.FLAGS, f"-I{kernel}", "-c", str(src), "-o", str(obj)],
                       capture_output=True, text=True)
    if p.returncode:
        return dict(kernel=name, status="compilation failed")
    img = m0.load(str(obj))
    lines = wcet.line_table(a.objdump, str(obj), f"{name}.m0.c")
    an = wcet.Analysis(img, lines, bounds)
    schema = {n: an.function(n) for n in sorted(img.funcs)}
    own = sorted(n for n, v in schema.items() if v is not None and not n.startswith("__aeabi"))
    row = dict(kernel=name, functions=len(own), results={})
    if not own:
        row["status"] = "no function with a bound"
        return row
    # flow facts, by label and offset (the functions keep their layout when linked)
    facts = []
    for fn, ls in sorted(an.loops.items()):
        if schema.get(fn) is None:
            continue
        entry = img.funcs[fn][0]
        for (h, _lines, n, _body) in ls:
            facts.append(f'  <loop label="{fn}" offset="{h - entry:#x}" maxcount="{n + 1}"/>')
    ffx = work / f"{name}.otawa.ffx"
    ffx.write_text('<?xml version="1.0"?>\n<flowfacts>\n' + "\n".join(facts) + "\n</flowfacts>\n")
    row["flow_facts"] = len(facts)
    elf = work / f"{name}.m0.elf"
    # Undefined functions (the soft-float library) stay undefined: the functions that call
    # them have no bound and are not given to OTAWA.
    p = subprocess.run([a.lld, "-flavor", "gnu", "-e", "main", "--unresolved-symbols=ignore-all",
                        "-o", str(elf), str(obj)], capture_output=True, text=True)
    if p.returncode:
        row["status"] = "not linked: " + (p.stderr.strip().splitlines() or ["?"])[0][-120:]
        return row
    if a.matching == "otawa":
        # the loops of OTAWA's own graphs, matched by otawa_flow.py (as crosscheck_link.py
        # does for the processors modelled by OTAWA), instead of those of wcet.py
        elf.chmod(0o644)
        lines_e = wcet.line_table(a.objdump, str(elf), [src.name])
        calls, unsupported = otawa_flow.call_graph(a.objdump, str(elf))
        graphs, _ = otawa_flow.graphs(a.image, work, elf.name, own, a.timeout)
        text, missing = otawa_flow.flow_facts(graphs, lines_e, {(src.name, l): b for l, b in bounds.items()})
        ffx.write_text(text)
        row["flow_facts"] = text.count("<loop ")
        refused = {f: otawa_flow.unsupported_reason(otawa_flow.reachable(calls, f), unsupported, missing, calls)
                   for f in own}
        row["refused_by_matching"] = {f: w for f, w in refused.items() if w}
        own = [f for f in own if not refused[f]]
    files = [elf, ffx]
    mounts = ["-v", f"{work}:/w:ro"]
    if a.timing == "m0":
        times = work / f"{name}.times"
        times.write_text("".join(f"{fn} {ad - img.funcs[fn][0]} {c}\n" for fn, ad, c in instruction_times(img)))
        files.append(times)
        mounts += ["-v", f"{a.build}:/b:ro"]
        run = lambda fn: f"/b/m0time /w/{elf.name} {fn} /w/{ffx.name} /w/{times.name}"
    else:
        run = lambda fn: f"{a.owcet_path}/owcet -s trivial -p stages=1 /w/{elf.name} {fn} -f /w/{ffx.name}"
    for f in files:
        f.chmod(0o644)
    loop = "; ".join(f"echo \"== {fn}\"; timeout {int(a.timeout)} {run(fn)} 2>&1 | grep -E \"^WCET|^ERROR|^no time\" | head -2"
                     for fn in own)
    p = subprocess.run(["docker", "run", "--rm", "--network", "none", *mounts, a.image,
                        "bash", "-c", loop], capture_output=True, text=True)
    cur = None
    for line in p.stdout.splitlines():
        if line.startswith("== "):
            cur = line[3:]
            row["results"][cur] = dict(schema=schema[cur])
        m = re.match(r"WCET\[.*\] = (\d+) cycles", line)
        if m and cur:
            row["results"][cur]["otawa"] = int(m.group(1))
        if (line.startswith("ERROR") or line.startswith("no time")) and cur:
            row["results"][cur]["error"] = line[:160]
    # the run: instructions of every completed call, by function
    entry = {ad: n for n, (ad, _) in img.funcs.items()}
    stack, observed = [], {}
    mach = m0.Machine(img)

    def hook(i, before, nxt):
        if i is not None and i.kind == "call":
            stack.append((entry.get(i.target), mach.cyc, i.addr + 4))
        elif stack and nxt == stack[-1][2] and (i is None or i.kind == "ret"):
            fn, start, _ = stack.pop()
            if fn is not None:
                observed[fn] = max(observed.get(fn, 0), mach.cyc - start)

    mach.on_insn = hook
    try:
        mach.call("main", max_cycles=2 * 10**9)
        observed["main"] = mach.cyc
        row["status"] = "ok"
    except m0.Stop as e:
        row["status"] = "run stopped (" + str(e) + "); completed calls compared"
    for fn, r in row["results"].items():
        if fn in observed:
            r["executed"] = observed[fn]
    return row


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tool", default=str(ROOT / "clang-plugin/build/crosscheck-tool"))
    ap.add_argument("--cache", default=str(ROOT / "benchmarks/tacle/.cache"))
    ap.add_argument("--extra-arg", action="append", default=[])
    ap.add_argument("--only", action="append")
    ap.add_argument("--clang", default=run_cycles.default_tool("clang"))
    ap.add_argument("--objdump", default=run_cycles.default_tool("llvm-objdump"))
    ap.add_argument("--lld", required=True, help="an LLVM linker (ld.lld or rust-lld)")
    ap.add_argument("--image", default="otawa:dev")
    ap.add_argument("--owcet-path", default="/tmp/otawa-install/bin")
    ap.add_argument("--timeout", type=float, default=300)
    ap.add_argument("--timing", choices=["instructions", "m0"], default="instructions")
    ap.add_argument("--matching", choices=["wcet", "otawa"], default="wcet",
                    help="loops matched on the graph of wcet.py, or on OTAWA's (otawa_flow.py)")
    ap.add_argument("--json")
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    # One unit per instruction, in the interpreter and in the timing schema, as in OTAWA's
    # `trivial` script with stages=1.
    if a.timing == "instructions":
        m0.cycles = lambda i, taken=True: 1
    src = run_tacle.fetch(pathlib.Path(a.cache), run_tacle.REV)
    work = pathlib.Path(a.cache) / "otawa"   # not `work`: other scripts write there
    work.mkdir(parents=True, exist_ok=True)
    work.chmod(0o755)
    kernels = sorted((src / "bench/kernel").iterdir())
    if a.only:
        kernels = [k for k in kernels if k.name in a.only]
    if a.timing == "m0":
        build = pathlib.Path(a.cache) / "otawa-build"
        build.mkdir(parents=True, exist_ok=True)
        build.chmod(0o777)
        p = subprocess.run(["docker", "run", "--rm", "--network", "none", "-v", f"{HERE / 'otawa'}:/src:ro",
                            "-v", f"{build}:/b", a.image, "bash", "-c",
                            f"export PATH={a.owcet_path}:$PATH; g++ -std=c++17 -O1 $(otawa-config --cflags) "
                            "/src/m0time.cpp -o /b/m0time $(otawa-config --libs) "
                            f"-Wl,-rpath,{a.owcet_path}/../lib"], capture_output=True, text=True)
        if p.returncode:
            sys.exit("m0time does not compile:\n" + p.stdout + p.stderr)
        a.build = build
    rt = run_cycles.runtime_bounds(a.tool, work, a.extra_arg)
    rows = []
    for k in kernels:
        r = analyse(k, work, a, rt)
        rows.append(r)
        res = r.get("results", {}).values()
        print(f"{r['kernel']:16s} functions={r.get('functions', 0)} otawa={sum('otawa' in x for x in res)} "
              f"compared={sum('otawa' in x and 'executed' in x for x in res)} "
              f"violations={sum('otawa' in x and 'executed' in x and x['otawa'] < x['executed'] for x in res)}"
              f"  {r['status']}", file=sys.stderr)
        for fn, x in r.get("results", {}).items():
            if "otawa" not in x:
                print(f"   no result for {fn}: {x.get('error', '?')}", file=sys.stderr)
            elif "executed" in x and x["otawa"] < x["executed"]:
                print(f"   VIOLATION {fn}: OTAWA {x['otawa']} < executed {x['executed']}", file=sys.stderr)
    allr = [(r["kernel"], fn, x) for r in rows for fn, x in r.get("results", {}).items()]
    got = [x for _, _, x in allr if "otawa" in x]
    cmp_ = [x for x in got if "executed" in x]
    ratios = sorted(x["otawa"] / x["executed"] for x in cmp_ if x["executed"])
    geo = 1.0
    for q in ratios:
        geo *= q ** (1 / len(ratios))
    tot = dict(kernels=len(rows), functions=len(allr), otawa=len(got), otawa_failed=len(allr) - len(got),
               entry_functions=sum(fn == "main" and "otawa" in x for _, fn, x in allr),
               flow_facts=sum(r.get("flow_facts", 0) for r in rows),
               compared=len(cmp_), violations=sum(x["otawa"] < x["executed"] for x in cmp_),
               exact=sum(x["otawa"] == x["executed"] for x in cmp_),
               geometric_mean=round(geo, 2) if ratios else None,
               max_ratio=round(ratios[-1], 2) if ratios else None,
               otawa_at_most_schema=sum(x["otawa"] <= x["schema"] for x in got))
    print(json.dumps(tot))
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(dict(total=tot, kernels=rows), indent=1) + "\n")
    if a.check and (tot["violations"] or tot["otawa_failed"]):
        sys.exit(1)


if __name__ == "__main__":
    main()
