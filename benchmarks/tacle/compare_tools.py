#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. MIT licence (see the repository's LICENSE).
"""Compare CrossCheck with other bound analysers on the TACLeBench kernels.

Tools and what is compared (see README.md, "Comparison with other tools"):

* LLVM ScalarEvolution (constant max backedge-taken count, llvm_scev.py): run
  live; compared loop by loop with the `loopbound` flow facts, like CrossCheck.
* KoAT2 (v2.1.0 Docker image, C front-end llvm2kittel): results read from
  --koat-dir, one `<kernel>.tsv` per kernel produced by koat_in_container.sh from
  the preprocessed kernel (the image's Clang 3.4 cannot see the kernel's headers):
      clang -E -P -w -std=gnu99 -I<kernel dir> .cache/work/<kernel>.c -o <kernel>.i
      docker run -i --rm --network none --entrypoint bash koat2:latest \
          -c "$(cat koat_in_container.sh)" < <kernel>.i > <kernel>.tsv
* Infer cost analysis (v1.3.0): results read from --infer-dir, one
  `<kernel>.json` per kernel (infer-out/costs-report.json) produced by
      infer --cost-only -o out -- clang -c -w -std=gnu99 -I<kernel dir> .cache/work/<kernel>.c

KoAT2 and Infer give one bound per function, not per loop; they are compared on
the entry function `<kernel>_main` and on all functions of the kernel. Their cost
units differ from CrossCheck's (transitions of the integer program; Infer's
instruction count), so only "finite bound or not" and the asymptotic class are
compared, never the numbers.

The KoAT2 and Infer answers of 2026-11-13 are stored in results/ (see README.md);
by default they are read from there, and only ScalarEvolution is run live.
The observed loop counts (measure_loops.py) are measured live: each kernel is
instrumented, linked with --cc and run on its built-in input.
Run run_tacle.py first: it fetches the benchmarks and writes .cache/work/.
"""

import argparse
import json
import math
import pathlib
import re
import shutil
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import llvm_scev  # noqa: E402
import measure_loops  # noqa: E402
import run_tacle  # noqa: E402

TYPE_RANGE = 1 << 24  # a bound this large comes from the range of the integer type


def crosscheck(kernel, work):
    rep = json.loads((work / f"{kernel}.json").read_text())
    loops, ctx, funcs = {}, {}, {}
    for f in rep["functions"]:
        funcs[f["name"]] = "const" if f["ok"] else "none"
        for lp in f.get("loops") or []:
            if lp.get("verified") and lp.get("bound") is not None:
                loops[lp["line"]] = min(loops.get(lp["line"], lp["bound"]), lp["bound"])
            if lp.get("in_context") is not None:
                ctx[lp["line"]] = max(ctx.get(lp["line"], 0), lp["in_context"])
    return loops, funcs, ctx


def koat(path):
    """function -> 'const' | 'symbolic' | 'none' (unbounded, timeout or translation failure)."""
    out = {}
    if not path.exists():
        return None
    for line in path.read_text().splitlines():
        if "\t" not in line:
            continue
        fn, ans = line.split("\t", 1)
        ans = ans.strip()
        if ans.startswith("!") or ans.startswith("inf") or "Infinity" in ans or not ans:
            out[fn] = "none"
        else:
            out[fn] = "const" if "{O(1)}" in ans else "symbolic"
    return out


def koat_values(path):
    """function -> constant bound, for KoAT2 answers in O(1)."""
    out = {}
    if path.exists():
        for line in path.read_text().splitlines():
            fn, _, ans = line.partition("\t")
            m = re.match(r"\s*(\d+)\s*\{O\(1\)\}", ans)
            if m:
                out[fn] = int(m.group(1))
    return out


def cofloco(path):
    """function -> ('const' | 'symbolic' | 'none', constant bound or None)."""
    if not path.exists():
        return None
    out = {}
    for line in path.read_text().splitlines():
        parts = [p.strip() for p in line.split("\t")]
        if len(parts) < 2:
            continue
        fn = parts[0]
        if parts[1].startswith("!") or len(parts) < 3:
            out[fn] = ("none", None)
            continue
        mx, cls = parts[1], parts[2]
        if cls in ("infinity", "unknown") or "inf" in mx:
            out[fn] = ("none", None)
        elif cls == "constant" and re.fullmatch(r"\d+", mx):
            out[fn] = ("const", int(mx))
        else:
            out[fn] = ("symbolic", None)
    return out


def infer(path):
    if not path.exists():
        return None
    out = {}
    for p in json.loads(path.read_text()):
        big_o = p["exec_cost"]["hum"]["big_o"]
        out[p["procedure_name"]] = "none" if big_o == "Top" else "const" if big_o in ("O(1)", "O(0)") else "symbolic"
    return out


ORANGE_LOOP = re.compile(r'<loop source="([^"]*)" line="(\d+)" max="([^"]*)"')


def orange(path, kernel):
    """{source line: max} from oRange's summary <loop> elements (maximum over all calling
    contexts); a max that is not a number (unknown or symbolic) counts as no bound."""
    if not path.exists():
        return None
    out = {}
    for src, line, mx in ORANGE_LOOP.findall(path.read_text(errors="replace")):
        if src != f"{kernel}.c":
            continue
        line = int(line)
        if mx.isdigit():
            out[line] = max(out.get(line, 0), int(mx))
        else:
            out.setdefault(line, None)
    return {l: b for l, b in out.items() if b is not None}


def loop_stats(pragmas, bounds):
    s = dict(bounded=0, equal=0, looser=0, tighter=0, type_range=0)
    for line, mx in pragmas.items():
        b = bounds.get(line)
        if b is None:
            continue
        if b >= TYPE_RANGE:
            s["type_range"] += 1
            continue
        s["bounded"] += 1
        s["equal" if b == mx else "looser" if b > mx else "tighter"] += 1
    return s


def observed_stats(pragmas, bounds, obs):
    """Bounds against the observed per-entry maximum, on the loops the run reaches."""
    s = dict(reached=0, bounded=0, below=0, equal=0, above=0, ratios=[], below_at=[])
    for line in pragmas:
        if line not in obs:
            continue
        s["reached"] += 1
        b = bounds.get(line)
        if b is None or b >= TYPE_RANGE:
            continue
        s["bounded"] += 1
        o = obs[line]
        s["below" if b < o else "equal" if b == o else "above"] += 1
        if b < o:
            s["below_at"].append([line, b, o])
        if o > 0:
            s["ratios"].append(b / o)
    return s


def overlap(pragmas, cc, sc):
    """Loops bounded by only one of CrossCheck / the other tool, and which is tighter when both."""
    sc = {l: b for l, b in sc.items() if b < TYPE_RANGE}
    o = dict(cc_only=0, other_only=0, cc_tighter=0, other_tighter=0, same=0)
    for line in pragmas:
        a, b = cc.get(line), sc.get(line)
        if a is not None and b is None:
            o["cc_only"] += 1
        elif b is not None and a is None:
            o["other_only"] += 1
        elif a is not None:
            o["same" if a == b else "cc_tighter" if a < b else "other_tighter"] += 1
    return o


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cache", default=str(HERE / ".cache"))
    ap.add_argument("--clang", default=shutil.which("clang") or "/usr/lib/llvm-18/bin/clang")
    ap.add_argument("--opt", default=shutil.which("opt") or "/usr/lib/llvm-18/bin/opt")
    ap.add_argument("--extra-arg", action="append", default=[])
    ap.add_argument("--cc", default="cc", help="C compiler used to link the instrumented kernels")
    ap.add_argument("--koat-dir", default=str(HERE / "results/koat2"),
                    help="KoAT2 answers, one <kernel>.tsv each (default: the stored results)")
    ap.add_argument("--infer-dir", default=str(HERE / "results/infer"),
                    help="Infer costs-report.json files, one <kernel>.json each (default: the stored results)")
    ap.add_argument("--cofloco-dir", default=str(HERE / "results/cofloco"),
                    help="CoFloCo answers, one <kernel>.tsv each (default: the stored results)")
    ap.add_argument("--orange-dir", default=str(HERE / "results/orange"),
                    help="oRange flow-fact XML, one <kernel>.xml each (default: the stored results)")
    ap.add_argument("--json"); ap.add_argument("--latex")
    ap.add_argument("--check", action="store_true",
                    help="exit with status 1 if a CrossCheck loop bound is below an observed count")
    a = ap.parse_args()

    cache = pathlib.Path(a.cache)
    work = cache / "work"
    kdirs = cache / "tacle-bench/bench/kernel"
    rows = []
    for kdir in sorted(p for p in kdirs.iterdir() if p.is_dir()):
        k = kdir.name
        unit = work / f"{k}.c"
        prag = run_tacle.pragmas(unit.read_text(errors="replace").splitlines())
        cc_loops, cc_funcs, cc_ctx = crosscheck(k, work)
        sc_loops = llvm_scev.scev_bounds(unit, kdir, a.clang, a.opt, a.extra_arg, work)
        obs, not_reached, _ = measure_loops.observed_counts(unit, kdir, a.clang, a.opt, a.extra_arg, work, a.cc)
        obs = {l: n for l, n in obs.items() if l in prag}
        orl = orange(pathlib.Path(a.orange_dir) / f"{k}.xml", k) if a.orange_dir else None
        cof = cofloco(pathlib.Path(a.cofloco_dir) / f"{k}.tsv") if a.cofloco_dir else None
        kov = koat_values(pathlib.Path(a.koat_dir) / f"{k}.tsv") if a.koat_dir else {}
        ko = koat(pathlib.Path(a.koat_dir) / f"{k}.tsv") if a.koat_dir else None
        inf = infer(pathlib.Path(a.infer_dir) / f"{k}.json") if a.infer_dir else None
        main_fn = f"{k}_main"
        names = sorted(cc_funcs)  # every function defined in the kernel
        cof_cls = None if cof is None else {n: c for n, (c, _) in cof.items()}
        both = [n for n in sorted(cc_funcs) if cof and cof.get(n, ("none",))[0] == "const" and n in kov]
        row_ck = dict(both=len(both),
                      cofloco_lower=sum(1 for n in both if cof[n][1] < kov[n]),
                      equal=sum(1 for n in both if cof[n][1] == kov[n]),
                      koat_lower=sum(1 for n in both if cof[n][1] > kov[n]))
        row = dict(kernel=k, cofloco_vs_koat=row_ck, loops=len(prag), functions=len(names),
                   crosscheck=loop_stats(prag, cc_loops), crosscheck_ctx=loop_stats(prag, cc_ctx),
                   scev=loop_stats(prag, sc_loops),
                   orange=loop_stats(prag, orl or {}),
                   both_loops=sum(1 for l in prag if l in cc_loops and sc_loops.get(l, TYPE_RANGE) < TYPE_RANGE),
                   overlap=overlap(prag, cc_loops, sc_loops),
                   overlap_orange=overlap(prag, cc_loops, orl or {}),
                   overlap_ctx_orange=overlap(prag, cc_ctx, orl or {}),
                   observed={str(l): n for l, n in sorted(obs.items())},
                   vs_observed={t: observed_stats(prag, b, obs)
                                for t, b in (("crosscheck", cc_loops), ("crosscheck_ctx", cc_ctx),
                                             ("scev", sc_loops), ("orange", orl or {}),
                                             ("flow_fact", prag))},
                   main=dict(crosscheck=cc_funcs.get(main_fn, "none"),
                             koat=None if ko is None else ko.get(main_fn, "none"),
                             cofloco=None if cof_cls is None else cof_cls.get(main_fn, "none"),
                             infer=None if inf is None else inf.get(main_fn, "none")),
                   funcs={t: None if d is None else {c: sum(1 for n in names if d.get(n, "none") == c)
                                                     for c in ("const", "symbolic", "none")}
                          for t, d in (("crosscheck", cc_funcs), ("koat", ko), ("cofloco", cof_cls),
                                       ("infer", inf))})
        rows.append(row)
        print(f"{k:16s} cc={row['crosscheck']} scev={row['scev']} main={row['main']}", file=sys.stderr)

    def tot(tool, key):
        return sum(r[tool][key] for r in rows)
    print("\nLoops with a flow fact:", sum(r["loops"] for r in rows))
    for tool in ("crosscheck", "crosscheck_ctx", "scev", "orange"):
        print(f"  {tool:14s} bounded={tot(tool,'bounded')} equal={tot(tool,'equal')} looser={tot(tool,'looser')}"
              f" tighter={tot(tool,'tighter')} type-range-only={tot(tool,'type_range')}")
    for key, other in (("overlap", "crosscheck/scev"), ("overlap_orange", "crosscheck/orange"),
                       ("overlap_ctx_orange", "crosscheck_ctx/orange")):
        print(f"  overlap {other}:", {k: sum(r[key][k] for r in rows) for k in rows[0][key]})
    print("Against the observed counts (loops reached on the built-in input):",
          sum(r["vs_observed"]["crosscheck"]["reached"] for r in rows))
    for tool in ("crosscheck", "crosscheck_ctx", "scev", "orange", "flow_fact"):
        v = {k: sum(r["vs_observed"][tool][k] for r in rows) for k in ("bounded", "below", "equal", "above")}
        ratios = sorted(x for r in rows for x in r["vs_observed"][tool]["ratios"])
        med = ratios[len(ratios) // 2] if ratios else None
        gm = math.exp(sum(math.log(x) for x in ratios) / len(ratios)) if ratios else None
        print(f"  {tool:14s} " + " ".join(f"{k}={n}" for k, n in v.items())
              + (f" ratio median={med:.2f} geomean={gm:.2f} max={ratios[-1]:.1f}" if ratios else ""))
        for r in rows:
            for line, b, o in r["vs_observed"][tool]["below_at"]:
                print(f"    below the observed count: {r['kernel']} line {line}: bound {b}, observed {o}")
    print("Entry functions <kernel>_main with a finite bound (const / symbolic):")
    for tool in ("crosscheck", "koat", "cofloco", "infer"):
        v = [r["main"][tool] for r in rows]
        if None in v:
            continue
        print(f"  {tool:10s} const={v.count('const')} symbolic={v.count('symbolic')}")
    print("All functions (const / symbolic / none):", sum(r["functions"] for r in rows))
    for tool in ("crosscheck", "koat", "cofloco", "infer"):
        if any(r["funcs"][tool] is None for r in rows):
            continue
        print(f"  {tool:10s} " + " ".join(f"{c}={sum(r['funcs'][tool][c] for r in rows)}"
                                         for c in ("const", "symbolic", "none")))

    print("CoFloCo vs KoAT2 (same integer programs, same unit), functions with a constant bound from both:",
          {k: sum(r["cofloco_vs_koat"][k] for r in rows) for k in rows[0]["cofloco_vs_koat"]})
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(rows, indent=2) + "\n")
    if a.latex:
        mark = {"const": r"\checkmark", "symbolic": "sym.", "none": "--", None: "?"}
        lines = []
        for r in rows:
            c, s = r["crosscheck"], r["scev"]
            lines.append(f"{r['kernel'].replace('_', chr(92) + '_')} & {r['loops']} & {c['bounded']} & {c['equal']}"
                         f" & {s['bounded']} & {s['equal']} & {s['type_range']}"
                         f" & {mark[r['main']['crosscheck']]} & {mark[r['main']['koat']]} & {mark[r['main']['infer']]} \\\\")
        def cnt(tool, val):
            return sum(1 for r in rows if r["main"][tool] == val)
        lines.append(r"\midrule")
        lines.append(f"Total & {sum(r['loops'] for r in rows)} & {tot('crosscheck','bounded')} & {tot('crosscheck','equal')}"
                     f" & {tot('scev','bounded')} & {tot('scev','equal')} & {tot('scev','type_range')}"
                     + "".join(f" & {cnt(t,'const')}" + (f"+{cnt(t,'symbolic')}" if cnt(t, 'symbolic') else "")
                               for t in ("crosscheck", "koat", "infer")) + r" \\")
        pathlib.Path(a.latex).write_text("\n".join(lines) + "\n")
    if a.check and any(r["vs_observed"][t]["below"] for r in rows for t in ("crosscheck", "crosscheck_ctx")):
        print("error: a CrossCheck loop bound is below an observed count", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
