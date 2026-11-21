#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Diagnosis of the kernel loops that `binloops.py` does not certify on the machine code.

    python3 benchmarks/cycles/classify_loops.py RUN.json [--examples]

RUN.json is the output of `run_cycles.py --json ... --certify-loops --abi --frame` (default
build). For every loop left uncertified (the run-time division routines `__aeabi_*` are
skipped), the exits are examined: the instruction that set the flags of the exit branch and,
for each of its register operands, the definitions that reach it along paths inside the loop
(a backward search through registers and tracked words of the frame). An operand is a
*counter* if every such definition adds a constant to it, *invariant* if none is in the loop.
For a counter compared with a constant or an invariant limit, the definitions of its value
at the loop entry are reported too. Heuristic and untrusted: it explains failures, it proves
nothing; the groups are those quoted in the cycles README and in Paper III.
"""
import collections
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import binloops as B  # noqa: E402
import m0  # noqa: E402
import wcet  # noqa: E402

W = HERE.parent / "tacle/.cache/work"

def mn(ctx, a):
    return str(ctx.insn[a]).split(":")[1].split("(")[0]


LOADS = {"ldri", "ldrr", "ldrbi", "ldrhi", "ldrb", "ldrh", "ldm", "ldrbr", "ldrhr", "ldrsb", "ldrsh"}
SHIFTS = {"lsli", "lsri", "asri", "lsl", "lsr", "asr", "ror"}

def preds(ctx):
    P = collections.defaultdict(list)
    for a in ctx.nodes:
        for n, _w, _c in ctx.out[a]:
            if n is not None: P[n].append(a)
    return P

def origin(ctx, body, h, node, var, P):
    """kinds of the definitions reaching `var` just before `node`, along paths inside the loop"""
    Bs = set(body); out = set(); seen = set(); work = [(node, var)]
    while work:
        n, v = work.pop()
        if (n, v) in seen: continue
        seen.add((n, v))
        for p in P[n]:
            if p not in Bs or (n == h and p not in Bs):
                out.add("entry"); continue
            if n == h and p in Bs and v[0] == "r" and False: pass
            dfn = None
            if v[0] == "r":
                sp, mem, ld, _e = ctx.st[p]
                if ld and ld[0] == v[1]:
                    dd = ctx.sp.get(p); k = -(dd + ld[1]) if dd is not None else None
                    if k in ctx.slots: work.append((p, ("s", ctx.slots.index(k))))
                    else: out.add("load-sp-untracked")
                    continue
                for r, val in ctx.eff[p][0]:
                    if r == v[1]: dfn = val; break
                if dfn is None: work.append((p, v)); continue
                if dfn == "any":
                    m = mn(ctx, p)
                    out.add("load" if m in LOADS else "shift" if m in SHIFTS else {"mul": "mul", "bl": "call", "ldrlit": "const"}.get(m, "other:" + m))
                    continue
                op, x, y = dfn
                if op == "shl": out.add("shift"); continue
                srcs = [t for t in (x, y) if t[0] == "reg"]
                if not srcs: out.add("const"); continue
                if len(srcs) == 2:
                    out.add("sum2"); continue
                c = [t[1] for t in (x, y) if t[0] == "imm"][0]
                if c != 0: out.add("step")
                work.append((p, ("r", srcs[0][1])))
            else:
                k = ctx.slots[v[1]]
                sp, mem, ld, _e = ctx.st[p]; dd = ctx.sp.get(p)
                if mem != "keep" and mem[0] == "store" and dd is not None and -(dd + mem[1]) == k:
                    work.append((p, ("r", mem[2]))); continue
                if mem != "keep" and (mem[0] == "store" and dd is None or mem[0] == "other" and not ctx.frame):
                    out.add("clobber"); continue
                work.append((p, v))
    return out

def entry_def(ctx, h, Bs, r, P):
    """mnemonics of the definitions of register r reaching the loop entry from outside"""
    out = set(); seen = set(); work = [(p, r) for p in P[h] if p not in Bs]
    while work:
        p, v = work.pop()
        if (p, v) in seen or len(seen) > 400: continue
        seen.add((p, v))
        sp, mem, ld, _e = ctx.st[p]
        if ld and ld[0] == v: out.add("ldrsp"); continue
        d = None
        for rr, val in ctx.eff[p][0]:
            if rr == v: d = val; break
        if d is None:
            if p == ctx.entry: out.add("arg"); continue
            work += [(q, v) for q in P[p]]; continue
        if d == "any": out.add(mn(ctx, p)); continue
        srcs = [t for t in B.val_srcs(d) if t[0] == "reg"]
        if not srcs: out.add("imm"); continue
        if len(srcs) == 2: out.add("sum2"); continue
        work += [(q, srcs[0][1]) for q in P[p]] if p != ctx.entry else []
        if p == ctx.entry: out.add("arg")
    return "/".join(sorted(out))

def opclass(ks):
    if ks <= {"entry"}: return "inv"
    if ks <= {"entry", "step"} and "step" in ks: return "counter"
    bad = sorted(k for k in ks if k not in ("entry", "step"))
    return "+".join(bad) if bad else "noinit"


INIT = {"ldrsp": "initial value from a word of the frame", "lsli": "initial value built by LSL",
        "lsri": "initial value by LSR of an argument", "ldrlit": "initial value from the literal pool",
        "mvn": "initial value by MVN", "stm": "initial value through STM", "arg": "initial value from an argument",
        "imm": "initial value a constant", "and": "initial value by AND", "sum2": "initial value a sum of registers"}


def group(c):
    """The group of a loop's description, and its sub-group."""
    if c.startswith("counter-vs-imm") or c.startswith("counter-vs-bounded"):
        init = c.split("init=")[1].split(" ")[0]
        return "A counter against a constant or a bounded limit", INIT.get(init, "initial value " + init)
    if c.startswith("counter-vs-unbounded"):
        return "B counter against a limit without a bound (a parameter)", c.split(" ", 1)[1]
    if c.startswith("flags-"):
        return "C exit on the flags of a shift", c
    if "call" in c:
        return "D exit on a value returned by a call", c
    if c in ("shift", "shift+shift", "counter+shift") or c.startswith("shift"):
        return "E counter shifted (logarithmic)", c
    if "load" in c and "sp-untracked" not in c:
        return "F exit on data loaded from memory", c
    if "sp-untracked" in c:
        return "G value from a word of the frame that is not tracked", c
    if "stm" in c or "adc" in c or "and" in c:
        return "H value through an instruction whose effect is approximated", c
    return "I other (two counters, sums of registers, ...)", c


def main():
    d = json.loads(pathlib.Path(sys.argv[1]).read_text())
    examples = "--examples" in sys.argv
    cat = collections.Counter(); ex = collections.defaultdict(list); reasons = collections.Counter()
    for k in d["kernels"]:
        img = m0.load(str(W / f"{k['kernel']}.m0.o")); an = wcet.Analysis(img, {}, {None: 5})
        for fn, v in k.get("loops_detail", {}).items():
            if fn.startswith("__aeabi") or not v["other"]: continue
            ctx = B.Ctx(an, fn, True, True); P = preds(ctx); kind = B.kinds_of(ctx); ctx.cong = B.congruences(ctx); st = B.analyse(ctx, kind)
            for h, why in v["other"]:
                reasons[why.split(" ")[0] + " " + " ".join(why.split(" ")[1:3])] += 1
                body = next(b for hh, b, _ in ctx.iloops if hh == h); Bs = set(body)
                exits = [a for a in body if any(n is None or n not in Bs for n, _, _ in ctx.out[a])]
                descs = []
                for a in exits:
                    if ctx.insn[a].kind != "cond": descs.append("exit-not-branch"); continue
                    b = a
                    while b in Bs and ctx.eff[b][1] == "keep": b -= 2
                    fl = ctx.eff[b][1] if b in Bs else "outside"
                    if fl in ("any", "outside"): descs.append("flags-" + (mn(ctx, b) if b in Bs else "outside")); continue
                    ops = []
                    for s in fl[1:]:
                        ops.append(("imm", s[1]) if s[0] == "imm" else (opclass(origin(ctx, body, h, b, ("r", s[1]), P)), s[1]))
                    cls = sorted(o[0] for o in ops)
                    cc = ctx.cc[a]
                    if "counter" in cls and all(c in ("counter", "inv", "imm", "const") for c in cls):
                        if cls.count("counter") == 2: descs.append("two-counters"); continue
                        lim = [o for o in ops if o[0] in ("inv", "const")]
                        cnt = [o for o in ops if o[0] == "counter"][0][1]
                        ent = "init=" + entry_def(ctx, h, Bs, cnt, P) + (" lim=" + entry_def(ctx, h, Bs, lim[0][1], P) if lim else "")
                        M = st[h]
                        if lim and M is not None:
                            lo, hi = ctx.zones.lohi(M, lim[0][1])
                            descs.append("counter-vs-" + ("bounded-limit" if hi < (1 << 31) and lo > -(1 << 31) else "unbounded-limit") + ("-eq" if cc in (0, 1) else "") + " " + ent)
                        else: descs.append("counter-vs-imm" + ("-eq" if cc in (0, 1) else "") + " " + ent)
                    else: descs.append("+".join(c for c in cls if c not in ("imm", "inv")) or "inv-only")
                pri = ["counter-vs-imm", "counter-vs-imm-eq", "counter-vs-bounded-limit", "counter-vs-bounded-limit-eq", "two-counters", "counter-vs-unbounded-limit", "counter-vs-unbounded-limit-eq"]
                got = [x for p in pri for x in descs if x.split(" ")[0] == p]
                c = got[0] if got else " | ".join(sorted(set(descs)))
                cat[c] += 1; ex[c].append((k["kernel"], fn, hex(h), "frame" if ctx.frame else "nofr", why[:20]))
    print("reasons given by the producer:", dict(reasons.most_common()))
    G = collections.Counter(); S = collections.defaultdict(collections.Counter)
    for c, n in cat.items():
        g, s = group(c)
        G[g] += n; S[g][s] += n
    for g in sorted(G):
        print(f"{G[g]:4d}  {g}")
        for s, n in S[g].most_common():
            print(f"      {n:4d}  {s}")
    print(f"{sum(G.values()):4d}  in all")
    if examples:
        for c, n in cat.most_common():
            print(n, c, ex[c][:4])


if __name__ == "__main__":
    main()
