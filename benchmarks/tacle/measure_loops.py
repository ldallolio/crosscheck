# Copyright (c) 2026 Luca Dall'Olio. MIT licence (see the repository's LICENSE).
"""Observed loop counts: run each kernel on its built-in input and record, for
every loop, the largest number of body executions in one entry of the loop.

This is the measured counterpart of the bounds: a sound bound is never below it,
and bound / observed is the pessimism of the bound on that input. TACLeBench's
programs are deterministic with a fixed input, so the observation is the number
the flow facts describe.

How: the kernel is compiled to unoptimised LLVM IR (as in llvm_scev.py, with -g so
that each loop maps back to its source line through `!llvm.loop`), loop-simplify
gives every loop a preheader, and the IR is instrumented as text:

* the preheader stores 0 into a counter local to the function activation (an
  `alloca`, so recursive calls do not disturb an outer activation's count);
* the loop's body block (`for.body`, `while.body` or `do.body`, which Clang
  enters exactly once per iteration) increments the counter and reports it to a
  small runtime that keeps the maximum per loop.

Loops never entered on the input are reported as not reached.
"""

import os
import re
import subprocess
import tempfile

import llvm_scev

BODY = re.compile(r"^(for|while|do)\.body\d*$")
PREDS = re.compile(r"^([\w.\-]+):\s*;\s*preds = (.*)$")

RUNTIME = r"""
#include <stdio.h>
#include <stdlib.h>
#define LB_N 8192
static unsigned long long lb_max[LB_N];
static char lb_entered[LB_N];
void __lb_enter(int id) { lb_entered[id] = 1; }
void __lb_iter(int id, unsigned long long n) { if (n > lb_max[id]) lb_max[id] = n; }
__attribute__((destructor)) static void lb_dump(void) {
  const char *p = getenv("LB_OUT");
  FILE *f = p ? fopen(p, "w") : NULL;
  if (!f) return;
  for (int i = 0; i < LB_N; i++)
    if (lb_entered[i]) fprintf(f, "%d %llu\n", i, lb_max[i]);
  fclose(f);
}
"""


def _blocks(ll_lines):
    """function -> {block -> (index of label line, index of last instruction line)}."""
    out, fn, block, start, last = {}, None, None, None, None
    for i, line in enumerate(ll_lines):
        m = llvm_scev.DEFINE.match(line)
        if m:
            fn, block, start, last = m.group(1), None, None, None
            out[fn] = {}
            continue
        if fn is None:
            continue
        if line.startswith("}"):
            if block is not None:
                out[fn][block] = (start, last)
            fn = None
            continue
        m = llvm_scev.LABEL.match(line)
        if m:
            if block is not None:
                out[fn][block] = (start, last)
            block, start, last = m.group(1), i, i
            continue
        if line.strip() and not line.lstrip().startswith(";"):
            last = i
    return out


def _preds(ll_lines):
    out, fn = {}, None
    for line in ll_lines:
        m = llvm_scev.DEFINE.match(line)
        if m:
            fn = m.group(1); out[fn] = {}; continue
        m = PREDS.match(line)
        if m and fn is not None:
            out[fn][m.group(1)] = [p.strip().lstrip("%") for p in m.group(2).split(",")]
    return out


def observed_counts(unit, include_dir, clang, opt, extra, workdir, cc="cc", timeout=120):
    """Return ({source line: max body executions per entry}, set of lines of loops not reached,
    number of IR loops not instrumented)."""
    stem = unit.stem
    ll0, ll1, ll2, exe = (workdir / f"{stem}.obs{s}" for s in (".0.ll", ".1.ll", ".2.ll", ""))
    subprocess.run([clang, "-x", "c", "-std=gnu99", "-w", "-g", "-O0", "-Xclang", "-disable-O0-optnone",
                    "-fno-discard-value-names", "-emit-llvm", "-S", f"-I{include_dir}", str(unit),
                    "-o", str(ll0), *extra], check=True, capture_output=True, timeout=600)
    subprocess.run([opt, "-passes=loop-simplify", "-S", str(ll0), "-o", str(ll1)],
                   check=True, capture_output=True, timeout=600)
    proc = subprocess.run([opt, "-passes=print<loops>", "-disable-output", str(ll1)],
                          capture_output=True, text=True, timeout=600)
    loops, _ = llvm_scev._parse_opt(proc.stderr + proc.stdout)
    text = ll1.read_text(errors="replace")
    lines = text.splitlines()
    latch_line = llvm_scev._parse_ir(text)
    blocks, preds = _blocks(lines), _preds(lines)

    before, after = {}, {}  # line index -> text to insert before / after it
    id_line, skipped, next_id = {}, 0, 0
    for fn, by_header in loops.items():
        names = {h: [b.split("<")[0] for b in bl] for h, bl in by_header.items()}
        for header, bl in names.items():
            inner = set()
            for h2, bl2 in names.items():
                if h2 != header and h2 in bl and set(bl2) < set(bl):
                    inner |= set(bl2)
            own = [b for b in bl if b not in inner]
            body = [b for b in own if BODY.match(b)]
            outside = [p for p in preds.get(fn, {}).get(header, []) if p not in bl]
            latches = [b.split("<")[0] for b in by_header[header] if "<latch>" in b]
            line = next((latch_line[fn][b] for b in latches if b in latch_line.get(fn, {})), None)
            if len(body) != 1 or len(outside) != 1 or line is None or fn not in blocks:
                skipped += 1
                continue
            lid, next_id = next_id, next_id + 1
            id_line[lid] = line
            c = f"%__lbc{lid}"
            entry_label, _ = blocks[fn]["entry"]
            after.setdefault(entry_label, []).append(f"  {c} = alloca i64, align 8")
            _, pre_last = blocks[fn][outside[0]]
            before.setdefault(pre_last, []).append(
                f"  store i64 0, ptr {c}, align 8\n  call void @__lb_enter(i32 {lid})")
            b_label, b_last = blocks[fn][body[0]]
            k = b_label + 1
            while k <= b_last and re.match(r"^\s*%[\w.\-]+ = phi ", lines[k]):
                k += 1
            before.setdefault(k, []).append(
                f"  %__lbv{lid} = load i64, ptr {c}, align 8\n  %__lbw{lid} = add i64 %__lbv{lid}, 1\n"
                f"  store i64 %__lbw{lid}, ptr {c}, align 8\n  call void @__lb_iter(i32 {lid}, i64 %__lbw{lid})")
    out = []
    for i, line in enumerate(lines):
        out.extend(before.get(i, []))
        out.append(line)
        out.extend(after.get(i, []))
    out.append("declare void @__lb_enter(i32)\ndeclare void @__lb_iter(i32, i64)")
    ll2.write_text("\n".join(out) + "\n")
    rt = workdir / "lb_runtime.c"
    rt.write_text(RUNTIME)
    # Objects from Clang, linked by the system C compiler (a conda Clang may not find
    # the system's libgcc for linking).
    objs = []
    for src in (ll2, rt):
        o = src.with_suffix(".o")
        subprocess.run([clang, "-c", "-w", "-O0", str(src), "-o", str(o), *extra],
                       check=True, capture_output=True, timeout=600)
        objs.append(str(o))
    subprocess.run([cc, *objs, "-o", str(exe), "-lm"], check=True, capture_output=True, timeout=600)
    with tempfile.TemporaryDirectory() as tmp:
        res = os.path.join(tmp, "counts")
        subprocess.run([str(exe)], env={**os.environ, "LB_OUT": res}, capture_output=True, timeout=timeout)
        seen = {}
        if os.path.exists(res):
            for row in open(res):
                i, n = map(int, row.split())
                seen[i] = n
    counts, not_reached = {}, set()
    for lid, line in id_line.items():
        if lid in seen:
            counts[line] = max(counts.get(line, 0), seen[lid])
        else:
            not_reached.add(line)
    return counts, not_reached - set(counts), skipped
