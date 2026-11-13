# Copyright (c) 2026 Luca Dall'Olio. MIT licence (see the repository's LICENSE).
"""Loop bounds from LLVM's ScalarEvolution, as a baseline for run_tacle.py.

For every loop, ScalarEvolution reports a *constant max backedge-taken count* N
when it can prove one (intraprocedurally, like CrossCheck). The number of
executions of the loop body is then at most N if the header is the only block
that leaves the loop (a `for`/`while` test), and at most N + 1 otherwise (a `do`
loop, or a loop left by `break`/`return`). Loops are mapped back to source lines
through the start location that Clang attaches to `!llvm.loop` metadata when
compiling with -g.

The IR is unoptimised except for mem2reg (no inlining, no unrolling), so each
source loop is analysed once, in its own function.
"""

import re
import subprocess

LOOPINFO_FN = re.compile(r"^Loop info for function '(.+)':")
LOOP_LINE = re.compile(r"^\s*Loop at depth \d+ containing: (.*)$")
SCEV_FN = re.compile(r"^Printing analysis 'Scalar Evolution Analysis' for function '(.+)':")
SCEV_MAX = re.compile(r"^Loop %([\w.\-]+): constant max backedge-taken count is (?:i\d+ )?(\d+)\s*$")
DEFINE = re.compile(r"^define .*@\"?([\w.$]+)\"?\(")
LABEL = re.compile(r"^([\w.\-]+):")
LOOPMD = re.compile(r"!llvm\.loop !(\d+)")
MDNODE = re.compile(r"^!(\d+) = (?:distinct )?!\{(.*)\}\s*$")
DILOC = re.compile(r"^!(\d+) = !DILocation\(line: (\d+)")


def _parse_ir(ll_text):
    """function -> {block label -> loop start line, for blocks ending in an !llvm.loop branch}."""
    md_nodes, dilocs = {}, {}
    for line in ll_text.splitlines():
        m = DILOC.match(line)
        if m:
            dilocs[m.group(1)] = int(m.group(2))
            continue
        m = MDNODE.match(line)
        if m:
            md_nodes[m.group(1)] = re.findall(r"!(\d+)", m.group(2))
    latch_line = {}
    fn, block = None, None
    for line in ll_text.splitlines():
        m = DEFINE.match(line)
        if m:
            fn, block = m.group(1), "entry"
            latch_line[fn] = {}
            continue
        if fn is None:
            continue
        if line.startswith("}"):
            fn = None
            continue
        m = LABEL.match(line)
        if m:
            block = m.group(1)
            continue
        m = LOOPMD.search(line)
        if m:
            refs = md_nodes.get(m.group(1), [])
            lines = [dilocs[r] for r in refs if r in dilocs]
            if lines:
                latch_line[fn][block] = lines[0]  # first location = start of the loop statement
    return latch_line


def _parse_opt(output):
    """function -> {header -> (blocks with tags)}, function -> {header -> N}."""
    loops, counts = {}, {}
    fn = None
    for line in output.splitlines():
        m = LOOPINFO_FN.match(line)
        if m:
            fn = m.group(1); loops.setdefault(fn, {}); continue
        m = SCEV_FN.match(line)
        if m:
            fn = m.group(1); counts.setdefault(fn, {}); continue
        m = LOOP_LINE.match(line)
        if m and fn is not None:
            blocks = [b.strip().lstrip("%") for b in m.group(1).split(",")]
            header = next(b for b in blocks if "<header>" in b).split("<")[0]
            loops[fn][header] = blocks
            continue
        m = SCEV_MAX.match(line)
        if m and fn is not None:
            counts[fn][m.group(1)] = int(m.group(2))
    return loops, counts


def scev_bounds(unit, include_dir, clang, opt, extra, workdir):
    """Return {source line of a loop: bound on body executions} for one C file."""
    ll = workdir / (unit.stem + ".ll")
    subprocess.run([clang, "-x", "c", "-std=gnu99", "-w", "-g", "-O0", "-Xclang", "-disable-O0-optnone",
                    "-fno-discard-value-names", "-emit-llvm", "-S", f"-I{include_dir}", str(unit),
                    "-o", str(ll), *extra], check=True, capture_output=True, timeout=600)
    proc = subprocess.run([opt, "-passes=mem2reg,loop-simplify,lcssa,print<loops>,print<scalar-evolution>",
                           "-disable-output", str(ll)], capture_output=True, text=True, timeout=600)
    loops, counts = _parse_opt(proc.stderr + proc.stdout)
    latches = _parse_ir(ll.read_text(errors="replace"))
    out = {}
    for fn, by_header in loops.items():
        for header, blocks in by_header.items():
            n = counts.get(fn, {}).get(header)
            if n is None:
                continue
            # Only this loop's own latches (tagged in its own listing): blocks of
            # nested loops also carry !llvm.loop, for their own loop.
            own = [b.split("<")[0] for b in blocks if "<latch>" in b]
            line = next((latches.get(fn, {}).get(b) for b in own if b in latches.get(fn, {})), None)
            if line is None:
                continue
            other_exit = any("<exiting>" in b and b.split("<")[0] != header for b in blocks)
            header_exits = any("<exiting>" in b and b.split("<")[0] == header for b in blocks)
            bound = n if header_exits and not other_exit else n + 1
            out[line] = max(out.get(line, bound), bound)  # one source loop, several IR loops: keep the safe value
    return out
