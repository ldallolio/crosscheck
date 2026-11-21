# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Source loop bounds as OTAWA flow facts on any binary OTAWA decodes, and OTAWA's WCET.

Used by `clang-plugin/scripts/crosscheck_link.py` for the processors whose timing model is
OTAWA's (`PROCESSORS`). Unlike `run_otawa.py`, which matches the loops on the Cortex-M0
control-flow graph of `wcet.py`, the loops here are OTAWA's own: in one container without
network, `mkff` lists the loop headers of the code reachable from each root function and
`dumpcfg --cfg-raw -S` gives the basic blocks (first and last address, successors) of each
function (the raw graph: in the tuned one, the blocks duplicated for an IT block lose their
incoming edges in this output; the loop headers are the same addresses).
A loop's body is the natural loop of its header in that graph (a call's synthetic block is
replaced by the block that follows the call), and it is matched with the source loops by
the rule of `wcet.py` (`wcet.Analysis.match`, from the lines of the loop's own instructions,
not in a nested loop, and the source loops' line ranges `loop_ends`): the innermost source
loop whose range holds those of its lines that lie in some source loop; the largest bound
if several source loops match; no flow fact, hence no WCET for the roots that reach it, if
none does or if the matched source loop has no bound. A source bound N (body executions per entry)
is written as `maxcount="N+1"` (executions of the header per entry), as in `run_otawa.py`.

Trusted, besides OTAWA itself and its processor model: that the compiler preserves the
source loops' iteration counts, as for `wcet.py`.
"""
import pathlib
import re
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import wcet as wcet_py  # noqa: E402  (this module has a function `wcet`)

OTAWA_BIN = "/tmp/otawa-install/bin"

# name -> (OTAWA script and parameters, description)
PROCESSORS = {
    "stm32f4": (["-s", "stm32", "-p", "ARCH=0"],
                "STM32F427, Cortex-M4 (OTAWA script stm32, ARCH=0: pipeline, no cache, the memory "
                "latencies of OTAWA's model, which its file says are not from the datasheet)"),
    "stm32h7": (["-s", "stm32", "-p", "ARCH=1"],
                "STM32H753, Cortex-M7 (OTAWA script stm32, ARCH=1: pipeline, caches and branch "
                "history table, as modelled by OTAWA)"),
}

LOOP = re.compile(r"^\s*loop .*// 0x([0-9a-fA-F]+)")
FUNC = re.compile(r"^// Function (\S+)")
BLOCK = re.compile(r"^(\d+) ([0-9a-fA-F]+) ([0-9a-fA-F]+)((?: -?\d+)*)$")
WCET = re.compile(r"^WCET\[(.*)\] = (\d+) cycles")


def docker(image, work, script, timeout):
    p = subprocess.run(["docker", "run", "--rm", "--network", "none", "-v", f"{work}:/w:ro",
                        image, "bash", "-c", script], capture_output=True, text=True, timeout=timeout)
    if p.returncode and not p.stdout:
        raise RuntimeError(f"docker run {image} failed: {p.stderr.strip()[-300:]}")
    return p.stdout


FUNHDR = re.compile(r"^([0-9a-f]+) <(.+)>:$")
INSN = re.compile(r"^\s+([0-9a-f]+):\s+(\S+)\s*(.*)$")
TARGET = re.compile(r"<([^<>+]+)(\+0x[0-9a-f]+)?>")


def call_graph(objdump, elf):
    """`parse_calls` on the disassembly of an executable, function ends from its symbols."""
    out = subprocess.run([objdump, "-d", "--no-show-raw-insn", elf], capture_output=True, text=True,
                         check=True).stdout
    nm = str(pathlib.Path(objdump).with_name(pathlib.Path(objdump).name.replace("objdump", "nm")))
    end = {}   # function -> end address (padding after it is not its code)
    for l in subprocess.run([nm, "-S", "--defined-only", elf], capture_output=True, text=True,
                            check=True).stdout.splitlines():
        f = l.split()
        if len(f) == 4 and f[2] in "Tt":
            end[f[3]] = (int(f[0], 16) & ~1) + int(f[1], 16)
    return parse_calls(out, end)


def parse_calls(out, end):
    """({function: callees}, {function: reason it is not supported}) from the disassembly
    `out` (llvm-objdump -d) of an ARM (Thumb) executable; `end`: function -> end address.
    Unsupported, conservatively: an indirect call or jump, a jump table (TBB/TBH), another
    write of the PC than a return, a branch into the middle of another function, a call into
    the middle of its own code (what a call of an undefined symbol becomes when linked
    anyway). A branch to the start of another function (a tail call) counts as a call."""
    calls, bad, cur = {}, {}, None
    for line in out.splitlines():
        m = FUNHDR.match(line)
        if m:
            cur = m.group(2)
            calls.setdefault(cur, set())
            continue
        m = INSN.match(line)
        if not m or cur is None or (cur in end and int(m.group(1), 16) >= end[cur]):
            continue
        op, args = m.group(2).lower(), m.group(3).split("@")[0].strip().lower()
        base = op.split(".")[0]
        t = TARGET.search(m.group(3))
        if base in ("tbb", "tbh"):
            bad.setdefault(cur, f"jump table at {m.group(1)}")
        elif base in ("blx", "bx") and not t:
            if not (base == "bx" and args == "lr"):
                bad.setdefault(cur, f"indirect {'call' if base == 'blx' else 'jump'} at {m.group(1)}")
        elif re.match(r"^(b|bl|blx|cbn?z)(eq|ne|cs|hs|cc|lo|mi|pl|vs|vc|hi|ls|ge|lt|gt|le|al)?$", base) and t:
            call = base in ("bl", "blx")
            if t.group(1) != cur:
                if t.group(2):
                    bad.setdefault(cur, f"branch into {t.group(1)}{t.group(2)} at {m.group(1)}")
                else:
                    calls[cur].add(t.group(1))
            elif call and t.group(2) is not None:
                bad.setdefault(cur, f"call into its own code at {m.group(1)} (an undefined symbol?)")
            elif call:
                calls[cur].add(cur)   # recursion
        elif re.match(r"^(pc\b|pc,)", args) and base not in ("pop", "ldm", "ldmia"):
            bad.setdefault(cur, f"write of the PC at {m.group(1)}")
    return calls, bad


def reachable(calls, root):
    seen, todo = set(), [root]
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.add(f)
        todo.extend(calls.get(f, ()))
    return seen


def unsupported_reason(reach, unsupported, missing, calls):
    """Why the functions `reach` (those reachable from a root) get no WCET, or None."""
    for f in sorted(reach):
        if f not in calls:
            return f"calls {f}, which has no code in the binary"
        if any(f in reachable(calls, g) for g in calls[f]):
            return f"{f} is recursive (no flow fact bounds its depth)"
        if f in unsupported:
            return f"{f}: {unsupported[f]}"
        if f in missing:
            return f"{f}: {missing[f]}"
    return None


def graphs(image, work, elf, roots, timeout=600):
    """({function: (blocks, loop headers)}, {root: functions reachable from it}) where
    blocks = {index: (first address, last address, [successor indices])}."""
    out = docker(image, work, "; ".join(f"echo '=== {r}'; {OTAWA_BIN}/mkff /w/{elf} {r} 2>/dev/null"
                                        for r in roots), timeout)
    heads, reach, root, cur = {}, {}, None, None
    for line in out.splitlines():
        if line.startswith("=== "):
            root = line[4:]
            reach[root] = set()
            continue
        m = FUNC.match(line)
        if m and root:
            cur = m.group(1)
            reach[root].add(cur)
            heads.setdefault(cur, set())
            continue
        m = LOOP.match(line)
        if m and cur:
            heads[cur].add(int(m.group(1), 16))
        elif line.startswith("// loop"):
            # a loop already bounded by a flow-fact file that OTAWA loaded by itself
            # (<binary>.ffx next to the binary): its header would be missed
            raise RuntimeError(f"mkff loaded flow facts next to {elf}; remove them: {line}")
    names = sorted(heads)
    out = docker(image, work, "; ".join(f"echo '!!! {f}'; {OTAWA_BIN}/dumpcfg --cfg-raw -S /w/{elf} {f} 2>/dev/null"
                                        for f in names), timeout) if names else ""
    cfgs, fn = {}, None
    for line in out.splitlines():
        if line.startswith("!!! "):
            fn = line[4:].strip()
            cfgs[fn] = {}
            continue
        m = BLOCK.match(line)
        if m and fn:
            succ = [int(x) for x in m.group(4).split()]
            cfgs[fn][int(m.group(1))] = (int(m.group(2), 16), int(m.group(3), 16), [x for x in succ if x >= 0])
    return {f: (cfgs.get(f, {}), heads[f]) for f in names}, reach


def natural_loops(blocks):
    """{header address: (body block indices, latch block indices)}."""
    if not blocks:
        return {}
    idx = sorted(blocks)
    succ = {}
    for b in idx:
        first, last, ss = blocks[b]
        out = []
        for s in ss:
            if s in blocks:
                out.append(s)
            else:   # a call (synthetic block): continue at the block after it
                nxt = [c for c in idx if blocks[c][0] > last]
                if nxt:
                    out.append(min(nxt, key=lambda c: blocks[c][0]))
        succ[b] = out
    entry = min(idx)
    pred = {b: [] for b in idx}
    for b in idx:
        for s in succ[b]:
            pred[s].append(b)
    dom = {b: set(idx) for b in idx}
    dom[entry] = {entry}
    changed = True
    while changed:
        changed = False
        for b in idx:
            if b == entry:
                continue
            ps = [dom[p] for p in pred[b]]
            new = ({b} | set.intersection(*ps)) if ps else {b}
            if new != dom[b]:
                dom[b], changed = new, True
    loops = {}
    for u in idx:
        for h in succ[u]:
            if h in dom[u]:
                body, latches = loops.setdefault(blocks[h][0], ({h}, set()))
                latches.add(u)
                stack = [u]
                while stack:
                    x = stack.pop()
                    if x not in body:
                        body.add(x)
                        stack.extend(pred[x])
    return loops


def flow_facts(funcs, lines, loop_bounds, loop_ends=None):
    """(FFX text, {function: reason it has a loop without a flow fact}). `loop_ends`: source
    loop -> its last line (the plugin's `end_line`), as for `wcet.Analysis`."""
    facts, missing = [], {}
    matcher = wcet_py.Analysis(None, {}, loop_bounds, loop_ends)
    for fn, (blocks, heads) in sorted(funcs.items()):
        loops = natural_loops(blocks)
        entry = blocks[min(blocks)][0] if blocks else None
        for h in sorted(heads):
            if h not in loops:
                missing[fn] = f"loop at {h:#x}: no back edge found in OTAWA's graph"
                continue
            body, _latches = loops[h]
            inner = [g for g in loops if g != h and loops[g][0] < body]
            own = body - set().union(*[loops[g][0] for g in inner]) if inner else body
            own_lines = {lines[a] for b in own for a in range(blocks[b][0], blocks[b][1] + 1) if a in lines}
            found = matcher.match(own_lines)
            if not found:
                missing[fn] = f"loop at {h:#x} matches no source loop"
                continue
            bs = [loop_bounds[l] for l in found]
            if any(b is None for b in bs):
                missing[fn] = f"loop at {h:#x} matches a source loop without a bound"
                continue
            facts.append(f'  <loop label="{fn}" offset="{h - entry:#x}" maxcount="{max(bs) + 1}"/>')
    return '<?xml version="1.0"?>\n<flowfacts>\n' + "\n".join(facts) + "\n</flowfacts>\n", missing


def wcet(image, work, elf, ffx, roots, processor, timeout=600):
    """{root: cycles or None, 'error ...'}"""
    params = " ".join(PROCESSORS[processor][0])
    script = "; ".join(f"echo '=== {r}'; timeout {int(timeout)} {OTAWA_BIN}/owcet {params} /w/{elf} {r} "
                       f"-f /w/{ffx} 2>&1 | grep -E '^WCET|^ERROR' | head -3" for r in roots)
    out = docker(image, work, script, timeout * max(1, len(roots)) + 60)
    res, cur = {}, None
    for line in out.splitlines():
        if line.startswith("=== "):
            cur = line[4:]
            res[cur] = (None, "no result from OTAWA")
        m = WCET.match(line)
        if m and cur:
            res[cur] = (int(m.group(2)), None)
        elif line.startswith("ERROR") and cur and res[cur][0] is None:
            res[cur] = (None, line[:160])
    return res
