# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Cycle bounds of the functions of a Cortex-M0 binary, from source loop bounds.

For each function: the control-flow graph is rebuilt from the code reachable from its
entry (`m0.decode`); it must be reducible, without indirect jumps. Its natural loops are
matched with the source loops through the debug line table: a binary loop takes the
bound of the innermost source loop whose line range (from the report's `end_line`) holds
the lines of its own instructions (those not in a nested loop) that lie in some source
loop; if no source loop holds them all, the largest bound of the source loops whose line
occurs; if none, the function is not bounded (`Analysis.match`).
A source loop bound `N` (from CrossCheck: at most `N` executions of the body per entry)
bounds the traversals of the binary loop's back edges per entry. The bound is the timing
schema on the binary: a loop costs `N * (longest iteration) + (longest exit path)`, inner
loops collapsed first; a call costs the callee's bound. Conditional branches are counted
as taken.

Trusted: the timing table (`m0.cycles`), and that the compiler preserves the source
loops' iteration counts (a binary loop iterates at most as often as the source loop it is
matched with). `run_cycles.py` checks both bounds against executions.
"""
import re
import subprocess

import m0

LINE = re.compile(r"^; (.*):(\d+)(?: \(discriminator \d+\))?$")
ROW = re.compile(r"^0x([0-9a-f]+)\s+(\d+)\s+\d+\s+\d+\s+\d+\s+\d+\s+\d+\s*(.*)$")


def zero_ranges(objdump, obj):
    """The address ranges of the line table's rows with line 0 (code the compiler attributes
    to no source line), from llvm-dwarfdump next to `objdump`: llvm-objdump --line-numbers
    does not print these rows, and the previous line would otherwise be carried over to that
    code (in Clang's matrix1, the set-up of a loop nest got the line of an earlier loop)."""
    import pathlib
    import shutil
    dd = pathlib.Path(objdump).with_name("llvm-dwarfdump")
    dd = str(dd) if dd.exists() else shutil.which("llvm-dwarfdump")
    if dd is None:
        raise RuntimeError("llvm-dwarfdump not found (needed for the rows with line 0)")
    out = subprocess.run([dd, "--debug-line", obj], capture_output=True, text=True, check=True).stdout
    ranges, prev = [], None
    for l in out.splitlines():
        m = ROW.match(l)
        if not m:
            continue
        a, line, flags = int(m.group(1), 16), int(m.group(2)), m.group(3)
        if prev is not None and prev[1] == 0 and a > prev[0]:
            ranges.append((prev[0], a))
        prev = None if "end_sequence" in flags else (a, line)
    return ranges
INSN = re.compile(r"^\s+([0-9a-f]+):\s")


def line_table(objdump, obj, src_name, base=0):
    """address - base -> source line, for the lines of `src_name` (inlined code included).
    With several names (a list), the lines are pairs (name, line)."""
    names = [src_name] if isinstance(src_name, str) else list(src_name)
    out = subprocess.run([objdump, "-d", "--line-numbers", "--no-show-raw-insn", obj],
                         capture_output=True, text=True, check=True).stdout
    zero = zero_ranges(objdump, obj)
    table, cur = {}, None
    for l in out.splitlines():
        m = LINE.match(l)
        if m:
            nm = next((n for n in names if m.group(1) == n or m.group(1).endswith("/" + n)), None)
            cur = None if nm is None else int(m.group(2)) if isinstance(src_name, str) else (nm, int(m.group(2)))
            continue
        m = INSN.match(l)
        if m and cur is not None:
            a = int(m.group(1), 16)
            if not any(lo <= a < hi for lo, hi in zero):
                table[a - base] = cur
    return table


_ABSENT = object()      # no record of the function in `Analysis.loops`


class Unbounded(Exception):
    pass



def acyclic(entry, succ):
    """No cycle reachable from `entry` in the graph `succ` (iterative depth-first search, so
    that large functions do not exhaust Python's recursion limit)."""
    state = {entry: 1}
    stack = [(entry, iter(succ[entry]))]
    while stack:
        b, it = stack[-1]
        for s in it:
            if state.get(s) == 1:
                return False
            if s not in state:
                state[s] = 1
                stack.append((s, iter(succ[s])))
                break
        else:
            state[b] = 2
            stack.pop()
    return True


def dag_longest(start, kids, cost, is_target):
    """Longest path from `start` to a node where `is_target` holds, in a DAG given by `kids`:
    the cost of a path is the sum of the costs of its nodes; None if no target is reachable.
    Iterative (post-order with an explicit stack)."""
    memo = {}
    stack = [(start, False)]
    while stack:
        x, done = stack.pop()
        if x in memo:
            continue
        ks = kids(x)
        if not done:
            stack.append((x, True))
            stack.extend((k, False) for k in ks if k not in memo)
            continue
        best = cost(x) if is_target(x) else None
        for k in ks:
            r = memo[k]
            if r is not None:
                best = max(best or 0, cost(x) + r)
        memo[x] = best
    return memo[start]

class Analysis:
    def __init__(self, img, lines, loop_bounds, loop_ends=None):
        """`loop_bounds`: source line -> iteration bound (None: no bound); `loop_ends`: source
        line -> last line of that loop (its body included; missing: the loop's own line)."""
        self.img, self.lines, self.loop_bounds = img, lines, loop_bounds
        self.loop_ends = loop_ends or {}
        self.memo, self.active = {}, set()
        self.loops = {}      # function -> [(header, matched line, bound)]
        self.why = {}
        self.jumps = {}      # function -> {address of a jump through a table: (start, targets, ix[, vr])}
        # jumps whose index is bounded by the invariant (`jumptable.inv_candidates`): their
        # targets come from the loop analysis of the function's graph, which needs them;
        # `cfg` iterates until they are stable (`_resolve_jumps`). `jt_opts`: the
        # assumptions of that analysis (abi, frame), those of the loop certificates.
        self.jt_opts = (False, False)
        self.jt_guess = {}   # function -> {jump: (start, targets, p, (d, lo, hi))}
        self.jt_cands = {}   # function -> {jump: [(start, p, d)]}
        self.jt_failed = {}  # function -> reason
        self.jt_resolving = set()

    def _within(self, k, l):
        """Line `l` lies in the source loop of line `k` (keys: lines, or (file, line) pairs)."""
        end = self.loop_ends.get(k)
        if isinstance(k, tuple):
            return isinstance(l, tuple) and l[0] == k[0] and k[1] <= l[1] <= (end or k[1])
        return not isinstance(l, tuple) and k <= l <= (end or k)

    def match(self, own):
        """The source loops a binary loop is matched with, from the lines of its own
        instructions (those not in a nested binary loop): of the lines that lie in some source
        loop, the innermost source loop that holds all of them (several if they have the same
        lines); if none holds them all, every source loop whose own line occurs (the largest
        bound is then taken). Lines outside every loop (e.g. the function's first line, kept
        by the compiler for code it moved) are ignored."""
        if set(self.loop_bounds) == {None}:   # every loop, one bound (binloops.structure)
            return {None}
        keys = [k for k in self.loop_bounds if k is not None]
        inside = {l for l in own if l is not None and any(self._within(k, l) for k in keys)}
        if not inside:
            return set()
        hold = [k for k in keys if all(self._within(k, l) for l in inside)]
        if not hold:
            return inside & set(keys)
        span = lambda k: (self.loop_ends.get(k) or (k[1] if isinstance(k, tuple) else k)) - (k[1] if isinstance(k, tuple) else k)
        best = min(span(k) for k in hold)
        return {k for k in hold if span(k) == best}

    def function(self, name):
        if name in self.memo:
            return self.memo[name]
        if name in self.active:
            raise Unbounded(f"recursion through {name}")
        self.active.add(name)
        try:
            res = self._function(name)
            self.memo[name] = res
            return res
        except Unbounded as e:
            self.memo[name] = None
            self.why[name] = str(e)
            return None
        finally:
            self.active.discard(name)

    def callee_cost(self, target):
        if target in self.img.undefined:
            raise Unbounded(f"call to {self.img.undefined[target]} (no code)")
        name = next((n for n, (a, _) in self.img.funcs.items() if a == target), None)
        if name is None:
            raise Unbounded(f"call to an unknown address {target:#x}")
        c = self.function(name)
        if c is None:
            raise Unbounded(f"call to {name}, which is not bounded")
        return c

    def cfg(self, name):
        """The control-flow graph of a function: entry, blocks (address -> instructions),
        successors (address -> block addresses); raises Unbounded if unsupported."""
        entry, size = self.img.funcs[name]
        mem = self.img.mem
        # reachable instructions and basic blocks
        insns, todo, leaders = {}, [entry], {entry}
        while todo:
            a = todo.pop()
            if a in insns:
                continue
            i = m0.decode(mem, a)
            insns[a] = i
            if i.kind == "indirect":
                # a jump through a table, if its window is recognised (jumptable.py)
                import jumptable
                within = (entry, entry + max(size, 2))
                jt = jumptable.find(jumptable.getter(self.img), a, within=within)
                if jt is None or not all(entry <= t < entry + max(size, 2) for t in jt[1]):
                    jt = self._inv_jump(name, a, within)
                self.jumps.setdefault(name, {})[a] = jt
                for t in jt[1]:
                    leaders.add(t)
                    todo.append(t)
                continue
            if i.kind == "stop":
                raise Unbounded(f"{i.op} at {a:#x} (indirect jump or unsupported instruction)")
            if i.kind in ("cond", "jump"):
                if not (entry <= i.target < entry + max(size, 2)):
                    raise Unbounded(f"jump out of the function at {a:#x}")
                leaders.add(i.target)
                todo.append(i.target)
            if i.kind in ("cond", "seq", "call"):
                todo.append(a + i.size)
            if i.kind == "cond":
                leaders.add(a + i.size)
        order = sorted(insns)
        blocks, succ = {}, {}
        cur = None
        for a in order:
            if a in leaders or cur is None:
                cur = a
                blocks[cur] = []
            blocks[cur].append(insns[a])
            i = insns[a]
            if i.kind in ("cond", "jump", "ret", "indirect") or (a + i.size) in leaders:
                cur = None
        for b, il in blocks.items():
            last = il[-1]
            s = []
            if last.kind in ("cond", "jump"):
                s.append(last.target)
            if last.kind in ("cond", "seq", "call"):
                s.append(last.addr + last.size)
            if last.kind == "indirect":
                s.extend(self.jumps[name][last.addr][1])
            succ[b] = [x for x in s if x in blocks]
        if self.jt_cands.get(name) and name not in self.jt_resolving and name not in self.jt_failed \
                and set(self.jt_cands[name]) - set(self.jt_guess.get(name, {})):
            self._resolve_jumps(name)
            return self.cfg(name)
        return entry, blocks, succ

    def _inv_jump(self, name, a, within):
        """The jump at `a` bounded by the invariant: its targets found so far (none at first),
        or Unbounded."""
        import jumptable
        i = m0.decode(self.img.mem, a)
        if name in self.jt_failed:
            raise Unbounded(f"{i.op} at {a:#x} (jump through a table: {self.jt_failed[name]})")
        g = self.jt_guess.get(name, {}).get(a)
        if g is not None:
            return g
        cands = jumptable.inv_candidates(jumptable.getter(self.img), a, within=within)
        if not cands:
            raise Unbounded(f"{i.op} at {a:#x} (indirect jump or unsupported instruction)")
        self.jt_cands.setdefault(name, {})[a] = cands
        return (None, [], None, None)

    JT_ROUNDS = 6

    def _resolve_jumps(self, name):
        """Targets of the jumps bounded by the invariant: the loop analysis of the graph with
        the targets found so far bounds each index (`binloops.inv_jumps`), until the targets
        are stable; failure makes the function unbounded."""
        import binloops
        self.jt_resolving.add(name)
        try:
            for _ in range(self.JT_ROUNDS):
                self.cfg(name)          # records the candidates of the jumps reached
                cands = self.jt_cands.get(name, {})
                res, why = binloops.inv_jumps(self, name, cands, *self.jt_opts)
                if res is None:
                    self.jt_failed[name] = why
                    return
                old = self.jt_guess.get(name, {})
                if res == old and set(res) == set(cands):
                    return
                self.jt_guess[name] = res
            self.jt_failed[name] = "its targets are not stable"
        finally:
            self.jt_resolving.discard(name)

    def _function(self, name):
        entry, blocks, succ = self.cfg(name)
        cost = {}
        for b, il in blocks.items():
            c = 0
            for i in il:
                c += m0.cycles(i, True)
                if i.kind == "call":
                    c += self.callee_cost(i.target)
            cost[b] = c
        return self._schema(name, entry, blocks, succ, cost)

    def loop_structure(self, name, entry, blocks, succ):
        """Natural loops of a reducible graph, matched with source loops: (pred, back edges,
        loop bodies by header, headers innermost first, parent loop, bound by header).
        Records `self.loops[name]`; raises Unbounded if a loop has no bound. Remembered per
        function for the same graph (its blocks, their instructions' addresses and its
        edges; `cfg` builds a new graph at each call): the same result, exception and record
        of `self.loops[name]` (the callers only read the result)."""
        key = (entry, tuple((b, tuple(i.addr for i in il)) for b, il in blocks.items()),
               tuple((b, tuple(x)) for b, x in succ.items()))
        memo = self.__dict__.setdefault("_ls_memo", {})
        hit = memo.get(name)
        if hit is None or hit[0] != key:
            before = self.loops.get(name, _ABSENT)
            try:
                res, err = self._loop_structure(name, entry, blocks, succ), None
            except Unbounded as e:
                res, err = None, e
            rec = self.loops.get(name, _ABSENT)
            hit = memo[name] = (key, res, err, None if rec is before else list(rec))
        _key, res, err, rec = hit
        if rec is not None:
            self.loops[name] = list(rec)
        if err is not None:
            raise Unbounded(str(err))
        return res

    def _loop_structure(self, name, entry, blocks, succ):
        nodes = list(blocks)
        pred = {b: [] for b in nodes}
        for b in nodes:
            for s in succ[b]:
                pred[s].append(b)
        # dominators
        dom = {b: set(nodes) for b in nodes}
        dom[entry] = {entry}
        changed = True
        while changed:
            changed = False
            for b in nodes:
                if b == entry:
                    continue
                ps = [dom[p] for p in pred[b]]
                new = ({b} | set.intersection(*ps)) if ps else {b}
                if new != dom[b]:
                    dom[b], changed = new, True
        back = [(u, h) for u in nodes for h in succ[u] if h in dom[u]]
        # reducible: the graph without back edges is acyclic
        back_set = set(back)
        fwd = {b: [s for s in succ[b] if (b, s) not in back_set] for b in nodes}
        if not acyclic(entry, fwd):
            raise Unbounded("irreducible control flow")
        loops = {}
        for u, h in back:
            body = loops.setdefault(h, {h})
            stack = [u]
            while stack:
                x = stack.pop()
                if x not in body:
                    body.add(x)
                    stack.extend(pred[x])
        headers = sorted(loops, key=lambda h: len(loops[h]))  # innermost first
        parent = {}
        for h in headers:
            outer = [g for g in headers if g != h and h in loops[g] and loops[h] <= loops[g]]
            parent[h] = min(outer, key=lambda g: len(loops[g])) if outer else None
        self.loops[name] = []
        bound = {}
        for h in headers:
            body = loops[h]
            inner = [g for g in headers if parent.get(g) == h]
            own = body - set().union(*[loops[g] for g in inner]) if inner else body
            # By the line ranges of the source loops (`match`). Trying the lines of the back
            # edges and of the header first, as before 2026-11-21, is wrong for rotated loops:
            # in GCC's fft_bit_reduct the outer loop's header holds the test of the inner
            # loop (bound 11 instead of 1024).
            lines = self.match({self.lines.get(i.addr) for b in own for i in blocks[b]})
            cands = [self.loop_bounds[l] for l in lines if l in self.loop_bounds]
            if not cands:
                raise Unbounded(f"binary loop at {h:#x} matches no source loop (lines {sorted(lines)})")
            if any(c is None for c in cands):
                raise Unbounded(f"binary loop at {h:#x} matches a source loop without a bound")
            N = max(cands)
            self.loops[name].append((h, sorted(l for l in lines if l in self.loop_bounds), N, set().union(*[set(i.addr for i in blocks[b]) for b in body])))
            bound[h] = N
        return pred, back, loops, headers, parent, bound

    def _schema(self, name, entry, blocks, succ, cost):
        nodes = list(blocks)
        pred, back, loops, headers, parent, bound = self.loop_structure(name, entry, blocks, succ)
        # collapsed graph: a node is a block or an inner loop (by its header)
        rep = {b: b for b in nodes}   # block -> representative node
        ncost = dict(cost)
        nsucc = {b: list(succ[b]) for b in nodes}
        for h in headers:
            body = loops[h]
            N = bound[h]
            members = {rep[b] for b in body}
            latches = {rep[u] for u, hh in back if hh == h}
            exits = [(rep[u], v) for u in body for v in succ[u] if v not in body]

            def longest(target_test):
                def kids(x):
                    return [rep.get(s, s) for s in nsucc[x]
                            if s != h and rep.get(s, s) in members and rep.get(s, s) != x]
                return dag_longest(h, kids, lambda x: ncost[x], target_test)

            p_iter = longest(lambda x: x in latches) or 0
            exit_nodes = {x for x, _ in exits}
            p_exit = longest(lambda x: x in exit_nodes) or 0
            ncost[h] = N * p_iter + p_exit
            nsucc[h] = sorted({v for _, v in exits})
            for b in body:
                rep[b] = h
            for x in members:
                if x != h:
                    ncost.pop(x, None)
                    nsucc.pop(x, None)
        # longest path from the entry to a return, on the collapsed DAG
        res = dag_longest(rep[entry], lambda x: [rep[s] for s in nsucc[x]], lambda x: ncost[x],
                          lambda x: not nsucc[x])
        if res is None:
            raise Unbounded("no path to a return")
        return res
