# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Cycle bounds of the functions of a Cortex-M0 binary, from source loop bounds.

For each function: the control-flow graph is rebuilt from the code reachable from its
entry (`m0.decode`); it must be reducible, without indirect jumps. Its natural loops are
matched with the source loops through the debug line table: a binary loop takes the
bound of the source loop whose line occurs among its own instructions (those not in a
nested loop), the lines of the back-edge branches (the loop test or the jump back) being
tried first, then those of the header; if several match, the largest bound; if none, the function is not
bounded.
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

LINE = re.compile(r"^; (.*):(\d+)$")
INSN = re.compile(r"^\s+([0-9a-f]+):\s")


def line_table(objdump, obj, src_name, base=0):
    """address - base -> source line, for the lines of `src_name` (inlined code included).
    With several names (a list), the lines are pairs (name, line)."""
    names = [src_name] if isinstance(src_name, str) else list(src_name)
    out = subprocess.run([objdump, "-d", "--line-numbers", "--no-show-raw-insn", obj],
                         capture_output=True, text=True, check=True).stdout
    table, cur = {}, None
    for l in out.splitlines():
        m = LINE.match(l)
        if m:
            nm = next((n for n in names if m.group(1) == n or m.group(1).endswith("/" + n)), None)
            cur = None if nm is None else int(m.group(2)) if isinstance(src_name, str) else (nm, int(m.group(2)))
            continue
        m = INSN.match(l)
        if m and cur is not None:
            table[int(m.group(1), 16) - base] = cur
    return table


class Unbounded(Exception):
    pass


class Analysis:
    def __init__(self, img, lines, loop_bounds):
        """`loop_bounds`: source line -> iteration bound (None: no bound)."""
        self.img, self.lines, self.loop_bounds = img, lines, loop_bounds
        self.memo, self.active = {}, set()
        self.loops = {}      # function -> [(header, matched line, bound)]
        self.why = {}

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
            if i.kind in ("stop", "indirect"):
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
            if i.kind in ("cond", "jump", "ret") or (a + i.size) in leaders:
                cur = None
        for b, il in blocks.items():
            last = il[-1]
            s = []
            if last.kind in ("cond", "jump"):
                s.append(last.target)
            if last.kind in ("cond", "seq", "call"):
                s.append(last.addr + last.size)
            succ[b] = [x for x in s if x in blocks]
        return entry, blocks, succ

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
        Records `self.loops[name]`; raises Unbounded if a loop has no bound."""
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
        fwd = {b: [s for s in succ[b] if (b, s) not in back] for b in nodes}
        state = {}

        def acyclic(b):
            state[b] = 1
            for s in fwd[b]:
                if state.get(s) == 1 or (s not in state and not acyclic(s)):
                    return False
            state[b] = 2
            return True

        if not acyclic(entry):
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
            # The loop test is in the header or at the back edges: their lines first, then
            # all the loop's own instructions.
            latch_blocks = {u for u, hh in back if hh == h}
            lines = set()
            for key in ({self.lines.get(blocks[u][-1].addr) for u in latch_blocks},
                        {self.lines.get(i.addr) for i in blocks[h]},
                        {self.lines.get(i.addr) for b in own for i in blocks[b]}):
                lines = {l for l in key if l in self.loop_bounds}
                if lines:
                    break
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
                memo = {}

                def go(x):
                    if x in memo:
                        return memo[x]
                    best = ncost[x] if target_test(x) else None
                    for s in nsucc[x]:
                        if s == h or rep.get(s, s) not in members or rep.get(s, s) == x:
                            continue
                        r = go(rep.get(s, s))
                        if r is not None:
                            best = max(best or 0, ncost[x] + r)
                    memo[x] = best
                    return best

                return go(h)

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
        memo = {}

        def go(x):
            if x in memo:
                return memo[x]
            best = ncost[x] if not nsucc[x] else None
            for s in nsucc[x]:
                r = go(rep[s])
                if r is not None:
                    best = max(best or 0, ncost[x] + r)
            memo[x] = best
            return best

        res = go(rep[entry])
        if res is None:
            raise Unbounded("no path to a return")
        return res
