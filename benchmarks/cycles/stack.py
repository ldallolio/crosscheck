# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
"""Stack bounds of the functions of a Cortex-M0 binary.

The stack used by a function is the largest depth of the stack pointer below its value
at the function's entry, over all paths, calls included:

    stack(f) = max over the instructions a of f of
                   depth(a)                      (bytes pushed or reserved before and by a)
                   depth(a) + stack(g)           if a calls g

`depth` is computed on the control-flow graph of the binary: `push` and `sub sp` increase
it, `pop` and `add sp` decrease it, and it must have one value at every instruction (the
same along every path that reaches it) and be 0 where the function returns. A function
is given no bound (with the reason) when this fails, when it writes the stack pointer in
another way, jumps out of its code, is recursive, or calls a function without code (the
software floating-point helpers, which the interpreter provides in Python).

Unlike a cycle bound, a stack bound needs no loop bound: a loop does not move the stack
pointer from one iteration to the next (checked: one depth per instruction). It is a
high-water mark, a maximum over paths where time is a sum (Lean: `ImperativeOptimization.
Stack`). Interrupt frames are not counted: the runs take no interrupt.
"""
import m0


class NoBound(Exception):
    pass


class StackAnalysis:
    def __init__(self, img):
        self.img = img
        self.memo, self.active, self.why = {}, set(), {}
        self.frame = {}  # function -> its own largest depth, callees excluded

    def function(self, name):
        if name in self.memo:
            return self.memo[name]
        if name in self.active:
            raise NoBound(f"recursion through {name}")
        self.active.add(name)
        try:
            res = self._function(name)
        except NoBound as e:
            res = None
            self.why[name] = str(e)
        finally:
            self.active.discard(name)
        self.memo[name] = res
        return res

    def callee(self, target):
        if target in self.img.undefined:
            raise NoBound(f"call to {self.img.undefined[target]} (no code)")
        name = next((n for n, (a, _) in self.img.funcs.items() if a == target), None)
        if name is None:
            raise NoBound(f"call to an unknown address {target:#x}")
        s = self.function(name)
        if s is None:
            raise NoBound(f"call to {name}, which has no stack bound")
        return s

    def _function(self, name):
        entry, size = self.img.funcs[name]
        mem = self.img.mem
        depth, todo = {entry: 0}, [entry]
        worst = own = 0
        while todo:
            a = todo.pop()
            d = depth[a]
            i = m0.decode(mem, a)
            if i.kind in ("stop", "indirect"):
                raise NoBound(f"{i.op} at {a:#x} (indirect jump or unsupported instruction)")
            if i.op == "push":
                nd = d + 4 * len(i.a[0])
            elif i.op == "pop":
                nd = d - 4 * len(i.a[0])
            elif i.op == "subsp":
                nd = d + i.a[0]
            elif i.op == "addsp":
                nd = d - i.a[0]
            elif i.op in ("addhi", "movhi") and i.a[0] == 13:
                raise NoBound(f"{i.op} writes the stack pointer at {a:#x}")
            else:
                nd = d
            if nd < 0:
                raise NoBound(f"the stack pointer rises above its entry value at {a:#x}")
            own = max(own, nd)
            worst = max(worst, nd)
            if i.kind == "call":
                worst = max(worst, d + self.callee(i.target))
            if i.kind == "ret":
                if nd != 0:
                    raise NoBound(f"return at {a:#x} with {nd} bytes still on the stack")
                continue
            succ = []
            if i.kind in ("cond", "jump"):
                if not (entry <= i.target < entry + max(size, 2)):
                    raise NoBound(f"jump out of the function at {a:#x}")
                succ.append(i.target)
            if i.kind in ("cond", "seq", "call"):
                succ.append(a + i.size)
            for s in succ:
                if s in depth:
                    if depth[s] != nd:
                        raise NoBound(f"two stack depths ({depth[s]} and {nd}) reach {s:#x}")
                else:
                    depth[s] = nd
                    todo.append(s)
        self.frame[name] = own
        return worst
