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
another way than from a known register, jumps out of its code, is recursive, or calls a
function without code (the software floating-point helpers, which the interpreter provides
in Python).

Known registers: along with the depth, every instruction gets the registers whose value is
known on every path that reaches it, either a constant of the literal pool (`ldr r, =c`) or
the stack pointer at entry minus a constant (`add r7, sp, #i`, `mov r, sp`, then `adds`,
`subs` by constants, `mov` between registers). Where paths meet, a register stays known only
if its value is the same on all of them. `add sp, r` with `r` a known constant (a frame
larger than `sub sp, #imm` can express, `ldr r, =-size; add sp, r`) and `mov sp, r` with `r`
known relative to the entry (the stack pointer restored from the frame pointer, `subs r6,
r7, #12; mov sp, r6`) set the depth. A call keeps a register known only if the callee
preserves it on its code (`preserved`): it saves it with its entry `push` and every return
pops it again, or neither it nor its callees write it; this assumes, as the calling
convention does, that the saved words are not overwritten during the call.

Unlike a cycle bound, a stack bound needs no loop bound: a loop does not move the stack
pointer from one iteration to the next (checked: one depth per instruction). It is a
high-water mark, a maximum over paths where time is a sum (Lean: `ImperativeOptimization.
Stack`). Interrupt frames are not counted: the runs take no interrupt.
"""
import struct

import m0


class NoBound(Exception):
    pass


class StackAnalysis:
    def __init__(self, img, jumps=None):
        """`jumps`: the jumps through tables found by `wcet.Analysis` (`Analysis.jumps`),
        for those whose index only the loop analysis bounds."""
        self.img = img
        self.jumps = jumps or {}
        self.memo, self.active, self.why = {}, set(), {}
        self.frame = {}  # function -> its own largest depth, callees excluded
        self.keeps = {}  # function -> registers among r4-r11 it leaves unchanged

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

    def preserved(self, target):
        """Registers among r4-r11 that the function at `target` leaves unchanged, from
        its code: those its entry `push` saves and every `pop` that returns restores, with
        no other `pop` of them; or that neither it nor its callees write. Empty when it
        has no code or no stack bound."""
        name = next((n for n, (a, _) in self.img.funcs.items() if a == target), None)
        if name is None or self.function(name) is None:
            return frozenset()
        return self.keeps.get(name, frozenset())

    def _function(self, name):
        entry, size = self.img.funcs[name]
        within = (entry, entry + max(size, 2))
        mem = self.img.mem
        # state at an address: (depth, {register: ("c", constant) | ("sp", k)}), where
        # ("sp", k) is the stack pointer at entry minus k
        state, todo = {entry: (0, {})}, [entry]
        worst = own = 0
        written, saved, rets = set(), None, []
        first = m0.decode(mem, entry)
        if first.op == "push":
            saved = {r for r in first.a[0] if 4 <= r <= 11}
        while todo:
            a = todo.pop()
            d, regs = state[a]
            i = m0.far_branch(m0.decode(mem, a), within[0], within[1] - within[0])
            jt = None
            if i.kind == "indirect":
                import jumptable
                jt = jumptable.find(jumptable.getter(self.img), a, within=within)
                known = self.jumps.get(name, {}).get(a)
                if jt is None and known is not None and known[0] is not None:
                    jt = known
            if i.kind == "stop" or (i.kind == "indirect" and jt is None):
                raise NoBound(f"{i.op} at {a:#x} (indirect jump or unsupported instruction)")
            out = dict(regs)
            w = writes(i)
            for r in w:
                out.pop(r, None)
            if i.op == "push":
                nd = d + 4 * len(i.a[0])
            elif i.op == "pop":
                nd = d - 4 * len(i.a[0])
                if i.kind != "ret":
                    rets.append(None)  # a pop that does not return: not followed
            elif i.op == "subsp":
                nd = d + i.a[0]
            elif i.op == "addsp":
                nd = d - i.a[0]
            elif i.op == "addhi" and i.a[0] == 13 and regs.get(i.a[1], ("",))[0] == "c":
                c = regs[i.a[1]][1]
                nd = d - (c - (1 << 32) if c & (1 << 31) else c)
            elif i.op == "movhi" and i.a[0] == 13 and regs.get(i.a[1], ("",))[0] == "sp":
                nd = regs[i.a[1]][1]
            elif i.op in ("addhi", "movhi") and i.a[0] == 13:
                raise NoBound(f"{i.op} writes the stack pointer at {a:#x}")
            else:
                nd = d
            if nd < 0:
                raise NoBound(f"the stack pointer rises above its entry value at {a:#x}")
            v = value(i, d, regs, mem)
            if v is not None:
                out[i.a[0]] = v
            written |= w
            own = max(own, nd)
            worst = max(worst, nd)
            if i.kind == "call":
                worst = max(worst, d + self.callee(i.target))
                keep = self.preserved(i.target)
                written |= set(range(4, 12)) - keep
                out = {r: x for r, x in out.items() if r in keep}
            if i.kind == "ret":
                rets.append(i)
                if nd != 0:
                    raise NoBound(f"return at {a:#x} with {nd} bytes still on the stack")
                continue
            succ = []
            if i.kind in ("cond", "jump"):
                if not (within[0] <= i.target < within[1]):
                    raise NoBound(f"jump out of the function at {a:#x}")
                succ.append(i.target)
            if i.kind in ("cond", "seq", "call"):
                succ.append(a + i.size)
            if jt is not None:
                if not all(within[0] <= t < within[1] for t in jt[1]):
                    raise NoBound(f"jump out of the function at {a:#x}")
                succ.extend(jt[1])
            for s in succ:
                if s in state:
                    sd, sr = state[s]
                    if sd != nd:
                        raise NoBound(f"two stack depths ({sd} and {nd}) reach {s:#x}")
                    joined = {r: x for r, x in sr.items() if out.get(r) == x}
                    if joined != sr:
                        state[s] = (nd, joined)
                        todo.append(s)
                else:
                    state[s] = (nd, out)
                    todo.append(s)
        # registers this function leaves unchanged for its callers
        keep = set(range(4, 12)) - written
        if saved is not None and all(p is not None and p.op == "pop"
                                     and set(p.a[0]) & set(range(4, 12)) == saved for p in rets):
            keep |= saved
        self.keeps[name] = frozenset(keep)
        self.frame[name] = own
        return worst


def writes(i):
    """Registers r0-r12 and lr that instruction `i` may write (the stack pointer and the
    PC apart)."""
    op, a = i.op, i.a
    if op in ("cmpi", "cmphi", "tst", "cmp", "cmn", "push", "nop", "bcond", "b",
              "subsp", "addsp") or op.startswith("str"):
        return set()
    if op == "stm":
        return {a[0]}
    if op == "ldm":
        return set(a[1]) | {a[0]}
    if op == "pop":
        return set(a[0]) - {15}
    if op == "bl":
        return {0, 1, 2, 3, 12, 14}
    if a and isinstance(a[0], int):
        return {a[0]} - {13, 15}
    return set(range(15)) - {13}


def value(i, d, regs, mem):
    """The value instruction `i` leaves in its first operand, if known: ("c", constant)
    from the literal pool, or ("sp", k), the stack pointer at entry minus k, when the
    stack pointer is `d` bytes below its entry value before `i`."""
    op, a = i.op, i.a
    if op == "ldrlit":
        return ("c", struct.unpack_from("<I", mem, ((i.addr + 4) & ~3) + a[1])[0])
    if op == "addspi":
        return ("sp", d - a[1])
    if op == "movhi" and a[0] != 13:
        return ("sp", d) if a[1] == 13 else regs.get(a[1])
    if op == "lsli" and a[2] == 0:  # movs rd, rm
        return regs.get(a[1])
    if op in ("addi3", "subi3"):
        src, k = a[1], (a[2] if op == "addi3" else -a[2])
    elif op in ("addi8", "subi8"):
        src, k = a[0], (a[1] if op == "addi8" else -a[1])
    else:
        return None
    x = regs.get(src)
    return ("sp", x[1] - k) if x is not None and x[0] == "sp" else None
