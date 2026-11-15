#!/usr/bin/env python3
# Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
"""Rust front-end of CrossCheck: translates the MIR of a Rust crate into C, which the
Clang-based analyser bounds (and certifies) as any C code.

    python3 frontends/rust/mir2c.py file.rs -o file.c      # needs rustc on $PATH

MIR is read as the text that `rustc --emit=mir -O -C overflow-checks=on -C panic=abort`
prints. That text is meant for humans and changes between Rust releases: this front-end
is written for rustc 1.100 and must be adjusted when the format changes (the tests in
`tests/` fail loudly when it does).

Fragment: free functions (no generics, closures, traits or methods) over integers, `bool`,
slices of integers (`&[T]`, `&mut [T]`: a pointer and a length), `Option` of an integer
(its payload), the tuples of checked arithmetic, and calls between such functions.
Anything else makes the function untranslated (with the reason, in a comment).

Semantics (what is assumed; `README.md`):
* MIR's `Add`, `Sub`, `Mul` wrap: wrapping C arithmetic (via the unsigned type);
* checked arithmetic (`AddWithOverflow` + `assert`) panics on overflow: translated to plain
  C arithmetic, which the analysis assumes not to overflow, i.e. the bound is for the
  executions that do not panic;
* every other `assert` (index in bounds, division by zero, user `assert!`) and every call
  of a function that does not return (panic) becomes `if (!(c)) return 0;`: the C program
  then has more behaviours than the Rust one (it continues where Rust stops), so its cost
  bounds also bound the Rust program, and the asserted fact holds afterwards;
* `usize`/`isize` are 64 bits (the host's).
"""
import argparse
import collections
import pathlib
import re
import subprocess
import sys

INT = {"i8": "int8_t", "i16": "int16_t", "i32": "int32_t", "i64": "int64_t", "isize": "int64_t",
       "u8": "uint8_t", "u16": "uint16_t", "u32": "uint32_t", "u64": "uint64_t", "usize": "uint64_t",
       "bool": "_Bool"}
UNSIGNED = {"i8": "uint8_t", "i16": "uint16_t", "i32": "uint32_t", "i64": "uint64_t", "isize": "uint64_t"}


class Unsupported(Exception):
    pass


# --- parsing --------------------------------------------------------------------------

class Fn:
    def __init__(self, name, params, ret):
        self.name, self.params, self.ret = name, params, ret   # params: [(local, type)]
        self.types = {}            # local -> Rust type
        self.debug = {}            # local -> source name
        self.blocks = collections.OrderedDict()   # bb -> (statements, terminator)


HEAD = re.compile(r"^fn (\w+)\((.*)\) -> (.+) \{$|^fn (\w+)\((.*)\) \{$")
LET = re.compile(r"^\s*let (?:mut )?(_\d+): (.+);$")
DEBUG = re.compile(r"^\s*debug (\w+) => (_\d+);$")
BB = re.compile(r"^\s*(bb\d+)(?: \(cleanup\))?: \{$")


def parse(text):
    fns, cur, bb, stmts = [], None, None, []
    depth = 0
    for raw in text.splitlines():
        line = raw.rstrip()
        if cur is None:
            m = HEAD.match(line)
            if m:
                name = m.group(1) or m.group(4)
                params = m.group(2) if m.group(1) else m.group(5)
                ret = m.group(3) if m.group(1) else "()"
                ps = []
                for p in split_top(params):
                    loc, ty = p.split(": ", 1)
                    ps.append((loc.strip(), ty.strip()))
                cur = Fn(name, ps, ret)
                for loc, ty in ps:
                    cur.types[loc] = ty
                cur.types["_0"] = ret
            elif line.startswith("fn "):
                fns.append(("skip", line))
            continue
        if line == "}" and bb is None:
            fns.append(cur)
            cur = None
            continue
        m = LET.match(line)
        if m and bb is None:
            cur.types[m.group(1)] = m.group(2)
            continue
        m = DEBUG.match(line)
        if m and bb is None:
            cur.debug[m.group(2)] = m.group(1)
            continue
        m = BB.match(line)
        if m:
            bb, stmts = m.group(1), []
            continue
        if bb is not None:
            s = line.strip()
            if s == "}":
                cur.blocks[bb] = (stmts[:-1], stmts[-1] if stmts else "unreachable;")
                bb = None
                continue
            if s.startswith("StorageLive") or s.startswith("StorageDead") or s == "nop;" \
                    or s.startswith("PlaceMention") or s.startswith("FakeRead") or s.startswith("AscribeUserType"):
                continue
            stmts.append(s)
    return [f for f in fns if isinstance(f, Fn)], [f[1] for f in fns if not isinstance(f, Fn)]


def split_top(s):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([<{":
            depth += 1
        elif ch in ")]>}":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


# --- types ------------------------------------------------------------------------------

def scalar(ty):
    return ty in INT


def slice_elem(ty):
    m = re.fullmatch(r"&(?:mut )?\[(\w+)\]", ty)
    return m.group(1) if m and scalar(m.group(1)) else None


def option_elem(ty):
    m = re.fullmatch(r"(?:std::option::|core::option::)?Option<(\w+)>", ty)
    return m.group(1) if m and scalar(m.group(1)) else None


def tuple_elem(ty):
    m = re.fullmatch(r"\((\w+), bool\)", ty)
    return m.group(1) if m and scalar(m.group(1)) else None


def ctype(ty):
    if scalar(ty):
        return INT[ty]
    raise Unsupported(f"type {ty}")


# --- translation of one function ----------------------------------------------------------

class Translator:
    def __init__(self, fn, known):
        self.fn, self.known = fn, known
        self.decls = {}

    def var(self, loc):
        return f"v{loc[1:]}" if loc != "_0" else "ret"

    def ty(self, loc):
        return self.fn.types[loc]

    # operands and places
    def place(self, p):
        p = p.strip()
        m = re.fullmatch(r"_\d+", p)
        if m:
            ty = self.ty(p)
            if slice_elem(ty):
                return self.var(p)
            if option_elem(ty):
                return self.var(p) + "_some"
            return self.var(p)
        m = re.fullmatch(r"\((_\d+)\.([01]): (\w+)\)", p)
        if m:
            loc, k = m.group(1), m.group(2)
            if not tuple_elem(self.ty(loc)):
                raise Unsupported(f"field of {self.ty(loc)}")
            return self.var(loc) + ("_val" if k == "0" else "_ovf")
        m = re.fullmatch(r"\(\((_\d+) as Some\)\.0: (\w+)\)", p)
        if m:
            return self.var(m.group(1)) + "_some"
        m = re.fullmatch(r"\(\*(_\d+)\)\[(_\d+)\]", p)
        if m:
            if not slice_elem(self.ty(m.group(1))):
                raise Unsupported(f"index into {self.ty(m.group(1))}")
            return f"{self.var(m.group(1))}[{self.var(m.group(2))}]"
        raise Unsupported(f"place {p}")

    def operand(self, o):
        o = o.strip()
        if o.startswith("copy ") or o.startswith("move "):
            return self.place(o[5:])
        m = re.fullmatch(r"const (-?\d+)_(\w+)", o)
        if m:
            v, t = int(m.group(1)), m.group(2)
            if t not in INT:
                raise Unsupported(f"constant {o}")
            if t in ("i64", "isize") and v == -(1 << 63):
                return "INT64_MIN"
            suffix = {"u64": "ull", "usize": "ull", "i64": "ll", "isize": "ll", "u32": "u"}.get(t, "")
            return f"(({INT[t]}){v}{suffix})"
        if o in ("const true", "const false"):
            return "1" if o.endswith("true") else "0"
        raise Unsupported(f"operand {o}")

    def optype(self, o):
        o = o.strip()
        if o.startswith("copy ") or o.startswith("move "):
            p = o[5:].strip()
            m = re.fullmatch(r"_\d+", p)
            if m:
                ty = self.ty(p)
                return option_elem(ty) or ty
            m = re.search(r": (\w+)\)$", p)
            if m:
                return m.group(1)
            m = re.fullmatch(r"\(\*(_\d+)\)\[_\d+\]", p)
            if m:
                return slice_elem(self.ty(m.group(1)))
        m = re.fullmatch(r"const -?\d+_(\w+)", o)
        if m:
            return m.group(1)
        if o in ("const true", "const false"):
            return "bool"
        return None

    @staticmethod
    def cast(t, e):
        """`e` (computed in C after the usual promotions) as a value of the Rust type `t`:
        no cast is needed for 32- and 64-bit operands, whose C type is already `t`'s."""
        if t in ("i32", "u32", "i64", "u64", "isize", "usize"):
            return e
        return f"({INT[t]}){e}"

    BIN = {"Add": "+", "Sub": "-", "Mul": "*", "Div": "/", "Rem": "%", "BitAnd": "&", "BitOr": "|",
           "BitXor": "^", "Shl": "<<", "Shr": ">>", "Eq": "==", "Ne": "!=", "Lt": "<", "Le": "<=",
           "Gt": ">", "Ge": ">=", "AddUnchecked": "+", "SubUnchecked": "-", "MulUnchecked": "*",
           "ShlUnchecked": "<<", "ShrUnchecked": ">>"}

    def rvalue(self, rv, dest_ty):
        rv = rv.strip()
        m = re.fullmatch(r"(\w+)\((.*)\)", rv)
        if m and m.group(1) in self.BIN or (m and m.group(1).endswith("WithOverflow")):
            op = m.group(1)
            args = split_top(m.group(2))
            if len(args) != 2:
                raise Unsupported(f"rvalue {rv}")
            a, b = self.operand(args[0]), self.operand(args[1])
            t = self.optype(args[0])
            base = op.replace("WithOverflow", "")
            sym = self.BIN[base]
            if op.endswith("WithOverflow"):
                # the overflow flag is only asserted false: plain arithmetic (no overflow)
                return ("tuple", self.cast(t, f"({a} {sym} {b})"))
            if base in ("Add", "Sub", "Mul"):
                # MIR's Add/Sub/Mul wrap: computed in an unsigned type of at least 32 bits
                # (narrower operands would be promoted to int, which may overflow)
                w = "uint64_t" if t in ("i64", "isize", "u64", "usize") else "uint32_t"
                return f"({INT[t]})(({w}){a} {sym} ({w}){b})"
            if base in ("Add", "Sub", "Mul", "Div", "Rem", "BitAnd", "BitOr", "BitXor", "Shl", "Shr") \
                    or base.endswith("Unchecked"):
                return self.cast(t, f"({a} {sym} {b})")
            return f"({a} {sym} {b})"
        m = re.fullmatch(r"Not\((.*)\)", rv)
        if m:
            t = self.optype(m.group(1))
            x = self.operand(m.group(1))
            return f"(!{x})" if t == "bool" else f"({INT[t]})(~{x})"
        m = re.fullmatch(r"Neg\((.*)\)", rv)
        if m:
            t = self.optype(m.group(1))
            return f"({INT[t]})(-{self.operand(m.group(1))})"
        m = re.fullmatch(r"PtrMetadata\((copy|move) (_\d+)\)", rv)
        if m:
            if not slice_elem(self.ty(m.group(2))):
                raise Unsupported(f"metadata of {self.ty(m.group(2))}")
            return f"{self.var(m.group(2))}_len"
        m = re.fullmatch(r"(.*) as (\w+) \((IntToInt|Transmute)\)", rv)
        if m and m.group(3) == "IntToInt":
            return f"({INT[m.group(2)]}){self.operand(m.group(1))}"
        m = re.fullmatch(r"(?:std::option::|core::option::)?Option::<\w+>::Some\((.*)\)", rv)
        if m:
            return ("some", self.operand(m.group(1)))
        if re.fullmatch(r"(?:std::option::|core::option::)?Option::<\w+>::None", rv):
            return ("none", None)
        m = re.fullmatch(r"discriminant\((_\d+)\)", rv)
        if m:
            return self.var(m.group(1)) + "_tag"
        return self.operand(rv)

    def statement(self, s):
        m = re.fullmatch(r"(.+?) = (.+);", s)
        if not m:
            raise Unsupported(f"statement {s}")
        lhs, rv = m.group(1), m.group(2)
        if re.fullmatch(r"_\d+", lhs):
            ty = self.ty(lhs)
            r = self.rvalue(rv, ty)
            if isinstance(r, tuple):
                kind, e = r
                v = self.var(lhs)
                if kind == "tuple":
                    return f"{v}_val = {e};"
                if kind == "some":
                    return f"{v}_tag = 1; {v}_some = {e};"
                return f"{v}_tag = 0;"
            if slice_elem(ty):
                m2 = re.fullmatch(r"(copy|move) (_\d+)", rv)
                if not m2:
                    raise Unsupported(f"slice value {rv}")
                return f"{self.var(lhs)} = {self.var(m2.group(2))}; {self.var(lhs)}_len = {self.var(m2.group(2))}_len;"
            return f"{self.place(lhs)} = {r};"
        r = self.rvalue(rv, None)
        if isinstance(r, tuple):
            raise Unsupported(f"statement {s}")
        return f"{self.place(lhs)} = {r};"

    def declare(self):
        out = []
        params = {p for p, _ in self.fn.params}
        for loc, ty in self.fn.types.items():
            if loc in params:
                continue
            v = self.var(loc)
            if ty in ("()", "!"):
                continue
            if scalar(ty):
                out.append(f"{INT[ty]} {v} = 0;")
            elif slice_elem(ty):
                c = INT[slice_elem(ty)]
                out.append(f"{c} *{v} = 0; uint64_t {v}_len = 0;")
            elif option_elem(ty):
                out.append(f"_Bool {v}_tag = 0; {INT[option_elem(ty)]} {v}_some = 0;")
            elif tuple_elem(ty):
                out.append(f"{INT[tuple_elem(ty)]} {v}_val = 0;")
            else:
                raise Unsupported(f"local of type {ty}")
        return out

    def signature(self):
        ps = []
        for loc, ty in self.fn.params:
            if scalar(ty):
                ps.append(f"{INT[ty]} {self.var(loc)}")
            elif slice_elem(ty):
                const = "" if ty.startswith("&mut") else "const "
                ps.append(f"{const}{INT[slice_elem(ty)]} *{self.var(loc)}")
                ps.append(f"uint64_t {self.var(loc)}_len")
            else:
                raise Unsupported(f"parameter of type {ty}")
        ret = self.fn.ret
        rt = "void" if ret == "()" else ctype(ret)
        return f"{rt} {self.fn.name}({', '.join(ps) or 'void'})"

    # --- control flow ---------------------------------------------------------------------

    def cfg(self):
        succ = {}
        for bb, (stmts, term) in self.fn.blocks.items():
            succ[bb] = targets(term)
        return succ

    def translate(self):
        self.succ = self.cfg()
        blocks = list(self.fn.blocks)
        self.entry = blocks[0]
        # skip blocks that only jump
        self.resolve = {}
        for bb in blocks:
            self.resolve[bb] = self.follow(bb)
        self.succ = {bb: [self.resolve[t] for t in ts] for bb, ts in self.succ.items()}
        self.compute_loops()
        self.compute_postdom()
        body = self.region(self.resolve[self.entry], None, None, indent="  ")
        lines = [self.signature() + " {"]
        lines += ["  " + d for d in self.declare()]
        lines += body
        if self.fn.ret != "()":
            pass
        lines.append("}")
        return "\n".join(lines)

    def follow(self, bb, seen=None):
        seen = seen or set()
        stmts, term = self.fn.blocks[bb]
        m = re.fullmatch(r"goto -> (bb\d+);", term)
        if not stmts and m and bb not in seen:
            seen.add(bb)
            return self.follow(m.group(1), seen)
        return bb

    def compute_loops(self):
        nodes = [b for b in self.fn.blocks if self.resolve[b] == b]
        entry = self.resolve[self.entry]
        pred = {b: [] for b in nodes}
        for b in nodes:
            for s in self.succ[b]:
                pred[s].append(b)
        dom = {b: set(nodes) for b in nodes}
        dom[entry] = {entry}
        changed = True
        while changed:
            changed = False
            for b in nodes:
                if b == entry:
                    continue
                ps = [dom[p] for p in pred[b] if p in dom]
                new = ({b} | set.intersection(*ps)) if ps else {b}
                if new != dom[b]:
                    dom[b], changed = new, True
        self.loops = {}
        for u in nodes:
            for h in self.succ[u]:
                if h in dom[u]:
                    body = self.loops.setdefault(h, {h})
                    stack = [u]
                    while stack:
                        x = stack.pop()
                        if x not in body:
                            body.add(x)
                            stack.extend(pred[x])
                elif h in dom and self.reaches_back(h, u, dom):
                    raise Unsupported("irreducible control flow")
        self.pred = pred
        self.nodes = nodes

    def reaches_back(self, h, u, dom):
        return False

    def compute_postdom(self):
        nodes = self.nodes
        exits = [b for b in nodes if not self.succ[b]]
        pdom = {b: set(nodes) for b in nodes}
        for e in exits:
            pdom[e] = {e}
        changed = True
        while changed:
            changed = False
            for b in nodes:
                if b in exits:
                    continue
                ss = [pdom[s] for s in self.succ[b]]
                new = ({b} | set.intersection(*ss)) if ss else {b}
                if new != pdom[b]:
                    pdom[b], changed = new, True
        self.pdom = pdom

    def ipdom(self, b, within):
        """The nearest strict post-dominator of `b` inside the node set `within` (or None)."""
        cands = [x for x in self.pdom[b] if x != b and (within is None or x in within)]
        for c in cands:
            if all(c == d or d in self.pdom[c] or d not in cands for d in cands):
                # c is post-dominated by all other candidates => nearest
                if all(d == c or d in self.pdom[c] for d in cands):
                    return c
        return None

    def loop_exit(self, h):
        body = self.loops[h]
        outs = {s for b in body for s in self.succ[b] if s not in body}
        if len(outs) == 1:
            return next(iter(outs))
        # exits that only return are inlined; the others must be one block
        rest = {o for o in outs if not self.only_returns(o)}
        if len(rest) > 1:
            raise Unsupported(f"loop {h} with several exits")
        return next(iter(rest)) if rest else None

    def only_returns(self, b):
        stmts, term = self.fn.blocks[b]
        return term == "return;" and all(re.fullmatch(r"_0 = .*;", s) for s in stmts)

    OVF = re.compile(r"assert\(!(?:move |copy )?\(_\d+\.1: bool\), .*\) -> \[success: (bb\d+)(?:, unwind .*)?\];")

    def test_block(self, b, body, header):
        """Statements from `b` up to a `switchInt`, through overflow checks and jumps that
        stay in `body`: (statements, switchInt terminator) or None."""
        stmts, seen = [], set()
        while b not in seen:
            seen.add(b)
            ss, term = self.fn.blocks[b]
            stmts += ss
            if term.startswith("switchInt("):
                return stmts, term
            m = self.OVF.fullmatch(term) or re.fullmatch(r"goto -> (bb\d+);", term)
            if not m:
                return None
            b = self.resolve[m.group(1)]
            if b not in body or b == header:
                return None
        return None

    def cond_chain(self, h, body, exit_):
        """The blocks from the header that only compute a test and leave the loop when it
        fails: their tests form the loop condition (a conjunction)."""
        conds, b = [], h
        self.test_stmts = []
        while True:
            tb = self.test_block(b, body, h)
            if tb is None:
                break
            stmts, term = tb
            m = re.fullmatch(r"switchInt\((copy|move) (_\d+)\) -> \[(-?\d+): (bb\d+), otherwise: (bb\d+)\];", term)
            if not m:
                break
            val, a_, o_ = m.group(3), self.resolve[m.group(4)], self.resolve[m.group(5)]
            try:
                x = self.inline_test(stmts, m.group(2))
            except Unsupported:
                break
            isbool = self.ty(m.group(2)) == "bool"
            if a_ not in body and o_ in body:      # leaves when x == val
                f, t = a_, o_
                expr = x if isbool and val == "0" else f"(({x}) != {val})"
            elif o_ not in body and a_ in body:    # stays only when x == val
                f, t = o_, a_
                expr = f"(!({x}))" if isbool and val == "0" else f"(({x}) == {val})"
            else:
                break
            conds.append(expr)
            self.test_stmts += stmts
            b = t
            if b == h:
                break
            if f != exit_ and exit_ is not None and not self.only_returns(f):
                return [], h
        return conds, b

    def inline_test(self, stmts, flag):
        """The value of the boolean `flag` as one expression, the temporaries computed by
        `stmts` (pure assignments) substituted."""
        env = {}
        for s in stmts:
            m = re.fullmatch(r"(_\d+) = (.+);", s)
            if not m:
                raise Unsupported("test with effects")
            loc = m.group(1)
            ty = self.ty(loc)
            e = self.rvalue(m.group(2), None)
            if isinstance(e, tuple):
                if e[0] != "tuple":
                    raise Unsupported("test with effects")
                name, e = self.var(loc) + "_val", e[1]
            elif scalar(ty):
                name = self.var(loc)
            else:
                raise Unsupported("test with effects")
            for k, v in env.items():
                e = re.sub(rf"\b{k}\b", v, e)
            env[name] = f"({e})"
        return env.get(self.var(flag), self.var(flag))

    def region(self, b, stop, loop, indent):
        """Code for the blocks from `b` until `stop`, inside the loop `loop` = (header,
        exit) or None."""
        out = []
        while b is not None and b != stop:
            if loop and b == loop[0]:
                out.append(indent + "continue;")
                return out
            if loop and b == loop[1]:
                out.append(indent + "break;")
                return out
            if b in self.loops and (not loop or b != loop[0]):
                h = b
                exit_ = self.loop_exit(h)
                conds, first = self.cond_chain(h, self.loops[h], exit_)
                if not conds:
                    raise Unsupported(f"loop {h} without a test at its head")
                # the test's statements are pure: re-run in the body and after the loop,
                # where their temporaries may be used
                again = [self.statement(x) for x in self.test_stmts]
                out.append(indent + f"while ({' && '.join(conds)}) {{")
                out += [indent + "  " + x for x in again]
                out += self.region(first, h, (h, exit_), indent + "  ")
                out.append(indent + "}")
                out += [indent + x for x in again]
                b = exit_
                continue
            stmts, term = self.fn.blocks[b]
            for s in stmts:
                out.append(indent + self.statement(s))
            nxt, code = self.terminator(b, term, stop, loop, indent)
            out += code
            b = nxt
        return out

    def terminator(self, b, term, stop, loop, indent):
        if term == "return;":
            return None, [indent + ("return;" if self.fn.ret == "()" else "return ret;")]
        if term == "unreachable;":
            return None, [indent + self.ret0()]
        m = re.fullmatch(r"goto -> (bb\d+);", term)
        if m:
            return self.resolve[m.group(1)], []
        m = re.fullmatch(r"switchInt\((.+?)\) -> \[(.*)\];", term)
        if m:
            x = self.operand(m.group(1))
            arms = [a.split(": ") for a in split_top(m.group(2))]
            within = self.loops[loop[0]] if loop else None
            merge = self.ipdom(b, within)
            code, first = [], True
            # a boolean test computed in this block: the test itself, so that the analysis
            # sees the comparison (its operands are not changed after it in the block)
            mv = re.fullmatch(r"(?:copy|move) (_\d+)", m.group(1).strip())
            if mv and self.ty(mv.group(1)) == "bool" and len(arms) == 2 and arms[0][0] == "0":
                try:
                    x = self.inline_test(self.fn.blocks[b][0], mv.group(1))
                except Unsupported:
                    pass
                code.append(indent + f"if ({x}) {{")
                code += self.region(self.resolve[arms[1][1]], merge, loop, indent + "  ")
                code.append(indent + "} else {")
                code += self.region(self.resolve[arms[0][1]], merge, loop, indent + "  ")
                code.append(indent + "}")
                return merge, code
            for val, tgt in arms[:-1]:
                kw = "if" if first else "} else if"
                code.append(indent + f"{kw} ({x} == {val}) {{")
                code += self.region(self.resolve[tgt], merge, loop, indent + "  ")
                first = False
            code.append(indent + "} else {")
            code += self.region(self.resolve[arms[-1][1]], merge, loop, indent + "  ")
            code.append(indent + "}")
            return merge, code
        m = re.fullmatch(r"assert\((!?)(?:move |copy )?(.+?), .*\) -> \[success: (bb\d+)(?:, unwind .*)?\];", term)
        if m:
            neg, p, nxt = m.group(1), m.group(2), m.group(3)
            p = p.strip()
            if neg and re.fullmatch(r"\(_\d+\.1: bool\)", p):
                return self.resolve[nxt], []  # overflow check: no overflow assumed (see above)
            c = self.place(p) if not p.startswith("const") else self.operand(p)
            test = f"({c})" if neg else f"!({c})"
            return self.resolve[nxt], [indent + f"if ({test}) {self.ret0()}"]
        m = re.fullmatch(r"(?:(.+?) = )?([\w:<>]+)\((.*)\) -> (.+);", term)
        if m:
            dest, callee, args, rest = m.groups()
            rm = re.search(r"return: (bb\d+)", rest)
            if not rm:   # does not return: a panic
                return None, [indent + self.ret0()]
            if callee not in self.known:
                raise Unsupported(f"call of {callee}")
            cargs = []
            for a in split_top(args):
                a = a.strip()
                mm = re.fullmatch(r"(copy|move) (_\d+)", a)
                if mm and slice_elem(self.ty(mm.group(2))):
                    cargs += [self.var(mm.group(2)), self.var(mm.group(2)) + "_len"]
                else:
                    cargs.append(self.operand(a))
            call = f"{callee}({', '.join(cargs)})"
            line = f"{self.place(dest)} = {call};" if dest and self.ty(dest.strip()) != "()" else f"{call};"
            return self.resolve[rm.group(1)], [indent + line]
        raise Unsupported(f"terminator {term}")

    def ret0(self):
        return "return;" if self.fn.ret == "()" else "return 0;"


def targets(term):
    return re.findall(r"(bb\d+)", term)


def translate(text, keep=None):
    fns, skipped = parse(text)
    known = {f.name for f in fns}
    out = ["/* Generated by frontends/rust/mir2c.py from Rust MIR. */", "#include <stdint.h>", ""]
    protos, bodies, report = [], [], []
    for f in fns:
        t = Translator(f, known)
        try:
            code = t.translate()
            protos.append(t.signature() + ";")
            bodies.append(code)
            report.append((f.name, None))
        except (Unsupported, KeyError) as e:
            known.discard(f.name)
            bodies.append(f"/* {f.name}: not translated: {e} */")
            report.append((f.name, str(e)))
    for s in skipped:
        report.append((s, "not a free function"))
    return "\n".join(out + protos + [""] + [b + "\n" for b in bodies]), report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("source")
    ap.add_argument("-o", "--output", required=True)
    ap.add_argument("--rustc", default="rustc")
    a = ap.parse_args()
    mir = pathlib.Path(a.output).with_suffix(".mir")
    subprocess.run([a.rustc, "--crate-type=lib", "--emit=mir", "-O", "-C", "overflow-checks=on",
                    "-C", "panic=abort", "-o", str(mir), a.source], check=True)
    code, report = translate(mir.read_text())
    pathlib.Path(a.output).write_text(code)
    for name, why in report:
        print(f"{'ok  ' if why is None else 'skip'} {name}" + (f": {why}" if why else ""), file=sys.stderr)


if __name__ == "__main__":
    main()
