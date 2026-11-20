# Cost certificate format (versions 1 and 2)

A certificate file is read by `crosscheck-check`
(`formalization/CheckerMain.lean`), which converts it into the Lean type
`Checker.ACmd` and runs the verified function `Checker.check`
(`formalization/ImperativeOptimization/CheckerCore.lean`; soundness:
`Checker.check_sound` in `Checker.lean`, paper `thm:checker-soundness`). The Clang
plugin writes this format with `--opt=certificates=FILE` (tool) or
`-fplugin-arg-crosscheck-certificates=FILE` (plugin).

Version 2 (written by the plugin): one *program certificate* per translation unit, a list
of functions that share one variable table (Lean `FunCert`, checked by `checkProgram`,
soundness `Checker.program_sound`, paper `thm:program-soundness`):

```json
{ "format": "crosscheck-certificates", "version": 2,
  "programs": [
    { "name": "file.cpp", "variables": ["?choice", "?cost", "sum::n", "sum::i", ...],
      "functions": [
        { "name": "sum", "pre": [ <Lin>... ], "bound": {"c": 5, "co": [7]}, "post": [],
          "mods": [3, 4], "body": <node> },
        { "name": "contract hal_read", "pre": [], "bound": 25, "post": [], "mods": [],
          "contract": true } ] } ] }
```

A function may call only the functions before it (no recursion). A function with
`"contract": true` and no body is an **assumed contract**: `crosscheck-check` prints it as
`ASSUMED` and the verdict of the program (`PROGRAM … ACCEPTED (relative to the assumed
contracts)`) holds only if the contracts hold. Every function's body must modify only its
`mods` (checked).

Version 1 (still read): a list of standalone certificates without calls:

```json
{ "format": "crosscheck-certificates", "version": 1,
  "certificates": [
    { "function": "f", "variables": ["?choice", "?cost", "n", "i"],
      "pre": [ <Lin>... ], "bound": 21, "post": [ <Lin>... ],
      "program": <node> } ] }
```

`variables` only names the indices for printing (`crosscheck-check --print`). Missing
`sv`/`lv` fields mean the empty list. `test/certificates/count.json` is a complete
example (a single loop, and a loop with a conjunctive test); every certificate of
`count_rejected.json` (five) must be rejected.

## Contents

The checker's input is the Lean type `ACmd` of
`formalization/ImperativeOptimization/Checker.lean`, with a precondition, a bound and a
postcondition. Everything is integer data:

- **Variables** are numbered `0, 1, 2, …`. The emitter assigns a number to every tracked
  program variable of the function (parameters first) and keeps the table in the
  certificate for readability.
- **`PExp`** `{sv, c}`: the affine expression `Σ sv[i]·xᵢ + c` (dense coefficient list).
- **`Lin`** `{sv, lv, c}`: an affine form over program variables (`sv`) and logical
  variables (`lv`); as a constraint it means `≤ 0`. An assertion is a list of `Lin`.
- **Symbolic bound** (Lean `SB`): a natural number, or `{c, co, q}` meaning
  `c + Σ co[j]·max(0, γⱼ) + Σ a·max(0, γᵢ)·max(0, γⱼ)` over the quadratic terms
  `q = [[a, i, j], ...]` (optional; absent = none), with natural coefficients over the
  logical variables. A function's precondition contains `x_p = γ_p` for its parameters, so
  its bound is a *summary* in its parameters, at most quadratic. Bounds are compared coefficient by coefficient, the quadratic terms of the
  smaller one being a subsequence of those of the larger (`SB.le`, `qsub`: syntactic, so
  the producer writes the expansion the checker computes, `SB.mul`/`crossQ`, which
  includes zero coefficients).
- **Farkas certificate** `(mu, lam)`: `mu ≥ 1` and one multiplier per premise, in the
  order of the premise list, such that `mu·goal − Σ lam[i]·premise[i]` is a constant
  `≤ 0`. Z3 gives rational multipliers: multiply by the common denominator.
- **Nodes** (`ACmd`):

| Node | Fields | Accepted when |
|---|---|---|
| `skip` | – | `P = Q`, `B = 0` |
| `assign w x a` | weight, variable, `PExp` | `P = Q[a/x]` (syntactically, constraint by constraint), `B = w` |
| `havoc w x` | weight, variable | `P = Q`, `x` does not occur in `Q`, `B = w` |
| `havocC w x cs` | weight, variable, constraints `cs` (each `g ≤ 0`, program variables only) | `x` does not occur in `P`; `Q = P ++ cs`; `B ≥ w` (an unknown value of which the constraints hold) |
| `seq c₁ mid B₁ B₂ c₂` | intermediate assertion, two bounds | both parts accepted, `B = B₁ + B₂` |
| `ite w g B₁ B₂ c₁ c₂` | test `g ≤ 0`, two bounds | `c₁` accepted from `g ≤ 0 :: P`, `c₂` from `1 − g ≤ 0 :: P`, `B = w + max B₁ B₂` |
| `while w g inv pot d k kl j posCert Wb body` | invariant, potential `pot/d`, entry bound `K = k + Σ kl[i]·γᵢ` (`kl` optional), logical variable `j`, certificate of `pot ≥ d`, body bound | `d ≥ 1`; `P = (pot − K ≤ 0) :: inv`; `Q = (1 − g ≤ 0) :: inv`; `γⱼ` not in `inv`; `posCert` proves `d − pot ≤ 0` from `g :: inv`; body accepted from `(pot − γⱼ ≤ 0) :: g :: inv` to `(pot + d − γⱼ ≤ 0) :: inv` with bound `Wb`; then (`loopOk`) either `γⱼ` not in `Wb` and: `kl = 0` and `B ≥ ⌊k/d⌋·(w + Wb) + w`, or `Wb` constant (no quadratic term), `B.c ≥ w`, `(w+Wb)·k ≤ d·(B.c − w)` and `(w+Wb)·kl ≤ d·B.co`, or, **a product**, `d = 1`, `Wb` linear and `B ≥ (w + Wb)·⟨max(0,k), kl⟩ + w` (`SB.mul`; a nest of two loops over parameters) (`loopBoundOk`; `γⱼ` in no linear or quadratic term of `Wb`, `qfree`); or, **amortised** (`triOk`, soundness `triloop_sound`, paper `prop:amortised-loop`): `kl = 0`, `Wb = a + c·max(0, γⱼ)` with no other logical variable, and `2·B.c ≥ 2((N+1)w + N·a) + c·(2Nk − dN(N−1))`, `N = ⌊k/d⌋` (`triBound2`) |
| `whileAnd w gs inv pot d k j posCert Wb body` | as `while`, with a list of tests `gs` (the loop runs while every `g ≤ 0`) | as `while` with `g :: inv` replaced by `gs ++ inv` (each `g` as the constraint `g ≤ 0`), except `Q = inv`: the negation of a conjunction is not an assertion |
| `whileLog w gs inv pot b k j posCert Wb body` | tests `gs`, invariant, potential `pot`, base `b`, constant entry bound `k`, logical variable `j`, certificate of `pot ≥ 1`, constant body bound | `b ≥ 2`; `P = (pot − k ≤ 0) :: inv`; `Q = (1 − g ≤ 0) :: inv` if `gs = [g]`, else `inv`; `γⱼ` not in `inv`; `Wb` constant; `posCert` proves `1 − pot ≤ 0` from `gs ++ inv`; body accepted from `(pot − γⱼ ≤ 0) :: gs ++ inv` to `(b·pot − γⱼ ≤ 0) :: inv`; `B ≥ N·(w + Wb) + w` with `N = 0` if `k ≤ 0`, else `⌊log_b k⌋ + 1` (`logIters`; soundness `logloop_sound`, paper `thm:checker-soundness`) |
| `whileGrow w gs inv pot b K j capCert Wb body` | as `whileLog`, with a limit `K` instead of an entry bound and a certificate `capCert` of `pot ≤ K` | `b ≥ 2`; `P = (1 − pot ≤ 0) :: inv`; `Q` as `whileLog`; `capCert` proves `pot − K ≤ 0` from `gs ++ inv`; body accepted from `(γⱼ − pot ≤ 0) :: (1 − pot ≤ 0) :: gs ++ inv` to `(b·γⱼ − pot ≤ 0) :: inv`; `B ≥ logIters(b, K)·(w + Wb) + w` (`growloop_sound`) |
| `whileUp w gs inv pot d k j posCert Wb body` | as `whileAnd` without `kl` (constant entry bound `k`): **amortised with increasing cost** (an inner loop from `0` to the outer counter) | `d ≥ 1`; `P = (pot − k ≤ 0) :: inv`; `Q` as `whileLog`; `γⱼ` not in `inv`; `posCert` proves `d − pot ≤ 0` from `gs ++ inv`; body accepted from `(k − pot − γⱼ ≤ 0) :: (pot + γⱼ − k ≤ 0) :: gs ++ inv` (`upLo`, `upHi`: `γⱼ = k − pot`, what the potential has lost) to `(pot + γⱼ − k + d ≤ 0) :: inv`; `Wb = a + c·max(0, γⱼ)` with no other logical variable; `2·B.c ≥ 2((N+1)w + N·a) + c·(2Nk − dN(N+1))`, `N = ⌊k/d⌋` (`upOk`, `upBound2`; soundness `uploop_sound`, paper `prop:amortised-loop`(2)) |
| `call w f inst preCerts ubs ubCerts` | callee index `f` (an earlier function), expressions `inst[j]` for the callee's `γⱼ`, certificates of its precondition, symbolic bounds `ubs[j]` of `inst[j]` in the caller's `γ` with their certificates | `preCerts` prove the callee's `pre` with `γⱼ := inst[j]` from `P`; `ubCerts` prove `inst[j] ≤ ubs[j]`; `len(callee.co) ≤ len(ubs) ≤ len(inst)`, every `ubs[j]` linear and every index of `callee.q` below `len(ubs)`; `B ≥ w + callee.c + Σ callee.co[j]·ubs[j] + Σ a·ubs[i]·ubs[j]` over `callee.q` (`callBound`, `SB.qcomb`); `Q` = the constraints of `P` that do not mention the callee's `mods` |
| `weaken P' preCerts B' Q' postCerts c` | inner triple and certificates | `P ⊢ P'` and `Q' ⊢ Q` constraint by constraint, `B' ≤ B`, `c` accepted for the inner triple |
| `dead cert c` | certificate | `P ⊢ 1 ≤ 0` |

Syntactic equalities (`P = …`) are exact list equalities: the emitter must produce the
vectors the checker computes (e.g. for `assign`, apply the same substitution as
`Lin.subst`), or wrap the node in a `weaken`. `countCert` in `Checker.lean` is a complete
worked example; use it as the first test.

JSON field names: `skip`; `assign {w, x, a}`; `havoc {w, x}`; `seq {c1, mid, B1, B2, c2}`;
`havocC {w, x, cs}`; `ite {w, g, B1, B2, c1, c2}`; `while {w, g, inv, pot, d, k, j, posCert, Wb, body}`;
`whileAnd {w, gs, inv, pot, d, k, j, posCert, Wb, body}` (both with an optional `kl`);
`whileLog {w, gs, inv, pot, b, k, j, posCert, Wb, body}`;
`whileGrow {w, gs, inv, pot, b, K, j, capCert, Wb, body}`;
`whileUp {w, gs, inv, pot, d, k, j, posCert, Wb, body}`;
`call {w, f, inst, preCerts, ubs, ubCerts}`; bounds `B1`, `B2`, `Wb`, `B`, `bound`, `ubs[j]` are
symbolic bounds;
`weaken {P, preCerts, B, Q, postCerts, c}`; `dead {cert, c}`; a Farkas certificate is
`{mu, lam}`; `PExp` is `{sv, c}`; `Lin` is `{sv, lv, c}`.


## Mini-C sources (validation against the source)

With `--opt=minic` (and `--opt=certificates=FILE`), each function of a version-2 file may
also carry `"source"`: the C function as a **mini-C** program (Lean `MiniC.MStmt`,
`formalization/ImperativeOptimization/MiniCCore.lean`), written by
`clang-plugin/src/analysis/MiniC.cpp` from the C syntax alone, not from the certificate.
`crosscheck-check` then runs the verified `MiniC.validate`: it lowers the source
(`MiniC.lower`, the definition of mini-C's meaning) and compares it with the
certificate's program after removing annotations, `weaken` and `dead` nodes (keeping the
code they contain), `skip` and the nesting of sequences (`MiniC.nf`). It prints

```
VALIDATED f: the certificate's program is the lowering of its source
NOT VALIDATED f: the certificate's program is not the lowering of its source
```

(exit status 1 for `NOT VALIDATED`; `--print` then shows both normal forms). A validated
certificate bounds the cost of the source program (theorem `MiniC.validated_sound`,
paper `thm:validated`): the certificate generator is not trusted, the exporter and the
cost model are. When a function is outside the exporter's fragment, `"source_refused"`
gives the reason (the checker ignores it).

```
stmt  ::= {"s":"skip"} | {"s":"assign","w":W,"x":X,"e":exp} | {"s":"cost","w":W}
        | {"s":"div","w":W,"x":X,"op":"div"|"rem"|"and","y":exp,"c":C[,"old":T]}
        | {"s":"assignU","w":W,"x":X,"hi":H,"e":exp}
        | {"s":"call","f":F,"args":[{"x":X,"e":exp[,"hi":H]}...]}
        | {"s":"seq","ss":[stmt...]} | {"s":"if","w":W,"c":cond,"a":stmt,"b":stmt}
        | {"s":"while","w":W,"cs":[cond...],"body":stmt}
        | {"s":"for","init":stmt,"w":W,"cs":[cond...],"inc":stmt,"body":stmt}
exp   ::= {"e":"var","x":X} | {"e":"lit","k":K} | {"e":"add"|"sub"|"mul","a":exp,"b":exp}
        | {"e":"neg","a":exp} | {"e":"other"}
cond  ::= {"c":"cmp","op":"<"|"<="|">"|">=","a":exp,"b":exp} | {"c":"not","a":cond}
        | {"c":"other"}
```

`div` is `x = y op c` for a constant `c` (a right shift by `k` is written as `div` by
`2^k`): `x` receives an unknown value constrained by the facts of Lean `divFacts` (for
`y >= 0`: `c*x <= y <= c*x + c - 1`, or `0 <= x <= c - 1` and `x <= y`, or `0 <= x <= c`
and `x <= y`; for a negative `y` nothing, except `0 <= x <= c` for a mask). When `y`
mentions `x`, `old` names a scratch variable that first receives `y`; the exporter takes
it from the certificate's variables after checking that it is not a variable of the
source.

`assignU` is a store into an unsigned variable (`unsigned int` or wider) whose largest
value is `hi`: `x` receives the value of `e`, computed over the integers, if it lies in
`[0, hi]`, and an unknown value otherwise (where C wraps). `hi` is `2^width - 1`, and
`2^62` for 64-bit variables.

`call` is a call of function number `F` of the same program: each listed argument is
stored into the variable `X` of the callee's parameter (an unsigned store when `hi` is
given), at no cost, then the callee's program runs. Only the callee's tracked integer
parameters are listed; the value of the call is unknown to the caller. The cost of
evaluating the call belongs to the statement that follows.

`w` are the weights of the cost model; `x` index the program's `variables`; `other` is an
unknown value (an unknown test, in a conditional, is a nondeterministic choice; in a loop
test it is outside the fragment). With `minic`, a `dead` node of the certificate
contains the code that is not reached (loops in it get the potential 0: nothing inside a
dead node is checked). `test/certificates/minic.json` validates; no source of
`minic_rejected.json` (four variations of the program) does.

What the exporter does (`MiniC.cpp`): tracked variables (those of the certificate) are
read as variables, every other read is `other`; assignments to them are `assign`, every
other statement is `cost`; signed `+`, `-`, `*`, unary `-` and value-preserving
conversions are exact (signed overflow is undefined behaviour, assumed absent);
compound `+=`/`-=` and `++`/`--` are exact only when converting the result back to the
variable's type preserves values. `return` ends the function: outside loops, the rest
of the body moves into the branches of a conditional that contains one. Quotients,
shifts, remainders and masks by a constant are `div` statements, stores into
`unsigned int` or wider variables are `assignU`, calls of functions with an entry in the
file are `call` (see the grammar above).

**Jumps, `switch` and `do` loops (`"jsource"`).** Since 2026-11-16 the exporter writes
every function as `"jsource": {"ret": r, "body": J}`, a statement of mini-C with jumps
(Lean `MiniC.JStmt`, `MiniCJumpCore.lean`):

    J ::= {"j":"basic","s":S} | {"j":"seq","js":[J...]} | {"j":"if","w","c","a":J,"b":J}
        | {"j":"loop","w","cs":[C...],"body":J,"inc":S?,"fb":n?,"fc":n?}
        | {"j":"do","w","cs":[C...],"body":J,"fb":n?,"fc":n?}
        | {"j":"break","w"} | {"j":"continue","w"} | {"j":"return","s":S}
        | {"j":"switch","w","sc":n,"groups":[J...]}

with `S` and `C` the mini-C statements and tests above. `fb`, `fc`, `sc` and `r` are the
certificate's ghost variables, found by name (`?break<d>`, `?continue<d>` for a loop at
nesting depth `d`; `?case<s>` for a `switch` at `switch` depth `s`; `?return`; `r` is an
unused index when there is none). The checker eliminates the jumps itself
(`MiniC.elim`): a jump stores 1 into its flag, loops test their exit flags, what follows a
jump moves into the branches that do not jump, the statements after a construct that may
set the return or continue flag run under `if (flag <= 0)`, each `switch` group runs
under `?case<s> := ?; if (?case<s> <= 0)`, and a `do` loop without own `break`/`continue`
is its body followed by the loop. It then validates as for `"source"` (`MiniC.validateJ`),
refusing ghost variables named by the source or not fresh along a nesting path, and
checks that no earlier function body reads or writes them (`MiniC.quietCmd`). Theorem
`MiniC.validatedJ_sound`: the bound holds for every execution prefix of the source in
its direct meaning (`MiniC.JExecD`). The rewriting is no longer trusted.

**`switch`.** Mini-C has no such statement and the tested value is not compared with
the labels: a `switch` is the cost of its test followed by each case group (the
statements from one label to the next) under an unknown test of weight 0, `if (other)
group`. Every execution of the C statement is one of these (the groups from the label
entered up to a `break`); the description has more of them, so it is an
over-approximation, like every unknown test. A `break` ends its group (weight: a
branch); `return` and `continue` use the flags above, and what follows a `switch` that
contains one of them runs under a test of the flag. Labels inside nested statements are
refused.

Refused (no source, reason in `source_refused`): calls in tests, indirect calls, calls
of functions without an entry; loops without a test that are left by a jump; `goto`,
`do`; tracked variables that are global, static, volatile, of a narrow unsigned
type, or whose address is taken; divisions and shifts outside the modelled forms; reads
of constant tables.

## Cycle certificates (`"format": "crosscheck-cycles"`)

Cycle bounds of machine code, in a file of their own (produced by
`benchmarks/cycles/ipet.py`, for the Cortex-M0; checked by the same `crosscheck-check`;
Lean `Cycles`, Paper I `prop:cycles`):

```json
{"format": "crosscheck-cycles", "version": 1,
 "programs": [{"name": "program", "functions": [
   {"name": "f", "entry": 0, "exit": 3,
    "edges": [{"src": 0, "dst": 1, "w": 2}, {"src": 1, "dst": 2, "w": 1},
              {"src": 2, "dst": 1, "w": 5, "calls": ["g"]}, {"src": 1, "dst": 3, "w": 3}],
    "rows": [{"coef": [[2, 1], [0, -10]], "rhs": 0, "note": "loop at 0x...: at most 10 back edges per entry"}],
    "certificate": {"scale": 1, "pot": [65, 3, 2, 0], "mult": [6], "bound": 65}}]}]}
```

- A function is a graph on nodes `0..`: `entry`, `exit`, `edges` (indexed by position:
  `w` = cycles when the edge is taken, `calls` = functions of the same program called
  on it, by name), and `rows` `Σ coef[e]·x_e ≤ rhs` on the number of times `x_e` each
  edge is taken (`[edge, coefficient]` pairs). The graph, weights and rows are trusted:
  they are the producer's description of the code, its timing and its loop bounds.
- The certificate: `scale` `D > 0`, potentials `pot` (one per node; missing ones are 0),
  multipliers `mult ≥ 0` (one per row; missing ones are 0), claimed `bound`. It is
  accepted if, for every edge `e = (u, v)`,
  `D·(w + Σ bound(callee)) + pot[v] − pot[u] ≤ Σ_k mult[k]·coef_k[e]`, and
  `pot[entry] − pot[exit] + Σ_k mult[k]·rhs[k] ≤ D·bound`.
- The program is accepted (`PROGRAM … ACCEPTED`) if every function is, with the claimed
  bounds of all; then every completed run of each function whose edge counts satisfy its
  rows costs at most its bound (`Cycles.program_sound`; recursion is allowed, the
  argument is by induction on the depth of calls).
- Other fields (`note`, `blocks`: the block addresses) are ignored by the checker.

## Cycle certificates on machine code (`"format": "crosscheck-binary-cycles"`)

The same certificates, but the graph is built by the checker from the machine code
(Lean `Thumb`, Paper III `thm:machine-cycles`); this is what `benchmarks/cycles/ipet.py`
produces for the Cortex-M0:

```json
{"format": "crosscheck-binary-cycles", "version": 1, "mul_cycles": 32,
 "code": {"base": 0, "halfwords": [8192, 10250, 55809, 12289, 59387, 18288]},
 "programs": [{"name": "program", "functions": [
   {"name": "f", "entry": 0, "nodes": [0, 2, 4, 6, 8, 10],
    "rows": [{"coef": [[8, 2, 1], [0, 2, -10]], "rhs": 0, "note": "loop at 0x2: ..."}],
    "certificate": {"scale": 1, "pot": [68, 7, 6, 5, 4, 3, 0], "mult": [6], "bound": 68}}]}]}
```

- `code`: the 16-bit halfwords of the code region from address `base`; `mul_cycles`: the
  cycles of MULS (1 or 32, a configuration of the processor).
- A function: its `entry`, the addresses of its instructions (`nodes`), its loop `rows`
  on transitions `[src, dst, coefficient]` (the number of times the instruction at `src`
  is followed by the one at `dst`), and the certificate: potentials in the order of
  `nodes`, then the exit node.
- The checker decodes every address of `nodes` (`Thumb.decode`: ARMv6-M Thumb, cycles of
  the Cortex-M0 with zero-wait-state memory), requires the entry to be in `nodes`, every
  successor to be in `nodes` and no instruction without a modelled effect on the program
  counter (indirect branches, `BLX`, `SVC`, `WFI`, undefined...), maps every `BL` target to
  a function of the program, builds one edge per successor (a conditional branch: 3
  cycles taken, 1 not taken; `BL`: 4 cycles plus the callee's bound), and checks the
  certificate on that graph (`Thumb.checkBinary`).
- Accepted: every run of the machine code of each function, in the semantics of
  `Thumb.MRun` (data abstracted: both successors of a conditional branch possible), on
  which its rows hold, costs at most its bound (`Thumb.binary_sound`). Trusted: the
  decoder and timing table, that the code is the binary's, the rows.
- `crosscheck-check --decode FILE` prints the decoding of the `addresses` of FILE
  (`mul_cycles`, `code`, `addresses`), for `benchmarks/cycles/test_thumb.py`.

### Version 2: loop bounds certified on the machine code

Version 2 (`"version": 2`, produced by `ipet.py` with `loops=True`, i.e. `run_cycles.py
--certify-loops` or `crosscheck_link.py --certify`; Paper III `thm:machine-loops`, Lean
`ThumbData.data_sound`) adds optional fields; a version-1 file is read as before.

- `"abi"` (program-wide, default `false`): with `true`, a call may change only `r0`-`r3`
  and the flags (callees are assumed to preserve `r4`-`r7` and SP, as the AAPCS requires);
  the verdict says so.
- Per function, the stack (Lean `Thumb.stackEffect`, `StackOk`): `"sp"`: per instruction
  (order of `nodes`) the offset of SP from its value at the entry, or `null` (unknown; the
  entry's offset must be `0` or `null`; the checker verifies every transition against the
  effect: `PUSH`/`POP`/`ADD SP`/`SUB SP` move SP by their constants); `"slots"`: tracked
  words of the frame, distinct positive multiples of 4 below 2^20 (`k`: the word at
  `SP₀ − k`), certificate variables `20 + j` (and `20 + S + j` for their fresh values
  after an instruction; `S` the number of slots, `nVars = 20 + 2S`); `"frame"` (default
  `false`): assume that stores through registers other than SP and calls do not write the
  function's frame (words between SP and `SP₀`); refused if the function puts an address
  derived from SP into a register (`ADD rd, SP, #i`, `MOV rd, SP`, `ADD rd, SP`), except
  the frame pointer `ADD r7, SP, #i`, provided no instruction may then read r7 other than
  as the base address of a load or a `PUSH` at the entry (`Thumb.frameUseOk`).
- Per function, `"rows"` are now the **trusted** rows only; `"loops"` lists the certified
  loops, whose rows the checker generates (`Thumb.loopRow`) and appends to the trusted
  ones, in that order (the IPET certificate's `mult` follows that order):
  `{"header": h, "body": [addresses], "scale": D, "bound": N, "pot": [affine expressions,
  in the order of body]}`; the row is `Σ_{u ∈ body} D·x(u→h) − Σ_{u ∉ body} N·x(u→h) ≤ N`
  if the entry is in the body, `≤ 0` otherwise (at most N/D back edges per entry).
- `"kinds"`: per instruction (order of `nodes`) the operation that set the flags,
  `"none"`, `"add"` or `"sub"`; `"inv"`: per instruction a list of constraints
  `{"sv": [[variable, coefficient], ...], "c": c}` meaning `Σ coefficient·x + c ≤ 0`;
  variables `0`-`7` are `r0`-`r7`, `8` and `9` the operands of the operation that set the
  flags. Potentials have the same form (an affine expression `Σ coefficient·x + c`).
- `"cong"` (optional, default none): per instruction (order of `nodes`) a list of
  congruences `[v, e, r]`, "variable `v` is `r` modulo `2^e`", `e ≤ 32`, `v` a variable of
  a state (`0`-`9` or a tracked word `20 + j`); none at the entry. The checker verifies
  them without Farkas certificates (Lean `congOk`): after every transition, in every wrap
  case, the post-expression `Σ k_v·x_v + c` of `v` (the same as for the invariants) must
  have, for each term, `2^e` dividing `k_v·2^{e_v}` (`e_v` from the congruences before the
  instruction, `0` if none), and `Σ k_v·r_v + c ≡ r (mod 2^e)`. At a conditional branch,
  if the ghosts `8` and `9` are congruent modulo `2^e` (largest such `e`, Lean `gExp`),
  the facts `±(x₈ − x₉) + c ≤ 0` of the condition are rounded to `c` a multiple of `2^e`
  (`tightenL`) before they become premises (Paper III, after `lem:cond-facts`). Likewise,
  if `x₈ + x₉` is a multiple of `2^e` (largest such `e`, at most both exponents, Lean
  `gExpS`), the facts `±(x₈ + x₉) + c ≤ 0` (those of the flags of an addition) are rounded
  (`tightenS`).
- `"alt"` (optional, default none): per instruction (order of `nodes`) a list of further
  disjuncts of the invariant, each a list of constraints like `"inv"`; the invariant at an
  instruction is then `inv` **or** one of these (Lean `invsAt`; disjunct `0` is `inv`). The
  producer gives them between an addition or subtraction that may wrap around and the next
  conditional branch (the loops of the division routines, `for (i = 31; i >= 0; i--)`).
- `"pick"` (optional, default none): per instruction a list of `[j, m, d, s, t]`: the case of
  transition `j`, wrap case `m`, fact `d` of the branch and source disjunct `s` lands in
  disjunct `t` of the next instruction's invariant (Lean `tgtIdx`, `tgtInv`); cases not
  listed land in disjunct `0`, as does a `t` without such a disjunct.
- `"proofs"`: one Farkas certificate `[mu, [[premise index, multiplier], ...]]` per
  obligation, in the order of `Thumb.obligations` (the entry's invariant and the
  potentials at the entry from the ranges alone; then, for every instruction, every
  transition, every wrap case of a written sum or difference, every disjunct of the
  facts of a branch and every disjunct of the instruction's invariant, the target disjunct
  of the successor's invariant and the descent `k + Φ(next) − Φ(here) ≤ 0` of every
  certified loop). The premises are the fact of the branch, the wrap case, the disjunct of
  the instruction's invariant and the ranges `[0, 2^32 − 1]` of the `20 + 2S` variables
  (`10`-`17`: registers written with any value, `18`, `19`: fresh ghosts, then the
  tracked words before and after).
- Accepted (the second line per function, `ACCEPTED f: loop bounds of the machine code`,
  and the program line): every run of the data semantics (`ThumbData.DRun`: effects of the
  instructions on `r0`-`r7` and the flags, `Thumb.effect`; a branch taken iff its
  condition holds, `Thumb.condHolds`) on which the trusted rows hold costs at most the
  bound. Trusted: the decoder, the timing table, the effects, flags and conditions
  (compared with `m0.py` by `test_effect.py`), the code and that it is not written during a
  run (a load from the literal pool, `LDR rt, [pc, #i]`, gives the word of the code at its
  address when both halfwords are in `"code"`, any value otherwise), the trusted rows, and
  the assumption on callees if `"abi"` is true. Exact effects (since 2026-11-19, besides
  `ADDS`/`SUBS`/`MOVS`/`CMP`/`CMN`/`MOV`/`ADD` of low registers): `LSLS` by a constant
  (`rm·2^s` when it does not overflow, any value when `rm·2^s ≥ 2^32`), `NEGS`, `MVNS`, the
  literal load, the write-back of `STM`/`LDM` (base + 4 per register; `STM` keeps its list;
  `LDM` with the base in its list, or an empty list, gives any value).
- `crosscheck-check --effect FILE` prints, for each case (`a`, registers `r`, flags `f`),
  the registers and flags after the instruction as Lean computes them and the fourteen
  conditions, for `benchmarks/cycles/test_effect.py`.

Example (the counting loop of the version-1 example, its bound proved on the code; no
trusted row), excerpt:

```json
{"loops": [{"header": 258, "body": [258, 260, 262, 264], "scale": 1, "bound": 10, "pot": [{"sv": [[0, -1]], "c": 10}, {"sv": [[0, -1]], "c": 10}, {"sv": [[0, -1]], "c": 10}, {"sv": [[0, -1]], "c": 11}]}], "kinds": ["none", "none", "sub", "sub", "add", "sub"], "inv": [[], [{"sv": [[0, 1]], "c": -10}], [{"sv": [[0, 1]], "c": -10}, {"sv": [[0, 1], [8, -1]], "c": 0}, {"sv": [[8, 1]], "c": -10}, {"sv": [[0, -1], [8, 1]], "c": 0}, {"sv": [[9, 1]], "c": -10}, {"sv": [[9, -1]], "c": 10}], "..."]} ...
```

## How the plugin produces certificates

`src/analysis/Analyzer.cpp`, section "Certificates", and `src/core/Cert.{hpp,cpp}`:

- **Variables**: the tracked integer variables (signed or unsigned) that can influence control
  (those of tests and loop potentials, closed under the assignments and argument
  passing that feed them); index 0 is a variable for nondeterministic tests, index 1 a
  variable that no assertion mentions (statements that only cost are unknown values
  given to it). Other variables are not part of the certificate.
- **Assertions** are computed forwards (strongest postconditions, Fourier–Motzkin);
  every step is wrapped in `weaken` with Farkas multipliers found by Z3 and turned into
  integers. Joins after a conditional keep the constraints implied by both branches.
- **Loops** use the potential found by the analysis (scaled to integers), an invariant
  found by Houdini over the entry constraints, and the entry bound computed by Z3.
- **Calls** of a function that already has its own certificate (an earlier root of the
  translation unit) become `call` nodes: the callee's parameters (its variables) receive the
  arguments, its precondition is proved, and each argument is bounded by a symbolic bound
  of the caller's parameters (if one is no looser than a constant at the largest admissible
  arguments) or by a constant. Otherwise the callee's body is inlined in its calling
  context, as before.
- **Summaries**: in a function with parameters, the potential suggested by the loop test
  (`n − i` for `i < n`) is tried before the analysis' potential (which may use the range,
  `64 − i`); the entry bound is symbolic (`symbolicUpper`: Fourier–Motzkin projection on
  the potential and the parameters' logical variables) when the body bound is constant and
  the symbolic bound is no looser than the constant one at the largest admissible
  parameters. The report gives `certificate_summary` (e.g. `5 + 7*max(0,n)`) and
  `certificate_bound` (its value at those parameters).
- **Contracts**: `CROSSCHECK_COST(n)` functions and the functions of a contract file
  (`docs/contracts.md`) are contract entries (`"contract": true`); a contract with a cost per
  argument has variables for those arguments and `x = γ` in its precondition.
- **Early returns** are restructured: the statements after `if (c) return ...;` become
  the other branch (more generally, the rest of a list moves into the branches of any
  conditional or block that may leave it).
- **Early exits from loops**: each loop that needs them gets flag variables
  `?break<j>` and `?continue<j>`, and the function a flag `?return`; a jump sets its
  flag to 1. The rest of the body after a statement that may jump runs under `if (flag
  ≤ 0)`; the increment of a `for` runs unless `break` or `return` was taken; the loop
  test is the conjunction of the C test and `flag ≤ 0` for the `break` and `return`
  flags (node `whileAnd`), and after a loop containing a `return` the rest of the list
  is guarded by `?return ≤ 0`. The iteration that leaves through a flag does not
  decrease the C potential, so the potential becomes `pot + c·(1 − Σ flags)` for the
  first `c` in `d, 2d, …, 64d` that the checker's conditions accept; the invariant
  contains `0 ≤ flag ≤ 1`. A callee inlined inside a loop gets its own flags.
- **`switch`**: a cost atom for the test, then one conditional per group of cases,
  `havoc ?choice; if (?choice ≤ 0) group else skip` (the cases are taken
  nondeterministically, which is sound); fall-through is the sequence of groups; `break`
  in a case ends the group (the rest of the group moves into the branches). Case labels
  nested in other statements (Duff's device) are refused.
- **`&&` loop tests** become the list of a `whileAnd` node; a conjunct that is not a
  linear comparison (`||`, `!=`, a memory read) is replaced by a choice variable
  `?test<j>` havocked before the test.
- **Shifts, quotients, remainders and masks by constants** (`x = y >> k`, `y / c`, `y % c`,
  `y & m`, and `x >>= k` …): `if (0 ≤ y) x := ? with c·x ≤ y ≤ c·x + c − 1` (or `0 ≤ x ≤
  c − 1, x ≤ y`; `0 ≤ x ≤ m`) `else x := ?` (`havocC`), when the result type fits `x`.
- **Constant tables**: `x = tab[i]` for a `const` integer array with a constant
  initializer is `x := ? with min ≤ x ≤ max` of its entries.
- **Globals and static locals**: one variable of the program certificate each, shared by all
  functions (a callee's writes are in its `mods`). **Fields** `p->f` read through pointer
  parameters: a variable never assigned (its value at entry); the precondition contains the
  `input-range` facts.
- **Unsigned variables** of width w: the plugin computes an affine `a` congruent to the
  stored value modulo 2^w (sums, differences and multiples, through conversions that
  keep values or reduce modulo at least 2^w), and emits
  `if (a ≤ 2^w − 1) { if (0 ≤ a) x := a else havoc x } else havoc x` (tests of weight 0;
  `2^62` instead of `2^64 − 1` for 64-bit types, which also excludes wrap-around). The
  checker proves the wrapping branches dead where they are; nothing about wrap-around is
  trusted. Values are exact only through value-preserving conversions; a comparison of a
  signed and an unsigned operand that changes values is a nondeterministic test.
  Unsigned parameters get `0 ≤ x` (and `x ≤ 2^w − 1` for w ≤ 32) in the precondition.
- The weights are those of the plugin's cost model, so the certified bound equals the
  plugin's bound unless the certificate prunes an infeasible path (lower) or the entry
  bound of a loop is rounded up (higher).

Outside the fragment (the report says why): `do`, `goto`, case labels inside nested
statements, recursion, calls to functions without a body or contract,
`CROSSCHECK_ASSUME` / `LOOP_BOUND`, loops whose entry bound and body bound are both
symbolic (a quadratic bound) when no constant entry bound exists, globals, struct fields
and pointer counters (not tracked by the analysis either).

What a certificate does **not** say: that its program is the C/C++ function. The
lowering is unverified; the checker verifies the certificate's program.
