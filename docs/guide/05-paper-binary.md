# Part 5 — Paper III explained: certified cycle bounds of machine code

`paper/binary/crosscheck-binary.tex`. Paper III takes the step from source code to the
**compiled binary**: bounds in processor cycles, checked by the Lean checker on the machine
code itself. Read Part 2, sections 2.5, 2.6, 2.10, 2.11 and 2.15 first.

## 5.1 Why go down to the binary

A bound in abstract units (Parts 3 and 4) is about the source code. The deadline is about
time on a processor, and the processor runs the compiled code, which the compiler may have
transformed (loops rotated, functions inlined, variables kept in registers or on the
stack). A certification argument must eventually be about the binary.

```mermaid
flowchart LR
  C["C source"] -->|"plugin: loop bounds<br/>(certified on the source)"| LB["source loop bounds"]
  C -->|"Clang -O1"| B["Cortex-M0 binary"]
  B --> G["control-flow graph"]
  LB -->|"matched through debug lines<br/>(trusted: the compiler keeps<br/>the iteration counts)"| R["loop rows"]
  G --> CYC["cycle bound<br/>(timing schema or IPET)"]
  R --> CYC
```

The chain has four links: (1) the source loop bound, (2) the match between source and binary
loops, (3) the graph of the binary and the computation of the bound, (4) the timing of the
processor. Paper III makes the checker responsible for (3), and then for (2), by proving
the loop bounds on the machine code itself.

## 5.2 The processor and its timing

The target is the **Arm Cortex-M0** (ARMv6-M, Thumb instructions), with zero-wait-state
memory: no cache, no branch prediction, and every instruction has a fixed cycle count in
the Technical Reference Manual (Part 2, section 2.15). That is what makes exact cycle
counting possible without a micro-architectural model.

- `benchmarks/cycles/m0.py`: a decoder of the Thumb instructions, the cycle table, an ELF
  loader and an **interpreter** written for this project. It runs each kernel, counts
  cycles with the same table, and the kernels check their own results.
- `test_m0.py` compares the cycle table row by row with the manual (87 rows), and the
  interpreter with the C semantics.

## 5.3 First step: cycles by the timing schema (`wcet.py`)

`benchmarks/cycles/wcet.py` builds the control-flow graph of each function of the binary,
finds its **natural loops** (a loop = a header that dominates a back edge's source), and
matches each binary loop with a source loop through the **debug line table** (the line of
its back-edge branch, else of its header, else of its instructions). The source loop's bound
(from the plugin, in context) bounds the binary loop. The timing schema then gives the
function's cycles.

Results on the 29 TACLeBench kernels: **107 of 267 functions** get a cycle bound, including 6
`main` functions, at 1.24 to 2.49 times the emulated run; on the 11 calls and 45 loops
compared with the emulator, no bound is exceeded. This step trusts the matching (checked on
the runs) and the cycle table.

## 5.4 Second step: a certificate for the cycle bound (`sec:graphs`)

### IPET and its dual, on an example

Take the counting loop (Lean `Thumb.exCode`), at address `0x100`:

```text
0x100  movs r0, #0       1 cycle
0x102  cmp  r0, #10      1
0x104  bge  0x10a        3 if taken, 1 if not
0x106  adds r0, #1       1
0x108  b    0x102        3
0x10a  bx   lr           3
```

The loop row: the back edge `0x108 → 0x102` is taken at most 10 times per entry
`0x100 → 0x102`, that is `x(0x108→0x102) − 10·x(0x100→0x102) ≤ 0`. The worst case:
`1 + 10 × (1 + 1 + 1 + 3) + (1 + 3) + 3 = 68` cycles.

The **cycle certificate** (`def:cycle-certificate`) is: a scale `D = 1`, a potential `π` per
instruction (and 0 at the exit), a multiplier `λ = 6` for the row, and the bound `B = 68`:

| Instruction | `π` |
|---|---|
| `0x100` | 68 |
| `0x102` | 7 |
| `0x104` | 6 |
| `0x106` | 5 |
| `0x108` | 4 |
| `0x10a` | 3 |
| exit | 0 |

The checker verifies, for every edge `u → v` with cost `w` and row coefficient `a`:
`D·w + π(v) − π(u) ≤ λ·a`.

| Edge | `w` | `a` | `w + π(v) − π(u)` | `λ·a` | OK |
|---|---|---|---|---|---|
| `0x100 → 0x102` (entry) | 1 | −10 | 1 + 7 − 68 = −60 | 6 × −10 = −60 | ✓ |
| `0x102 → 0x104` | 1 | 0 | 1 + 6 − 7 = 0 | 0 | ✓ |
| `0x104 → 0x106` (not taken) | 1 | 0 | 1 + 5 − 6 = 0 | 0 | ✓ |
| `0x104 → 0x10a` (taken) | 3 | 0 | 3 + 3 − 6 = 0 | 0 | ✓ |
| `0x106 → 0x108` | 1 | 0 | 1 + 4 − 5 = 0 | 0 | ✓ |
| `0x108 → 0x102` (back edge) | 3 | 1 | 3 + 7 − 4 = 6 | 6 × 1 = 6 | ✓ |
| `0x10a → exit` | 3 | 0 | 3 + 0 − 3 = 0 | 0 | ✓ |

and the exit condition `π(entry) − π(exit) + λ·(row's right-hand side) ≤ D·B`:
`68 − 0 + 6 × 0 ≤ 68` ✓. Why this proves the bound: sum the edge inequalities along any run;
the `π` terms telescope (Part 2, section 2.6) and the `λ·a` terms add up to `λ` times the
row's value on the run, which is ≤ 0 because the row holds. So the run's cycles are ≤ 68.
The back edge "borrows" 6 cycles per iteration from the row, and the entry "pays back"
60 = 6 × 10.

![potentials of the example](img/telescoping.svg)

`prop:cycles` (Lean `Cycles.cycles_sound`, `program_sound`) proves this for any graph with
calls (a call edge costs the callee's claimed bound; claims may be circular for recursive
functions, since the induction is on the depth of runs). The certificate is found by an
LP solver (scipy's HiGHS) and made exact (`benchmarks/cycles/ipet.py`); the checker never
solves anything.

Maroneze et al. (2014) validated the IPET solution of their CompCert WCET tool with a Farkas
certificate in Coq: the same idea, there on CompCert's assembly, here on any binary.

## 5.5 Third step: the checker builds the graph itself (`sec:machine`)

If the producer supplies the graph, the graph is trusted. In Paper III's format
(`crosscheck-binary-cycles`), the certificate contains **the machine code itself** (the
16-bit halfwords of the code region) and, per function, its entry and the addresses of its
instructions. The checker:

1. **decodes** each instruction with a decoder written in Lean (`Thumb.decode`): its size,
   its effect on the program counter (sequential, conditional branch to `t`, branch, call,
   return, or `stop` for anything not modelled) and its cycles;
2. checks the list of addresses is **closed** (every successor is in the list, no `stop`);
3. **builds** the graph (one edge per successor) and checks the cycle certificate on it.

`def:machine-run`, `thm:machine-cycles` (Lean `Thumb.binary_sound`, `translate`): every run of
the machine code — a sequence of instruction addresses in which each step is allowed by the
decoder — is a walk of the built graph with the same cycles, so the bound holds for it.

**The decoder is trusted**, as an instruction-set specification is. It is tested against the
interpreter's decoder on all 2¹⁶ halfwords and against llvm-objdump on the 24 285 instructions
of the kernels (`test_thumb.py`): no difference. It is not validated on hardware (Fox and
Myreen's ARM model in HOL4 is, and is the standard to aim at).

Result: all 107 functions certified; the checker checks 223 functions (with the run-time
division routines), 8 333 instructions, in 0.15 s. IPET bounds are below the timing schema for
60 functions, equal for 47.

## 5.6 Fourth step: loop bounds proved on the machine code (`sec:loops`)

The loop rows are still assumptions: they come from the source through the debug lines. To
remove them, the checker must see **why** the loop at `0x102` iterates at most 10 times: it
needs the values of `r0`, which the program-counter semantics of 5.5 ignores.

### The data semantics (`def:data-run`)

A state now holds the eight low registers `r0`–`r7`, the four flags, the stack pointer and
the memory. Each instruction has an **effect** (`Thumb.effect`, `Thumb.stackEffect`):

| Instruction | Effect in the model |
|---|---|
| `ADDS rd, rn, #k`, `SUBS`, `ADDS rd, rn, rm`, … | `rd := (rn ± k) mod 2³²`; flags of the addition or subtraction (AddWithCarry) |
| `MOVS rd, #k` | `rd := k`; flags: any |
| `MOV rd, rm` (low registers) | `rd := rm`; flags kept |
| `CMP rn, #k`, `CMP rn, rm`, `CMN` | registers kept; flags of `rn − k` (or `rn + rm`) |
| `LSLS rd, rm, #s` | `rd := rm·2^s` if that is below 2³², otherwise any value (two cases in every proof); flags: any. `LSLS rd, rm, #0` is `MOVS rd, rm`: `rd := rm` |
| `NEGS rd, rm` | `rd := (0 − rm) mod 2³²`; flags of that subtraction |
| `MVNS rd, rm` | `rd := 2³² − 1 − rm` (all bits flipped); flags: any |
| `STM rn!, {list}` | `rn := rn + 4·(number of registers)`; the registers of the list are kept |
| `LDM rn!, {list}` | the registers of the list: any; `rn := rn + 4·n` if `rn` is not in the list |
| `LDR rt, [pc, #i]` (literal pool) | `rt :=` the word of the code at that address (the code is assumed not to be written while the program runs) |
| `LDR rt, [sp, #i]` | `rt :=` the word at `sp + i` |
| `STR rt, [sp, #i]` | the word at `sp + i` `:= rt` |
| `SUB sp, #k`, `ADD sp, #k`, `PUSH`, `POP` | `sp` moved by the constant; `PUSH` writes the words just below `sp` |
| other loads | the destination register: any value |
| other stores, calls | memory: any word may change (except the frame, under `frame`) |
| `BL` (call) | `r0`–`r3`, flags: any; `r4`–`r7` and `sp` also any unless `abi` |
| everything else | the registers it may write: any; flags: any if it may change them |

"Any value" is a safe over-approximation: the model allows more behaviours than the real
processor, so a bound for all runs of the model is a bound for the real runs. A conditional
branch is taken **exactly when its condition holds** on the flags.

### The certificate (`def:loop-certificate`)

For each instruction `a`:

- a **kind** `k_a`: which operation set the flags (`none`, `add` or `sub`);
- two **ghost** variables `g₁, g₂`: the operands of that operation (after `cmp r0, #10`,
  `g₁ = r0`, `g₂ = 10`);
- an **offset** `δ_a` of the stack pointer from its value at the function's entry (or
  unknown);
- an **invariant** `I_a`: linear constraints over `r0`–`r7`, the ghosts, and the **tracked
  words** of the frame (the words at `sp₀ − k` for a list of offsets `k`).

For each certified loop: its header, its body, a scale `D`, a bound `N`, and a potential
`Φ_a` (an affine expression) for each instruction of the body.

The checker verifies, for every transition `a → a'` (every successor, every wrap-around case
of an addition, every disjunct of a branch condition), with Farkas certificates:

1. the successor's invariant holds after the instruction;
2. for every loop: `κ(a, a') + Φ(a', after) − Φ(a, before) ≤ 0`, where `κ` is `D` on a back
   edge into the header, `−N` on an entry edge into the header, 0 otherwise.

### The example, again

For the counting loop the producer finds:

| Instruction | Kind | Invariant (main facts) | Potential `Φ` |
|---|---|---|---|
| `0x102 cmp r0, #10` | none | `r0 ≤ 10` | `10 − r0` |
| `0x104 bge` | sub | `r0 ≤ 10`, `g₁ = r0`, `g₂ = 10` | `10 − r0` |
| `0x106 adds r0, #1` | sub | `r0 ≤ 9`, `g₁ = r0`, `g₂ = 10` | `10 − r0` |
| `0x108 b 0x102` | add | `1 ≤ r0 ≤ 10` | `11 − r0` |

Check a few transitions by hand:

- `0x104 → 0x106` (branch not taken): `bge` not taken means "signed `g₁ < g₂`", which the
  lemma `lem:cond-facts` turns into a disjunction of linear facts (split by the signs). With
  `g₁ = r0 ≤ 10` and `g₂ = 10`, every disjunct gives `r0 ≤ 9`: the invariant of `0x106`.
- `0x106 → 0x108` (`adds r0, #1`): `r0' = r0 + 1 + m·2³²` with `m ∈ {0, −1, 1}`. With `r0 ≤ 9`
  and `0 ≤ r0`, only `m = 0` is possible (the other cases contradict the invariant: a
  Farkas certificate of `0 ≤ −1`). Then `Φ(0x108, after) = 11 − (r0 + 1) = 10 − r0 = Φ(0x106)`:
  the potential does not increase. ✓
- `0x108 → 0x102` (back edge, `κ = D = 1`): `1 + (10 − r0) − (11 − r0) = 0 ≤ 0` ✓ — the
  potential drops by 1 per iteration.
- `0x100 → 0x102` (entry, `κ = −N = −10`): after `movs r0, #0`, `−10 + (10 − 0) = 0 ≤ 0` ✓.
- `0x104 → 0x10a` (exit): `0 + 0 − (10 − r0) ≤ 0` needs `r0 ≤ 10`: the invariant ✓.

`thm:machine-loops` (Lean `ThumbData.data_sound`): if all this checks, then on every run of the
data semantics the potentials **telescope** — summed along the run, the `κ` terms (which are
exactly the row's coefficients) are at most `Φ(entry) ≤ N` — so the loop's row holds, the run
is a run of 5.5, and the cycle bound applies. Nothing about the loop is trusted any more.
The Lean example `exData_sound` states it for this code: every data run costs at most 68
cycles, with no trusted row.

### Stack slots, and two assumptions

At `-O1`, a counter that must survive a call is often kept in the stack frame
(`str r0, [sp, #4]` … `ldr r0, [sp, #4]`). The model tracks the words of the frame accessed
through SP: the certificate lists their offsets, and gives the offset of SP at every
instruction; the checker verifies the offsets along every transition (`PUSH`, `SUB sp`
move SP by known constants), and knows which tracked word a load or store through SP touches.

A store through another register (`str r1, [r0, r5]`) or a call could, in principle, write
anywhere — including the frame. Two assumptions, each stated in the certificate and in the
checker's verdict, cover the usual case:

- **`abi`**: callees preserve `r4`–`r7` and `sp` (the Arm procedure call standard).
- **`frame`** (per function): no store through another register and no call writes the
  function's frame. This is true of C code without undefined behaviour **if the function
  never takes an address of its frame**, so the checker refuses `frame` for a function that
  writes an SP-derived address into a register (`add rd, sp, #i`, `mov rd, sp`).

### How the producer finds the certificate

`benchmarks/cycles/binloops.py`, untrusted:

1. **Offsets of SP** by data flow from the entry (an offset is dropped where two paths
   disagree).
2. **Kinds** of flags by data flow.
3. **Congruences** modulo powers of two (Part 2, end of section 2.11), computed on the
   checker's own post-expressions, so that the checker accepts exactly what was derived.
4. **Invariants** by abstract interpretation over **zones** (Part 2, sections 2.10–2.11): for
   registers, ghosts and tracked words; widening at loop headers to thresholds from the
   code's constants; three narrowing rounds; the facts of each branch rounded with the
   congruences (a counter stepped by 4 that exits at 80 gets `≤ 76`).
5. **Potentials** by trying `±x` for every register and tracked word and `±(x − y)` for the
   variables compared at the exits, with per-instruction constants computed as longest paths,
   and a scale `D` in {1, 2, 4, 8}. If that fails, **one linear program** looks for a
   potential with a *different* linear part at each instruction (Part 2, sections on Farkas
   and LP duality): the unknowns are the potentials' coefficients, the bound and the Farkas
   multipliers of every obligation; since the invariants are already fixed, every obligation
   is linear in these unknowns, and the program minimizes the bound (Colón & Sipma 2001;
   Alias et al. 2010 for one function per control point). Why it is needed: in
   `countnegative`, the loop counter lives in a register at some instructions and in a stack
   word at others, so no single expression `±x` decreases all along the loop. The solution
   is rational; it is rounded, scaled to integers (the scale becomes `D`) and proved again
   exactly. The solver (HiGHS) gets at most 5 s per program: the first runs without a limit
   hung for hours on one badly scaled program (constants up to 2³²).
6. **Farkas certificates** for every obligation: shortest paths in the difference graph, a
   negative cycle for contradictory cases, a linear program otherwise.
7. Anything that cannot be proved is **dropped** (an invariant constraint, or a loop, whose
   row then stays trusted). The checker decides.

### Results (`sec:evaluation`)

| Configuration | Kernel loops certified on the code (of 403) | Functions with a certified cycle bound |
|---|---|---|
| no assumption | 136 (131 without the exact shift below, 121 without the exact effects, 116 without the linear programs, 73 without congruences) | 115 |
| `abi` | 193 (183, 173, 167, 105) | 115 |
| `abi` and `frame` | 246 (229, 215, 175 before the frame-pointer exception, 169, 107) | 120 |

None of the 116 loops of the division routines (they shift) is certified. Every certificate
is accepted, and in the emulated runs no loop exceeds its certified bound. The 8 functions
gained over the 107 of 5.3 have loops that the source analysis does not bound but the binary
analysis does (`fac_fac`, the copy and fill loops of `md5` and `pm`); with both assumptions,
three functions of `bitcount` too.

Congruences made the largest difference: before them, 177 of the 210 loops whose counter
was tracked but had no potential left the loop on equality with a step above 1.

The frame pointer. Clang's `-O1` prologue sets up a frame pointer (`add r7, sp, #12`): r7
then holds an address of the frame. Until 2026-11-19 the checker refused `frame` for every
such function (190 of 265), and `frame` added only 2 loops. A pointer to the frame is only
dangerous if something can store through it, so the checker now allows that one instruction
provided r7 is never read afterwards except as the base address of a load (reading stack
arguments) or by the prologue's `PUSH` (which saves the caller's r7). The assumption itself
is unchanged, and the Lean proof never depended on this check: it only decides where the
assumption may be stated. `frame` is now refused in 26 functions (those that pass a local
array's address to a callee) and 215 loops were certified with both assumptions (175 before).

Exact effects (2026-11-19). Some instructions used to give "any value" although their result
is simple: `NEGS r0, r1` computes 0 − r1, `MVNS r0, r1` computes 2^32 − 1 − r1, `STM r0!, {...}`
and `LDM r0!, {...}` advance the base register by 4 bytes per listed register, and
`LDR r0, [pc, #i]` loads a constant stored in the code itself (the "literal pool"). These are
now exact in the Lean specification and in the producer. The literal load needs one new
trusted assumption: the code is not written while the program runs. Result: 229 loops with
both assumptions (233 without frame pointers); no loop lost, no bound changed. One snag:
the literal constants include addresses near 2^32, and with such numbers HiGHS (the LP
solver) sometimes gives up. The producer therefore retries a function, treating literal loads
as unknown again, when a loop is left uncertified, and keeps the better result; the checker
does not care how the certificate was found.

Exact shift (2026-11-20). `LSLS r1, r0, #10` multiplies r0 by 2^10. Compilers use it to build
constants (`movs r0, #1; lsls r1, r0, #10` makes 1024, a loop limit in `fft`) and
byte offsets. The result is exact as long as it fits in 32 bits; when it does not, the new
value is unknown. The checker treats the two cases like the wrap-around of a sum: the
certificate proves its claim once assuming no overflow and once assuming overflow (where
the value is any word). In Lean this is a new kind of value, `shl`, and the soundness proof
covers it; no new trusted assumption. The producer also got an exact fallback for Farkas
multipliers: when the LP returns multipliers too small to round, it solves
the same system exactly over the rationals. Result: 136 / 193 / 246 loops (251 without frame
pointers), in `fft`, `st`, `filterbank` and `bitcount`; no loop lost, no bound higher. A
first run lost one `jfdctint` loop (HiGHS again, on the constant 2^14), so the retry above
now also treats shifts as unknown.

Of the 157 kernel loops still not certified, 92
have a tracked counter but no potential (67 of them leave on equality). The
specification of effects, flags, conditions and stack effects is compared with the
interpreter on every 16-bit encoding (297 244 executions, no difference); 26 tests check that
altered certificates are refused.

## 5.7 The rest of Paper III's evaluation

- **OTAWA on the same binaries.** OTAWA 2.3 (an open-source WCET analyser) is given the loop
  bounds as flow facts on the binary loop headers; it computes IPET bounds for the same 107
  functions, in instructions and, with a small timing plug-in using the same cycle table, in
  cycles — never below our timing schema, none below an emulated run. This shows the bounds
  are usable by an industrial-style tool; it is not an independent timing model.
- **Other processors.** The same flow facts on OTAWA's own graphs of binaries for a
  Cortex-M4 and an M7 (OTAWA's STM32 models): 168 and 162 functions bounded; not checked
  against executions.
- **Stack bounds.** The high-water mark of the stack (Paper I, `prop:stack`) on the same
  binaries: 143 of 267 functions; 9 of the 10 `main` bounds equal the observed stack.
- **Time budgets after compilation.** `CROSSCHECK_DEADLINE_CYCLES(n)` / `_US(n)` are checked
  on the binary by `clang-plugin/scripts/crosscheck_link.py` (optionally with certified
  bounds, `--certify`), as a post-build step that fails when a budget is exceeded.

## 5.8 What is trusted, finally

| Item | Status |
|---|---|
| The analysis of the binary, the graph, the computation of the bound | **checked** (Lean) |
| The loop bounds (rows) of certified loops | **checked** (Lean), on the data semantics |
| The decoder, cycle table, effects, flags, conditions, stack effects | trusted specification; compared with our interpreter, not with hardware |
| That the code in the certificate is the binary's | trusted (a copy of the bytes) |
| `abi`, `frame` when used | stated assumptions |
| Rows of loops not certified on the code | trusted (from the source, through debug lines) |
| Interrupts, memory wait states | outside the model |

## 5.9 Prior work to cite and distinguish

- **Li and Malik** (1995): IPET. **Puschner and Koza** (1989): constraints on execution counts.
- **Maroneze et al.** (2014): verified WCET for CompCert, IPET validated in Coq; guarantees
  for CompCert-compiled code.
- **Sewell, Kam and Heiser** (2016, 2017): loop bounds of the seL4 binary proved with an SMT
  toolchain and C-level facts; CFG from a decompiler proved against the Cambridge ARM model.
  Their proofs trust SMT solvers; ours are certificates checked by a small verified checker,
  weaker (less of memory, no C-level facts) but self-contained.
- **Cullmann and Martin** (2007): aiT's data-flow loop bounds on executables — computed, not
  certified.
- **Crary and Weirich** (2000): resource bounds of typed assembly certified by type checking
  (time counted in calls).
- **Necula** (1997): proof-carrying code.

## 5.10 Paper III on one page

Cycle bounds of compiled code can be certified: a dual solution of the IPET program
(potentials and multipliers) is checked by a Lean-verified checker that decodes the machine
code and builds the graph itself, so the analysis of the binary leaves the trusted base. The
loop bounds can be certified on the same code: invariants on registers, flags and frame words,
and potentials that drop on back edges, checked by Farkas multipliers against a model of the
instructions' effects. On TACLeBench for a Cortex-M0, 115–120 functions get a certified cycle
bound and 136–246 of 403 loops are bounded on the code (251 built without frame pointers) with nothing trusted about them; the
rest keep their source bounds as assumptions.
