# Cycle bounds on a Cortex-M0

`run_cycles.py` turns CrossCheck's source loop bounds into **cycle bounds of compiled
code** for a processor whose instruction timings do not depend on the execution history:
the Arm Cortex-M0 (in order, no cache, no branch prediction), with zero-wait-state
memory.

```bash
python3 benchmarks/cycles/run_cycles.py --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13 \
    [--only bsort] [--json out.json] [--check] [--mul-cycles 32] \
    [--certify DIR --checker formalization/.lake/build/bin/crosscheck-check]
```

For each TACLeBench kernel (the single-file unit of `benchmarks/tacle/run_tacle.py`):

1. **Source loop bounds**: CrossCheck analyses the kernel (no annotation) and gives each
   loop a bound in the calling contexts of `main` (else for every call). The analysis is
   made for the binary's data model (`SOURCE_TARGET`: `--target=thumbv6m-none-eabi`, 32-bit
   `long` and pointers).
2. **Compilation**: Clang 18, `--target=thumbv6m-none-eabi -mcpu=cortex-m0 -O1 -g
   -fno-unroll-loops -ffreestanding -fno-builtin`, one object file; or, with `--gcc IMAGE
   --tag=.gcc`, arm-none-eabi-gcc in a Docker image run without network (`GCC_FLAGS`;
   image `benchmarks/hardware/Dockerfile`), see "GCC binaries" below.
3. **Static bound** (`wcet.py`): for each function, the control-flow graph of the code
   reachable from its entry (`m0.decode`, ARMv6-M Thumb); it must be reducible, without
   indirect jumps. Each natural loop is matched with the source loops through the debug
   line table (`wcet.Analysis.match`): of the lines of the loop's own instructions (not
   those of nested loops), those that lie in a source loop's range (its `line` to its
   `end_line`, from the plugin's report) are kept, and the innermost source loop holding
   all of them is chosen; lines outside every loop (often the function's first line, which
   compilers give to moved code) are ignored; if no source loop holds all of them, the
   largest bound among the source loops whose first line occurs; no bound if none does.
   Line-0 rows of the DWARF table (which llvm-objdump does not print) end the previous
   line (`zero_ranges`, with llvm-dwarfdump). The back edges are bounded by that source
   bound (see History for the rules tried before). The bound is the timing schema on the binary: a loop costs
   `N × (longest iteration) + (longest exit path)`, inner loops first, a call the callee's
   bound, a conditional branch the taken case (3 cycles).
4. **Check by execution** (`m0.Machine`, an interpreter of the instruction set written for
   this purpose): the kernel's `main` must return 0 (TACLeBench programs check their own
   result, which also checks the interpreter); every call of a function with a bound must
   take at most that many cycles, and every binary loop's back edges per entry at most its
   matched bound. `--check` fails otherwise. Run-time helpers without code (`__aeabi_*`
   division and floating point, `memset`, `memcpy`) are executed natively at no cost; a
   function that calls one has no static bound, so it is never compared.

Timings (`m0.cycles`): 1 cycle for data processing, 2 for loads and stores, `1+N` for
`LDM`/`STM`/`PUSH`/`POP`, `4+N` for `POP` with the PC (N counts the PC, as in the manual), 3 for `B` and a taken conditional branch, 1 for one not taken, 4 for `BL`,
3 for `BX`, `MULS` 32 (small multiplier; `--mul-cycles 1` for the fast one).

**What is trusted**: the timing table (the instruction summary of the Arm Cortex-M0
Technical Reference Manual, revision r0p0, Arm DDI 0432C, Table 3-1: `test_m0.py` holds
the table, 87 rows, and compares `m0.cycles` with it; `SVC`, `BKPT`, `WFE`, `WFI`, `CPS`
and the 32-bit system instructions stop the decoder, so a function that contains one gets
no bound; not checked here against hardware); that a binary loop
iterates at most as often as the source loop it is matched with (checked on the runs,
not proved); zero-wait-state memory, no interrupts (see `CROSSCHECK_INTERRUPT` for those).
The interpreter counts cycles with the same table, so the check validates the path
analysis and the loop matching, not the table.

`python3 benchmarks/cycles/test_m0.py` runs the interpreter's self-test (`selftest.c` and
`runtime.c` at `-O0` and `-O1`, results compared with the C semantics). Integer division
(`/`, `%`) is compiled from `runtime.c` (restoring division, 32 iterations) with each kernel,
so that its loop is bounded by CrossCheck and its cycles are counted; floating point
(software on the M0) has no code here and blocks the functions that use it.

## Results (2026-11-21)

29 kernels compiled; 28 return 0 when run (`fft` returns 1: it converts negative floats to
`unsigned long`, undefined behaviour in C, which Arm's conversion saturates and x86's wraps;
it is listed in `EXPECTED_FAILURE`). 156 s in total.

- **107 of the 267 kernel functions** receive a cycle bound (`runtime.c` not counted).
- **6 entry functions** (`main`) are bounded:

| Kernel | Bound (cycles) | Observed | Bound / observed |
|---|---:|---:|---:|
| binarysearch | 32,686 | 24,241 | 1.35 |
| bsort | 366,147 | 148,668 | 2.46 |
| countnegative | 449,615 | 327,923 | 1.37 |
| isqrt | 1,005,075 | 689,071 | 1.46 |
| jfdctint | 75,652 | 60,911 | 1.24 |
| matrix1 | 63,722 | 48,548 | 1.31 |

- **Checks**: 11 calls of bounded functions (the others are inlined at `-O1`) and 45 binary
  loops were compared with the run: **no violation**; over 10 of the calls, bound/observed is
  between 1.02 and 2.46. The eleventh, a function of `fft`, has a bound 970 times its observed cycles: its three nested loops are
  bounded by the product of their bounds, while at each outer iteration the count of one
  inner loop doubles and that of the other halves. `bsort`'s factor comes from its triangular nested loops, bounded
  as a rectangle (no amortisation).
- **Not bounded**, by cause: software floating point (`__aeabi_f*`, `__aeabi_d*`: most of the
  numeric kernels), source loops without a bound (data-dependent: `insertsort`,
  `binarysearch`, `quicksort`), and their callers.

## GCC binaries

The same kernels compiled by arm-none-eabi-gcc 13.2.1 (Ubuntu's package, Docker image
`benchmarks/hardware/Dockerfile`, run without network), `GCC_FLAGS`: `-mcpu=cortex-m0
-mthumb -O1 -g -fno-unroll-loops -ffreestanding -fno-builtin -fno-jump-tables
-fno-tree-loop-distribute-patterns` (no jump tables, which the decoder refuses; no
loops replaced by `memset`/`memcpy` calls):

```bash
python3 benchmarks/cycles/run_cycles.py --gcc armgcc:local --tag=.gcc --check --certify OUT \
    --checker formalization/.lake/build/bin/crosscheck-check --certify-loops --abi --frame --jobs 4 \
    --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13
```

| | GCC | Clang |
|---|---:|---:|
| functions with a cycle bound (of 267) | 107 (6 `main`) | 107 (6 `main`) |
| calls compared with emulated runs | 73 | 11 |
| binary loops compared | 65 | 45 |
| violations | 0 | 0 |
| `main`: bound / observed | 1.31-2.51 | 1.24-2.46 |
| functions with a certified cycle bound (none / `--abi` / both) | 110 / 110 / 112 | 116 / 116 / 121 |
| `main`: certified / observed (both assumptions) | 1.12-1.90 | 1.00-1.90 |
| kernel loops certified on the code (none / `--abi` / both) | 40 / 65 / 74 of 215 | 143 / 200 / 257 of 403 |
| loops of the division routines certified | 29 of 29 | 116 of 116 |

GCC inlines less at `-O1`, so many more calls are compared with the runs (73 instead of 11);
Clang's binaries have more loops, probably because inlining copies them (not counted). Why fewer of GCC's loops are
certified was not analysed.

The GCC binaries revealed three defects, all fixed before the figures above:

- **Data model** (a wrong bound): the source was analysed for the host (64-bit `long`), the
  binary is 32-bit; a loop of `sha_byte_reverse` over the bytes of a `long` got a bound of
  half its iterations, and GCC's binary, which keeps the function out of line, took 367
  cycles against a certified bound of 213 (Clang inlines it: no call was compared, its
  certified bound was 212 instead of 388). `SOURCE_TARGET` now gives the plugin the target.
- **Loop matching** (a wrong bound): GCC rotates the outer loop of `fft_bit_reduct` so that
  its back-edge branch carries the line of the inner loop's test, and the rule "line of the
  back-edge branch first" bounded it by 11 (1,023 iterations observed). Replaced by the
  matching on line ranges (`end_line` in the plugin's report; step 3 above); line-0 rows and
  discriminators of the DWARF line table are now read correctly. With it, `bsort`'s `main`
  (Clang) went from 369,779 to 366,147 cycles and GCC's `fft_bit_reduct` from 9.2e10 to 1.07e9.
- **Non-termination of the producer**: on GCC's `bitcount` the zone widening, followed by
  the closure, kept raising one bound (6,072 visits of one loop head in 7 hours). After
  `HARD_VISITS` (200) visits of a head, the entries still growing are forgotten
  (`binloops.forget_growing`); the result stays closed and the iteration stops. No Clang
  loop is lost by this (with a limit of 40, 20 were).

## Certified cycle bounds

`run_cycles.py --certify DIR --checker formalization/.lake/build/bin/crosscheck-check`
also gives every function an IPET bound with a certificate on its **machine code**
(`ipet.py`, format `crosscheck-binary-cycles` in `docs/certificate-format.md`): the code
region of the binary, and per function its entry, the addresses of its instructions, one
row per matched loop on pairs of addresses (`Σ back edges − N·Σ entry edges ≤ 0`, `≤ N` if
the header is the entry), the multipliers of the rows from the dual of the IPET linear
program (scipy's HiGHS, untrusted), made integer, and potentials computed exactly as
longest paths to the exit. The verified checker decodes the code itself (Lean
`Thumb.decode`: ARMv6-M Thumb and the Cortex-M0 cycles of `m0.py`), builds the graph (one
node per instruction, an edge per successor: a conditional branch costs 3 cycles taken,
1 not taken; `BL` 4 plus the callee's certified bound) and accepts or rejects the
certificate (Lean `Thumb.binary_sound`, Paper III `thm:machine-cycles`).

| | |
|---|---:|
| functions with a timing-schema bound | 107 |
| of which certified (checker: ACCEPTED) | **107** |
| certified bound below the schema's / equal / above | 60 / 47 / 0 |
| certified / schema bound: smallest, median | 0.72, 0.998 |
| calls compared with the runs, violations | 11, 0 |
| certificates checked (with the run-time division routines) | 223 functions, 8,333 instructions, 0.15 s |
| run time of all kernels, with certificates | 2.8 min |

| Kernel | Schema bound of `main` | Certified bound | Observed | Certified / observed |
|---|---:|---:|---:|---:|
| binarysearch | 32,686 | 27,222 | 24,241 | 1.12 |
| bsort | 366,147 | 285,349 | 148,668 | 1.92 |
| countnegative | 449,615 | 374,161 | 327,923 | 1.14 |
| isqrt | 1,005,075 | 806,676 | 689,071 | 1.17 |
| jfdctint | 75,652 | 64,760 | 60,911 | 1.06 |
| matrix1 | 63,722 | 63,447 | 48,548 | 1.31 |

The certified bounds can be lower because IPET costs each edge separately (a loop exit or
another not-taken branch is not charged as taken) and maximizes over consistent edge
counts rather than adding a longest iteration and a longest exit path; how much each
contributes was not measured. What the check removes from the trusted base is the analysis
of the binary, the graph construction and the computation of the bound; the Lean
specification of the processor (`Thumb.decode`), the copy of the code into the
certificate and the loop bounds (rows) stay trusted.

The Lean decoder is compared by `test_thumb.py` (CI) with `m0.py` on every 16-bit encoding
(each followed by a `BL` second half and by zero: 131,072 cases, size, kind, target and
cycles) and with llvm-objdump on the 24,285 instructions of the kernels' objects (kind,
size, target): no difference. Tests: `test_ipet.py` (machine code whose worst case is
known; certificates altered in each part, including the code, must be rejected), in CI,
where the certificates of all kernels are checked by the Lean checker job.

## Loop bounds certified on the machine code

`run_cycles.py --certify DIR --checker ... --certify-loops [--abi] [--frame]`: the loop
bounds are also certified on the machine code where `binloops.py` finds a certificate
(format version 2, `docs/certificate-format.md`; Lean `ThumbData.data_sound`, Paper III
`thm:machine-loops`). What cannot be proved is dropped; a dropped loop keeps its source
row, trusted.

**What a certificate holds.** Per instruction, the kind of operation that set the flags and
an invariant on `r0`-`r7` and the two operands of that operation, possibly a disjunction
(`alt` disjuncts and, per case of a transition, the disjunct it lands in, `pick`), and
congruences modulo powers of two (Granger), with which the facts of a branch are rounded:
a counter stepped by 4 that leaves its loop at 80 gets `≤ 76` (`congOk`, Lean
`congPE_sound`, `condFactsM_sound`), and facts on sums too (`gExpS`, `tightenS`, Lean
`tightenS_holds`: a byte offset counted from 2^32 − 16 up by 4 to zero). Per loop, a
potential that decreases on its back edges, with Farkas multipliers for every obligation.
The specification (`ThumbDataCore.effect`) is exact for sums and differences modulo 2^32
with the flags of AddWithCarry, `LSLS` by a constant, `NEGS`, `MVNS`, `STM`/`LDM`
write-back and literal-pool loads (assuming the code is not written during a run); other
instructions give any value. Two optional assumptions: `--abi` (callees preserve r4-r7 and
SP) and `--frame` (a function that takes no address of its frame other than the frame
pointer `ADD r7, SP, #i`, then read only as a load base, has its frame written only through
SP; checked where it may be stated by `frameUseOk`).

**How the producer finds them** (untrusted; the checker decides): a zone analysis of
differences of registers and tracked words of the frame (SP offsets per instruction),
widening at loop heads with thresholds at the wrap-around values of additions, descending
iterations, the zone split at an addition or subtraction that may wrap around and joined
after the next branch (trace partitioning, Mauborgne & Rival, ESOP 2005); potentials
`±r_i` or `±(r_i − r_j)` plus per-instruction constants with scale 1, 2, 4 or 8, else a
potential per instruction from one linear program over the obligations (`synth_lp`:
Colón–Sipma, Alias et al.; HiGHS, at most `LP_SECONDS` per program; retried without
presolve, with split constants, and with linear parts that follow a header variable,
`transport`, whose constants come first from longest paths); Farkas multipliers from
shortest paths, negative cycles, contradictions of one-variable bounds, the LP, or exact
rational elimination on the premises the LP used. Its own analysis ignores literal-pool
constants above `BIG` = 2^20 and, when a loop is left without a potential, analyses the
function again with literal loads and shifts as any value (`lit_any`): HiGHS fails
numerically on such constants. After `HARD_VISITS` visits of a loop head the zone entries
that still grow are forgotten, so that the analysis terminates.

### Results (2026-11-21)

| | no assumption | `--abi` | `--abi --frame` |
|---|---:|---:|---:|
| kernel loops certified (of 403) | 143 | 200 | 257 |
| ... built with `-fomit-frame-pointer` | 146 | 204 | 258 |
| ... certified bound below the source bound | 84 | 116 | 153 |
| ... no source bound | 59 | 84 | 104 |
| loops of the division routines certified (of 116) | 116 | 116 | 116 |
| functions with a certified cycle bound | 116 | 116 | 121 |
| loop rows still trusted in these bounds | 41 | 35 | 17 |
| ... built with `-fomit-frame-pointer` | 39 | 34 | 16 |
| run time with `--jobs 4` | 5 min | 8 min | 16 min |

Every certificate is accepted, and no back-edge count of the emulated runs exceeds a
certified bound. With both assumptions 373 of the 519 loops of the binaries are certified,
and 160 of the 174 functions with loops have no trusted row left. A certified bound is
never above the source bound (the producer keeps the source row then); those below it are
often below by one, since the binary counts back edges. `--frame` is refused in 26 of the
265 functions the producer analyses (25 without frame pointers): those that put another
address of their frame in a register, mostly to pass a local array to a callee. Functions
certified that the source bounds alone do not bound: `fac_fac`, `fir2dim_pin_down`,
`md5_R_RandomInit`, `md5_R_memset`, `md5_memcpy`, `md5_memset_x`, `pm_memcpy`, `pm_memset`,
`sha_fread`, and with both assumptions `bitcount_init`, `bitcount_init3`, `bitcount_init4`.

### The loops left (with both assumptions)

By the first obstacle the producer meets (146 loops, all in the kernels' own code): 86 have
a counter that the invariants track but no potential among the candidates (62 of them exit
on equality), 21 compare a value that is not tracked, 20 are in code where the SP offset is
unknown, 12 test flags set by an instruction whose effect is not modelled, 7 several of
these. The producer's own reasons: no potential found for 141, a potential whose bound
(2^31 − 2 or 2^32 − 2) exceeds the source bound for 5.

`classify_loops.py RUN.json` groups them by what drives their exits (for each exit, the
instruction that set its flags and the definitions reaching its operands inside the loop;
heuristic, for diagnosis only):

| group | loops | what would be needed |
|---|---:|---|
| A counter against a constant or a bounded limit | 40 | the counter's initial value: from a word of the frame (9), by `LSR` of an argument (9), from an argument (6), a constant (4), ...; `fir2dim` 0x242 starts from a frame word loaded outside the loop |
| B counter against a limit without a bound (a parameter) | 21 | bounds in the parameters, or calling contexts, on the binary |
| D exit on a value returned by a call | 22 | mostly soft-float comparisons (`for (i = 0.0f; i < 10; i += 0.1f)` in `cosf`) |
| F exit on data loaded from memory | 16 | invariants on memory (string and search loops) |
| C exit on the flags of a shift | 12 | `x >>= 8` until zero (`bitcount`, `sqrtf`): logarithmic potentials on the code |
| E counter shifted | 11 | logarithmic potentials (binary search, bit reversal) |
| I other (two counters, sums of registers) | 10 | |
| G word of the frame not tracked | 10 | SP offsets where they are unknown |
| H value through an approximated instruction | 4 | the `ADCS` loops (3, `bsort`) test Clang's `rsbs; adcs` form of `x == 0`, bubble sort's "swapped" flag (termination depends on the data); `x &= x - 1` in `bitcount` (as many iterations as set bits, no linear potential) |

### Tests and development cycle

Trusted, in addition to the decoder and timing table: the effects of the instructions on
`r0`-`r7` and the flags, the flags of additions and subtractions and the conditions
(`Thumb.effect`, `flagsAdd`, `flagsSub`, `condHolds`), compared by `test_effect.py` (CI)
with `m0.py` on every 16-bit encoding in three random states, with and without the
assumption on callees: 297,244 executions, no difference. `test_binloops.py` (CI):
certificates altered in their bounds, scales, potentials, invariants, kinds, multipliers,
tracked words, SP offsets, congruences, assumptions or code must be rejected, and so must
certificates of small loops whose instruction is changed (classes `ExactEffects`, `EXACT`,
`Disjunctions`, `WrapToZero`).

1. `python3 -m pytest -q test_binloops.py test_ipet.py test_effect.py` (under a minute);
2. a subset: `run_cycles.py --certify-loops --abi --frame --jobs 4 --only bitcount --only
   bitonic --only countnegative --only fft --only st --only isqrt --only matrix1 ...` (a few
   minutes), then `compare_runs.py OLD.json NEW.json --check` (fails on a loop lost or a
   bound higher);
3. the full run with both assumptions (`--jobs 4`), then `compare_runs.py --check`;
4. the six runs (default and `.nofp` builds; no assumption, `--abi`, both) only before the
   figures of the papers and of this file are updated.

`BINLOOPS_CHECK_CLOSE=1` compares each incremental closure of a zone with the full one.

## OTAWA on the same binaries

`run_otawa.py` gives CrossCheck's loop bounds to [OTAWA](https://github.com/statinf-otawa/otawa-project)
(Ballabriga, Cassé, Rochange, Sainrat, SEUS 2010; version 2.3.0 here), which is not part
of this repository: build its image yourself (`docker build . --target otawa-dev -t
otawa:dev` in its project). The script runs it without network.

```bash
python3 benchmarks/cycles/run_otawa.py --lld PATH/TO/ld.lld --check \
    --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13   # on the author's machine
#   --lld: any LLVM linker for Arm; a Rust toolchain has one (`rust-lld`)
```

Each kernel is linked into an executable (no library: the soft-float functions stay
undefined, and the functions that call them have no bound, as above). For every function
with a bound of the timing schema, the bounds of its loops are written as FFX flow facts
on the headers of the binary loops, by label and offset (`<loop label="f" offset="0x16"
maxcount="N+1"/>`: a source bound `N` counts executions of the body, OTAWA's `maxcount`
executions of the header per entry of the loop), and `owcet -s trivial -p stages=1`
computes a bound by IPET, in executed instructions (no Cortex-M0 description was written
for OTAWA, so this is not a cycle bound). The program is then run by `m0.py`.

| | |
|---|---:|
| functions given to OTAWA (those with a cycle bound above) | 107 |
| ... for which OTAWA computes a bound | 107 (6 entry functions `main`) |
| flow facts | 199 |
| calls completed by the runs and compared | 11, **no bound below the executed instructions** |
| bound / executed, geometric mean (largest) | 2.32 (756: `fft_bit_reduct`, product of nested bounds) |
| OTAWA's bound at most the timing schema's (same unit) | 52 functions; above for 55 |

**In cycles** (`--timing m0`): `otawa/m0time.cpp`, compiled against OTAWA in the same image
by the script, loads the ELF with OTAWA's ARM loader, builds OTAWA's control-flow graphs,
sets the time of each basic block to the sum of the Cortex-M0 cycles of its instructions
(`<kernel>.times`, written from the timing table of `m0.py`, Table 3-1 of the manual; a
conditional branch counted as taken, OTAWA's edge times not used) and requires OTAWA's
IPET WCET. The Cortex-M0 has no cache and fixed instruction times, so no pipeline model is
needed. Shared with the timing schema: the table and the loop bounds; not shared: the
graphs and the computation of the bound.

```bash
python3 benchmarks/cycles/run_otawa.py --lld PATH/TO/ld.lld --timing m0 --check \
    --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13
```

| | |
|---|---:|
| functions bounded by OTAWA, in cycles | 107 of 107 |
| calls compared | 11, **no bound below the executed cycles** |
| bound / executed, geometric mean (largest) | 2.69 (1,054: `fft_bit_reduct`) |
| OTAWA's bound / timing schema's | never below; equal for 52, larger for 55 (median 1.007, largest 1.29: `matrix1` `main`) |

OTAWA's bound is above the schema's where a loop header gets one more execution than the
body and the schema counts only the exit path for it. **Why label and offset**: the FFX
that the plugin exports designates a loop by source file and line; on these `-O1`
binaries OTAWA could not place such facts (inlined callees, rotated loops: "no limit for
the loop at ..."), so the matching of binary loops to source loops is done by `wcet.py`,
as for the cycle bounds. That matching is checked on runs, not proved.

**The loops of OTAWA's graphs** (`--matching otawa`): the same run with the
binary loops taken from OTAWA's own control-flow graphs and matched by `otawa_flow.py` (the
matching used for the processors modelled by OTAWA, below), instead of `wcet.py`'s:
107 of 107 functions bounded, none refused by the matching, 11 calls compared with **no
bound below the executed instructions**, the same bounds per function as with `wcet.py`'s
matching for all 107 (99 flow facts, written for the functions reachable from those given to OTAWA; 199 with `wcet.py`'s matching, 108 of them for the loops of the run-time division functions, written for every kernel).

## Other processors: OTAWA's STM32 models

`otawa_flow.py` gives CrossCheck's source loop bounds to OTAWA on any binary it decodes:
in a container without network, `mkff` lists the loop headers of the code reachable from
a function and `dumpcfg --cfg-raw -S` its basic blocks; each natural loop is matched with
the source loops through the debug lines by the rule of `wcet.py` (the innermost source
loop whose line range holds the loop's own lines; the largest bound if several match) and written as a flow
fact by label and offset (`maxcount` = bound + 1). A call graph read from the disassembly
refuses, for every function that reaches them, recursion, indirect calls and jumps, jump
tables (TBB/TBH), branches into another function, calls of undefined symbols (linked to
the next instruction when unresolved symbols are ignored) and loops without a matched
bound. `test_otawa_flow.py` tests these rules without OTAWA (CI). It is the back end of
`clang-plugin/scripts/crosscheck_link.py --processor stm32f4|stm32h7`.

`run_stm32.py` compiles each kernel for a Cortex-M4 with its single-precision FPU
(`-mcpu=cortex-m4 -mfloat-abi=hard -mfpu=fpv4-sp-d16 -O1 -g`), links it at the addresses of
an STM32 (flash from 0x08000000, RAM from 0x20000000: OTAWA's model gives an address outside
its memory banks the worst latency) and asks OTAWA's `stm32` script for the WCET of every
function, with `ARCH=0` (STM32F427, Cortex-M4: pipeline, no cache) and `ARCH=1`
(STM32H753, Cortex-M7: pipeline, caches, branch history table).

```bash
python3 benchmarks/cycles/run_stm32.py --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13 \
    [--m0-json cycles.json] [--json stm32.json]
```

| | Cortex-M4 (`stm32f4`) | Cortex-M7 (`stm32h7`) |
|---|---:|---:|
| functions (29 kernels) | 267 | 267 |
| with a WCET from OTAWA | **169** | **163** |
| ... entry functions `main` | 8 | 7 |
| of the 107 bounded on the Cortex-M0 (above) | 107 | 104 |
| bounded here and not on the Cortex-M0 | 62 | 59 |

Flow facts: 542. Not bounded (same for both, 98 functions): a reached loop matched with a
source loop without a bound, 59; a call of an undefined symbol (double-precision floating
point, `memcpy`...: no run-time library), 24; a loop that matches no source loop, 7;
recursion, 6; a jump table, 2. On the Cortex-M7, OTAWA gives no result within 300 s for 6
more functions (its cache analysis; `basicmath___ieee754_acosf` in three kernels and three
functions of `jfdctint`). Of the 62 functions bounded only on the Cortex-M4, 57 call a
single-precision floating-point function of the run-time library on the Cortex-M0 (no code
there; an FPU instruction on the M4) and 5 call a function without a bound. The run takes 29 minutes, most of it the
Cortex-M7 analysis (at most 300 s per function, `--timeout`).

Bounds of the `main` functions, in cycles:

| Kernel | Cortex-M0 (timing schema, above) | Cortex-M4 (OTAWA) | Cortex-M7 (OTAWA) |
|---|---:|---:|---:|
| binarysearch | 32,686 | 47,228 | 34,433 |
| bsort | 366,147 | 8,008,798 | 3,647,363 |
| complex_updates | -- | 72,360 | 15,275 |
| countnegative | 449,615 | 675,320 | 347,632 |
| iir | -- | 74,953 | 12,010 |
| isqrt | 1,005,075 | 22,803,665 | 2,307,706 |
| jfdctint | 75,652 | 156,189 | -- (timeout) |
| matrix1 | 63,722 | 970,223 | 760,826 |

The Cortex-M4 bounds are 1.4 to 23 times those of the Cortex-M0 for the same source, on a
faster core; we did not analyse where OTAWA's time goes, but its STM32F427 model gives
every memory bank, the flash included, a latency of 50 cycles (see above). The three
processors are not compared here: the numbers show that the same source bounds reach
OTAWA's models, not how fast these processors are.

**What these numbers are**: OTAWA's WCET on OTAWA's models of the two processors, with
CrossCheck's loop bounds as the only flow facts. They are **not checked against
executions** (there is no simulator of these processors here), and the models are OTAWA's:
its STM32F427 memory file gives every bank a latency of 50 cycles and says that the values
"could not be found in official datasheets", so the Cortex-M4 bounds are as pessimistic as
that assumption. What this measures is the interface: how many functions get a WCET on
another instruction set (Thumb-2, with hardware division and single-precision floating
point) from the same source bounds, with the matching that is checked on the Cortex-M0
above.

## Stack bounds

`stack.py` bounds the stack of every function of the same binaries: the largest depth of
the stack pointer below its value at entry, callees included. The depth is computed on the
control-flow graph (`push`, `pop`, `sub sp`, `add sp`); it must have one value at every
instruction and be 0 at every return. The rule over calls is a maximum, not a sum:
`stack(f) = max(own depth, depth at a call + stack(callee))` (Lean:
`Stack.highWater_le_of_bound`, Paper I `prop:stack`). No loop bound is needed, so more
functions get a stack bound than a cycle bound. `run_cycles.py` computes them and checks
each against the run: for every activation, the stack pointer at entry minus the lowest
value seen until it returns (`--check` fails on a violation).

| | |
|---|---:|
| functions with a stack bound | **143 of 267** |
| entry functions (`main`) with a stack bound | 10 of 29 |
| calls compared with the run | 24, **no violation** |
| of which the bound equals the observed stack | 19 |

| Kernel | Stack bound of `main` (bytes) | Observed |
|---|---:|---:|
| binarysearch | 56 | 56 |
| bsort | 28 | 28 |
| countnegative | 64 | 64 |
| fac | 24 | 24 |
| insertsort | 32 | 32 |
| isqrt | 52 | 52 |
| jfdctint | 104 | 104 |
| matrix1 | 36 | 36 |
| md5 | 584 | 552 |
| prime | 56 | 56 |

(`fac` is recursive in the source; at `-O1` the compiler turns its recursion into a loop.)

No bound, by cause (124 functions): a call to a software floating-point helper, which the
interpreter provides in Python, without code (84); a call to such a function (32); the
stack pointer written from a register whose value is not a constant loaded just before
(4; `ldr r, =-size; add sp, r`, the way large frames are reserved, is handled); recursion
in the binary (4: `bitonic`, `quicksort`, `recursion`). A recursive function could be bounded
from a recursion depth (`Stack.highWater_le_depth`); this is not implemented.

What the bound covers: the stack of the program's own code. Not counted: exception frames
(8 words per interrupt taken on this processor), and anything a real run-time library
would add. The decoder and the control-flow graph are those of the cycle analysis, and
the check is against the same interpreter: it tests the path analysis, not the decoder.

## History

The changes that moved the figures above, newest first (each run: no loop lost, no
certified bound higher, every certificate accepted, no emulated run above a bound, unless
said otherwise).

- **2026-11-21, GCC binaries, line ranges, target data model.** The GCC runs revealed three
  defects ("GCC binaries" above). The source had been analysed with the host's 64-bit
  `long`: `sha_byte_reverse` had a certified bound of 213 cycles, 367 observed in GCC's
  binary. Loop matching rules tried before line ranges: the largest bound among all lines of
  a loop's instructions made `matrix1_main` 100 iterations instead of 10 (a preheader
  instruction inherited another loop's line; bound 105 times the observed cycles, 80 with a
  first fix); the lines of the back-edge branches first gave 1.31 but matched GCC's rotated
  outer loop of `fft_bit_reduct` with its inner loop (bound 11, 1,023 iterations observed).
  With line ranges and the line-0 fix: `bsort` `main` 369,779 → 366,147 cycles (ratio
  2.49 → 2.46), one more loop of `minver` certified (0x104: its function's `while (1)`
  loop, line 167, which CrossCheck does not bound, had been matched with a bounded source
  loop, a wrong trusted bound; the function calls soft-float code and is never run), counts
  142 / 199 / 256 → 143 / 200 / 257; OTAWA geometric means 2.36 → 2.32 and 2.74 → 2.69;
  `otawa_flow.py` switched to the same rule (with its old rule and the line-0 fix it lost
  `bsort_BubbleSort`, 104 of 107 functions); STM32 models 168 / 162 → 169 / 163 bounded
  functions. `HARD_VISITS` added: on GCC's `bitcount` the widening and closure kept raising
  one bound (6,072 visits of a head in 7 hours); a limit of 40 lost 20 Clang loops, 200
  none.
- **2026-11-20, rounding of sums (wrap to zero).** Clang counts some byte offsets from
  2^32 − 16 up by 4 to zero (`adds r3, #4; bne`); the checker rounds facts on sums with the
  congruences (`exZero_sound`, `exZero_needs_cong`); the producer gained wrap-around
  thresholds, virtual premises in its Farkas proofs and longest-path constants for
  transported potentials (`synth_transport`). 136 / 193 / 250 → 142 / 199 / 256 (+6:
  `bsort`, `fft`, `fir2dim`); without frame pointers 140 / 198 / 252 → 146 / 204 / 258;
  trusted rows 43 / 37 / 19 → 41 / 35 / 17. Exact `ADCS`/`ANDS` were examined and not done.
- **2026-11-20, disjunctive invariants.** The division routines count
  `for (i = 31; i >= 0; i--)` as `subs; adds; bhs`, exiting when the counter wraps to
  2^32 − 1: between subtraction and branch `r3 ≤ 30 ∨ r3 = 2^32 − 1`. Checker: `alt`/`pick`
  (no new assumption). Producer: zone split at a possible wrap-around; HiGHS failed on
  these programs, hence the exact detection of contradictions and the retries (no presolve,
  split constants, `transport`). The 116 loops of the division routines certified (none
  before); kernels 136 / 193 / 246 → 136 / 193 / 250; trusted rows 159 / 153 / 137 → 43 /
  37 / 19.
- **2026-11-20, run time.** `pm` alone took 77 minutes (zones of 44 variables). The join of
  closed zones is no longer closed again (Miné, PADO 2001), constraints are closed
  incrementally, images are completed only on unknown variables, unused analyses removed,
  results of the division routines reused, kernels in parallel (`--jobs`): the run with
  both assumptions 103 → 18 minutes, certificates identical.
- **2026-11-20, exact shift.** `LSLS rd, rm, #s` exact (`Val.shl`); exact Farkas
  multipliers by Gaussian elimination when the LP's are too small to round. 131 / 183 / 229
  → 136 / 193 / 246; four bounds of `bitcount` 2^31 − 2 → 255; `jfdctint` 0x172 first lost
  (HiGHS), recovered by `lit_any` also for shifts.
- **2026-11-19, exact effects.** `NEGS`, `MVNS`, `STM`/`LDM` write-back, literal loads.
  121 / 173 / 215 → 131 / 183 / 229. The literal constants made HiGHS fail on three loops
  certified before, hence `BIG` and `lit_any`.
- **2026-11-19, frame pointer.** `--frame` no longer refused for the prologue
  `add r7, sp, #i` alone (`frameUseOk`, `regsRead`): with both assumptions 175 → 215;
  refusals 190 → 26.
- **2026-11-18, potentials per instruction (linear programs).** 116 / 167 / 169 → 121 / 173
  / 175 (`countnegative`, `isqrt`); `LP_SECONDS` after a run hung on `jfdctint`.
- **2026-11-18, congruences.** 73 / 105 / 107 → 116 / 167 / 169: most uncertified loops
  exited on equality with a counter stepped by more than 1. `ipet.py` stopped rounding the
  multipliers up when exact fractions give a smaller bound: 10 cycle bounds lower (up to 8 %).
- **2026-11-18, words of the frame.** Tracking SP-relative words raised 72 / 94 to the
  first counts above.
- **2026-11-17, certified cycle bounds** (IPET certificates on the machine code); the OTAWA
  runs and the STM32 models.
- **2026-11-16, first results** of the timing schema, OTAWA and the stack bounds.

