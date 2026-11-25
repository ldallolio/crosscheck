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
   this purpose, with a core in C for long runs, `m0core.c`, compared with QEMU by
   `run_qemu.py`): the kernel's `main` must return 0 (TACLeBench programs check their own
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
-fno-tree-loop-distribute-patterns` (no jump tables: GCC's Thumb-1 tables call libgcc
helpers, `__gnu_thumb1_case_*`, that rewrite the PC; no loops replaced by `memset`/`memcpy`
calls):

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
| kernel loops certified on the code (none / `--abi` / both) | 40 / 66 / 75 of 215 | 143 / 200 / 260 of 403 |
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

**The calling convention, checked (2026-11-22).** With `--abi`, the checker no longer takes
the callees' preservation of `r4`-`r7` and SP on trust: it verifies on the code of every
function that the registers of `r4`-`r7` it writes are pushed at its entry and popped by
every return at the right SP offset, and that its stores through SP stay below them (Lean
`ThumbConv`, `convOk`, `data_sound_conv`; Paper III `thm:machine-conv`). What remains is
the hypothesis that no store through a pointer and no callee overwrites the saved words (no
stack smashing). The checker prints `callees' preservation of r4-r7 and SP checked on the
code of every function`, or names the functions where the convention is not established.
On the 29 kernels it is established everywhere, with `--abi` and with `--abi --frame`; the
loop counts are those of the tables below. The producer gives the SP offsets of every
function, which the check needs (before, the functions without certified loops had none,
and the check failed in 9 kernels). Test: `test_binloops.py`
`Producer.test_convention_checked`.

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
Colón–Sipma, Alias et al.; HiGHS, limited in iterations, `lp_maxiter`; retried without
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
| kernel loops certified (of 403) | 143 | 200 | 260 |
| ... built with `-fomit-frame-pointer` | 146 | 204 | 261 |
| ... certified bound below the source bound | 84 | 116 | 153 |
| ... no source bound | 59 | 84 | 107 |
| loops of the division routines certified (of 116) | 116 | 116 | 116 |
| functions with a certified cycle bound | 116 | 116 | 121 |
| loop rows still trusted in these bounds | 41 | 35 | 17 |
| ... built with `-fomit-frame-pointer` | 39 | 34 | 16 |
| run time with `--jobs 4` | 5 min | 8 min | 16 min |

Every certificate is accepted, and no back-edge count of the emulated runs exceeds a
certified bound. With both assumptions 376 of the 524 loops of the binaries are certified,
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

## Floating point on its machine code: a run-time library linked (2026-11-23)

The Cortex-M0 has no floating-point unit: each float or double operation calls a routine of
the run-time library (`__aeabi_fadd`, `__aeabi_ddiv`, ...). In the runs above these routines
have no code (the interpreter computes them in Python, at no cycle cost), so every function
that reaches one has no bound. `run_cycles.py --rtlib compiler-rt|libgcc` links each object
with a real library first (`ld -r`, so that the archive members the object needs are added
as the toolchain's link would add them; `runtime.c`'s integer division stays), and the
routines are analysed, certified and run on their machine code like the kernels' own:

- `compiler-rt`: LLVM's soft-float routines and the 64-bit multiply and shifts they call
  (`COMPILER_RT_FILES`, Apache-2.0 with LLVM exception), fetched at tag `llvmorg-18.1.8` (the
  Clang used here) into `.cache/` (never vendored) and compiled by Clang at `-O2`. No loop,
  no indirect jump.
- `libgcc`: the Cortex-M0 multilib (`thumb/v6-m/nofp`) of arm-none-eabi-gcc 13.2.1 in the
  Docker image, unmodified. Its float and double divisions (`divsf3`, `divdf3`) dispatch the
  special cases through jump tables (`mov pc, r`) kept in `.rodata`; since 2026-11-24 the
  certificate's code includes the read-only data that follow the code, and these jumps are
  followed (see "Tables in read-only data and tables without a range check" below).

The link runs in `--link-image` (default `armgcc:local`, without network) or, with
`--link-image ''`, with the `arm-none-eabi-ld` of the machine (Ubuntu's
`binutils-arm-none-eabi`; CI). The functions the library adds are counted apart from the
kernels' (the 267 functions below are the kernels' own).

| all 29 kernels, `--certify-loops` | before | compiler-rt | libgcc |
|---|---:|---:|---:|
| functions with a certified cycle bound, no assumption | 116 | 181 | |
| ... with `--abi --frame` | 121 | 187 | 187 |
| entry functions (`main`) certified, `--abi --frame` | 6 | 10 | 10 |
| functions with a timing-schema bound | 107 | 172 | 161 |
| functions with a stack bound | 151 | 256 | 247 |
| entry functions with a stack bound | 12 | 26 | 23 |
| kernel loops certified, `--abi --frame` (of 403) | 260 | 261 | 261 |

Every certificate is accepted and no emulated run exceeds a cycle, loop or stack bound
(`--check`). The calling convention is not established everywhere any more, so `abi` is
assumed for the functions the checker names: with compiler-rt in 1 of the 29 programs
(`ludcmp_test`, which gets a certificate now that it has a bound: it restores SP from its
frame pointer, `subs r6, r7, #7; subs r6, #5; mov sp, r6`, which the SP offsets do not
follow); with libgcc in 13, all in its hand-written assembly routines (`__aeabi_cfrcmple`,
`__aeabi_cdrcmple`, `__aeabi_d2iz`, `__aeabi_f2uiz`; `__aeabi_cfrcmple`, for instance, swaps
its operands and branches into `__aeabi_cfcmple`). With compiler-rt, the certified bounds of the entry functions are 1.00
to 5.53 times the observed cycles:

| Kernel | Certified (cycles) | Observed | Ratio |
|---|---:|---:|---:|
| binarysearch | 24,895 | 24,241 | 1.03 |
| bsort | 282,526 | 148,668 | 1.90 |
| complex_updates | 102,437 | 42,672 | 2.40 |
| countnegative | 330,607 | 327,923 | 1.01 |
| iir | 23,926 | 6,840 | 3.50 |
| isqrt | 774,612 | 689,071 | 1.12 |
| jfdctint | 61,923 | 60,911 | 1.02 |
| ludcmp | 1,545,949 | 279,707 | 5.53 |
| matrix1 | 48,548 | 48,548 | 1.00 |
| st | 10,133,978 | 6,067,895 | 1.67 |

The four new ones (`complex_updates`, `iir`, `ludcmp`, `st`) compute in floating point; why
`ludcmp` and `iir` are further from their runs (the paths through the routines, their data or
the loops) was not analysed. libgcc's routines are faster than compiler-rt's
(`complex_updates`: 52,352 certified, 34,623 observed; `iir`: 13,888 and 6,799). The observed
cycles of the default runs leave the floating-point routines out (they cost nothing there):
`st` takes 6.07 million cycles with compiler-rt, 4.76 million with libgcc, 1.78 million
without code for them. The library's code is trusted to be the code the program is linked
with, as the kernels' code is; the run with compiler-rt takes 20 minutes with `--jobs 4`.
With libgcc, the figures before its tables were followed were 173 certified functions, 8
entry functions, 158 schema bounds and 204 / 15 stack bounds; `ludcmp` (891,004 certified,
221,543 observed) and `st` (5,995,251 and 4,758,503) were added.

## Larger programs and jumps through tables (2026-11-24)

```bash
python3 run_cycles.py --category sequential --category app --only lift --check --certify DIR \
  --checker ../../formalization/.lake/build/bin/crosscheck-check --certify-loops --abi --frame \
  --rtlib compiler-rt --json lift.json
```

TACLeBench's 23 `sequential` and 2 `app` programs, run one at a time with a limit of one
hour each (`--category`; the source analysis with `CROSSCHECK_TACLE_TIMEOUT=5400` for
`cjpeg_transupp`, whose plugin run takes about 30 minutes). Work-copy fixes
(`SOURCE_FIXES`): the debugging `printf` of `anagram` and `huff_enc`, whose declaration is
commented out at the pinned revision. `cjpeg_transupp` reads
`cjpeg_transupp_input5_2[65..71]` of an array of 65 (its "lower right corner" loop runs with
`i == 8`), so its expected checksum holds for x86's layout of the globals only: on the
Cortex-M0 it returns 1 (`EXPECTED_FAILURE`, as `fft`). Since 2026-11-25 (the changes of
"Analysis time" and "Deterministic limits") all 25 programs finish: 1,293 s for the 25 on a
40-core machine (`--jobs 10 --func-jobs 4`), `mpeg2` 692 s and `susan` 634 s alone
(`--func-jobs 8`); before, `ammunition` did not finish within an hour, and `mpeg2` and
`susan` took 2,981 s and 3,560 s on the author's machine, one program at a time.

| program | functions | certified | loops certified on the code | stack bounds | `main` certified |
|---|---:|---:|---:|---:|:-:|
| adpcm_dec | 17 | 13 | 23 of 28 | 17 | no |
| adpcm_enc | 19 | 15 | 27 of 31 | 19 | no |
| ammunition | 74 | 44 | 638 of 1,135 | 57 | no |
| anagram | 26 | 13 | 29 of 51 | 20 | no |
| audiobeam | 36 | 28 | 20 of 43 | 36 | no |
| cjpeg_transupp | 11 | 4 | 63 of 87 | 11 | no |
| cjpeg_wrbmp | 8 | 3 | 16 of 17 | 5 | no |
| dijkstra | 8 | 4 | 12 of 16 | 8 | no |
| epic | 9 | 1 | 15 of 67 | 9 | no |
| fmref | 19 | 14 | 25 of 34 | 19 | no |
| g723_enc | 18 | 16 | 26 of 32 | 18 | no |
| gsm_dec | 24 | 17 | 27 of 48 | 24 | no |
| gsm_enc | 36 | 28 | 57 of 79 | 36 | no |
| h264_dec | 5 | 2 | 15 of 17 | 5 | no |
| huff_dec | 11 | 7 | 14 of 32 | 11 | no |
| huff_enc | 18 | 9 | 15 of 38 | 12 | no |
| lift | 16 | 16 | 20 of 20 | 16 | yes |
| mpeg2 | 17 | 8 | 41 of 62 | 12 | no |
| ndes | 8 | 4 | 12 of 20 | 4 | no |
| petrinet | 4 | 2 | 10 of 10 | 2 | no |
| powerwindow | 51 | 49 | 77 of 78 | 51 | no |
| rijndael_dec | 13 | 8 | 11 of 18 | 9 | no |
| rijndael_enc | 14 | 9 | 11 of 19 | 10 | no |
| statemate | 10 | 10 | 5 of 5 | 10 | yes |
| susan | 41 | 20 | 38 of 83 | 31 | no |
| **25 programs** | **513** | **344** | **1,247 of 2,070** | **452** | **2** |

Functions and loops include those of compiler-rt. 535 of `ammunition`'s certified loops are
in `ammunition_arithm_test` (535 of its 910 loops), whose search reaches its work budget
and which receives no cycle bound. 32 of the linear
programs of 14 functions (in `anagram`, `cjpeg_transupp`, `epic`, `gsm_dec`, `h264_dec`,
`huff_enc`, `mpeg2`, `susan`) are stopped after 60 CPU seconds ("Deterministic limits");
a second run stopped 31 and gave the same 25 certificates, byte for byte. No certificate is rejected and no
emulated run exceeds a cycle or stack bound. `lift` (`main`: 1,157,990 cycles certified,
883,716 observed) and `statemate` are bounded entirely. What keeps `main` uncertified in the
others is listed by the run ("What keeps `main` uncertified", below).

**Jumps through tables.** A `switch` compiled to a table (`cmp rI, #n; bhi default;` ...
`add pc, rm` or `mov pc, rm`) was an indirect jump, refused. `jumptable.py` now finds the
window of the jump (the `cmp`, the `bhi`, or a `bls` to `start + 6` over `b default`, the
form Clang uses when the default case is beyond the reach of a conditional branch) and
evaluates it for every index `0..n` on the code, as the checker does (Lean `jumpOk`): the
certificate lists the targets (`jumps`), the checker evaluates the window again, checks that
nothing branches into it but from the instruction before (`interiorOk`), and Lean proves
that every data run follows a listed target (Paper III `prop:jump-table`, `jump_good`,
`steps_good`). The 25 programs have 8 such jumps (`gsm_dec` 2, `gsm_enc` 4, `lift` 1,
`ammunition` 1), all recognised; 3 are in functions that receive a certificate (`gsm_enc`'s
`Autocorrelation` and `Long_term_analysis_filtering`, `lift`'s `check_run`). Not followed: a
table whose index is bounded only by a loop or by constants set on several paths
(`bitcount_main`, the second jump of `sha_wordcopy_fwd_aligned`; see below), calls through
pointers. The
calling convention is checked in these functions too (Lean `convAll` along the targets;
before 2026-11-24 it stayed assumed there): with the new checker the certificates of the
25 programs report it as established on the code of every function. Tests: `test_jumptable.py` (a switch
in both forms certified and accepted; a dropped target, a moved window, a widened range
check and a branch into the window rejected, the last shown on `m0.py` to leave the
function; the convention established with a jump, and not established when a case reached
only through the table writes `r4`; Lean's exact values of `ADD rd, PC`, `ADR` and the loads from the code, and its
jump destinations, against `m0.py` on more than 1,000 states).

**Robustness.** On these programs the producer met two problems the kernels never showed:
a recursion limit (the depth-first searches of `wcet.py` were recursive; now iterative) and
analyses that run for hours on large functions. The loop certifier now has a budget per
function (600 CPU seconds when these programs were first run; in work units since
2026-11-25, see "Deterministic limits"): past it the function's analysis stops and its loops
stay uncertified, which is sound since the producer is untrusted; on the 29 kernels it loses
no loop (`compare_runs.py`: 257 kernel loops certified before and after, with and without
compiler-rt). An
exception in one program is reported as its error, and `--check` fails on it, instead of
stopping the run.

## Tables in read-only data and tables without a range check (2026-11-24)

**Read-only data.** `m0.load` records `ro_top`, the end of the read-only sections that follow
the code before the first writable one (in file order; the `ld -r` objects are ordered
`.text`, `.rodata`, ...), and `ipet.py` puts the code up to there in the certificate, so a
table in `.rodata` is read by the checker's exact values like a table in the code. The
assumption is the one already made for literal pools: the certificate's code, read-only data
included, is not written during a run. With libgcc this follows the jump tables of `divsf3`
and `divdf3` (`ldr r1, =table; lsls r3, r3, #2; ldr r3, [r1, r3]; mov pc, r3`); the figures
are in the table of the previous section (187 functions and 10 entry functions certified,
against 173 and 8). Kernel loops are unchanged (`compare_runs.py`: 257 before and after,
none lost); loops of the library's routines certified 116 → 125.

**Windows without `CMP`.** When the compiler knows the range of the index it emits no range
check: Clang compiles `switch (x & 7)` with all eight cases into
`movs r2, #7; ands r1, r2; ...; add pc, r1`. The certificate's jump then names the bounding
instruction (`index`); the checker (Lean `jumpRng`, `jumpOkF`) takes its bound from
`rngOps` (`ANDS` by a known operand, `LSRS` by a constant, `UXTB`, `LDRB`; trusted, compared
with `m0.py` by `test_jumptable.py`), requires it below 1,024, evaluates the window from no
known register up to that instruction and then for every value up to the bound, and checks
that nothing enters the window after it but from the instruction before (`interiorR`);
Lean: `jump_good_rng`, `exMask_sound`. `jumptable.find_rng` looks for the bounding
instruction closest to the jump whose targets stay in the function. On a scratch program
with that switch, the certified bound of the function is 20 cycles, the largest of the
emulated calls also 20, and the checker accepts the certificate with the convention
established. On the benchmarks this form adds nothing: `sha`'s first jump is found (8
targets), but its function has a second jump, and `bitcount`'s jump, whose index is bounded
only by its loop or by constants set on several paths (followed since, next section). Tests:
`test_jumptable.py` (the form accepted; a dropped target, a widened mask, the index at the
wrong instruction, a moved start and a missing index rejected).

## Jump indices bounded by the loop analysis (2026-11-24)

The two jumps left refused above have an index that no instruction of the window bounds:
`bitcount_main` jumps on `4 i` (`lsls r0, r6, #2`) where `i` is its loop counter, and
`sha`'s second jump on a value set to constants on several paths. The certificate's jump
then also names a register and a range (`"bound": [d, lo, hi]`, `hi` below 1,024), and the
checker (Lean `jumpInv`) requires that every disjunct of the certified invariant at the
bounding instruction contain `r_d <= u` with `u <= hi` (and `l <= r_d` with `l >= lo` when
`lo > 0`); values of the wrong residue for the certified congruence are skipped, the others
are evaluated through the window as for the masked form. The proof is circular on its face
(the invariant is proved along the graph's edges, the jump's edges are what is being
established) and Lean resolves it by induction along the run: when every earlier step
follows an edge, the invariant holds at the bounding instruction (`inv_prefix`), so the
jump goes to a listed target and that step follows an edge too (`steps_good`,
`jump_good_inv`; example `exPath_sound`, 17 cycles, equal to the emulated run). The
producer goes round the same circle (`wcet.Analysis._resolve_jumps`): graph with the
targets found so far (none at first), zones and congruences at the bounding instruction
(`binloops.inv_jumps`), window evaluated, until the targets stay the same (at most 6
rounds). `bitcount` also needed the congruence of a shift: after `LSLS rd, rm, #k`, `rd` is
a multiple of `2^k` whether the shift overflows or not (`shlCong`, proved), and the zones
now give a shift of a bounded register its interval.

On the 29 kernels (`compare_runs.py`, against the previous runs): no loop lost, no bound
higher, every certificate accepted, no emulated run above a bound. Kernel loops certified
257 → 261 with compiler-rt and libgcc (three in `bitcount_main`, one in `fft_bit_reduct`
by the shift congruence), 257 → 260 without a library (258 → 261 built with
`-fomit-frame-pointer`; with no assumption or `--abi` alone, 143 / 200 and 146 / 204, unchanged:
`bitcount_main`'s loops need `--frame`); stack bounds 239 → 244 (143 → 148
without a library), entry functions with a stack bound 21 → 22 (`bitcount_main`: 104
bytes, equal to the observed value; `sha`: 7 → 10 functions). Certified cycle bounds are
unchanged (121 / 187 / 187): `bitcount_main` calls the recursive `bitcount_ntbl_bitcnt`,
and `sha`'s caller loops over a parameter (`sha_wordcopy`, no constant bound). On scratch
programs compiled by Clang the checker accepts the certificates: `switch (i)` in a loop,
certified 126 cycles, 117 observed; a switch on constants set on several paths, 49 and 45.
Tests: `test_jumptable.py` (both programs accepted; a widened or missing bound, a dropped
target, a path that breaks the invariant, a removed congruence rejected).

## Analysis time, the interpreter in C, QEMU and Clang 23 (2026-11-24)

**Where the time went.** Profiles (cProfile) of `huff_dec`, `pm` and `mpeg2`: the loop
analysis on the machine code (`binloops.py`) and the emulated run (`m0.Machine`, about
0.3 to 0.5 million instructions per second in Python; `mpeg2` runs 294 million cycles, `pm`
296 million: about 660 of `mpeg2`'s 1,557 profiled seconds were the run and its checks).
Changes, none of which changes a certificate:

- `synth_transport` recomputed the transfer of every instruction of the function at each
  of its calls (252 in `huff_dec`, 321 of 926 profiled seconds); it now reuses the
  transfers of `certify_loops` and computes only those of the body and of the edges into
  the header, the only ones it uses; `synth` and `synth_transport` compute once, for the four
  scales `D`, what does not depend on them;
- the closures of zones (`Zones.close`, `add_edge`) and the shortest paths of the Farkas
  proofs (`Prover`) visit only the finite entries of the pivot row (the same updates in the
  same order), `apply_post`, `join` and `leq` with fewer dictionary look-ups;
- scipy validates each HiGHS option at every `linprog` call with a new options manager;
  a successful check is remembered (`ipet.memo_highs_options`, what HiGHS receives is
  unchanged);
- `--func-jobs N`: the loops of the functions of a program are certified by `N` forked
  processes (`ipet.loop_certificates`); each function keeps its own budget, so the
  certificate is that of a serial run (`--jobs` still runs programs in parallel);
- the interpreter in C (`m0core.c`, below).

On the 29 kernels (compiler-rt, `--abi --frame`, `--jobs 8`, on a 40-core machine), the
certificates are byte-identical to those of the code before these changes, which are also
identical to the runs on the author's machine reported above; the wall time of the run goes
from 472 s to 351 s with the analysis changes and to 239 s with the interpreter in C. The
slowest function, `pm_kernel` (244 CPU seconds), now sets the time of the run.

**The interpreter in C.** `m0core.c` executes the instructions as `Machine.execute` does,
from the table that `m0.decode` makes of the code (assuming, as the certificates do for the
literal pool, that the code is not written during a run), and makes the observations of
`run_cycles.py` (`m0.Watch`: the cycles of each call, the stack of each activation, the back
edges of each loop against its bounds). Anything it does not execute exactly as m0.py
(functions without code, accesses outside the memory, instructions that read or write the
PC through `ADD`/`MOV`/`BX`, unknown instructions) is handed back to m0.py for that
instruction. m0.py builds it with the C compiler (`cc`) into `.build/` when needed;
`CROSSCHECK_M0_CORE=python` disables it. Untrusted, like the interpreter: it checks the
bounds against runs; soundness rests on the Lean checker. Checks: `test_m0core.py` (CI)
compares one instruction by `Machine._step`, by `Machine.execute` alone and by the core, on
a sample of encodings from random states (`--all`: every 16-bit encoding, 131,072 cases, the
same), a program with a loop, a call and bounds exceeded on purpose (the same observations
and messages), the cycle limit, and the first 10^6 cycles of the kernels; the kernel run
gives the same JSON with and without the core (times apart). The emulated runs of the 29
kernels take 2 s instead of 215 s; `md5`, 9.3 million instructions, 0.23 s instead of 26 s.

**QEMU.** `run_qemu.py OBJ...` gives the image of m0.py (from address 0x400, after a vector
table and a stub that calls `main` and exits through semihosting) to QEMU 8.2
(`qemu-system-arm -M mps2-an385`, one instruction per translation block, `-d exec,nochain`)
and compares the result and the number of executions of every instruction address with the
interpreter. QEMU's micro:bit board is the only Cortex-M0 one and has 16 KiB of RAM; the
AN385 board has a Cortex-M3, which executes the ARMv6-M instructions of this code with the
same architectural semantics: this checks the instruction semantics and the control flow of
m0.py, not its cycle table. On the 54 objects of the kernels and larger programs linked with
compiler-rt: 50 the same (up to 199.5 million instructions, `mpeg2`), 4 not run (they call
`__aeabi_memcpy4`, `__aeabi_ldivmod` or `fabs`, which have no code in the object).

**Clang 23.** The 29 kernels compiled by Clang 23.1.6 (`--clang`, compiler-rt rebuilt by
it, the source still analysed by the plugin on Clang 18): 187 of 267 functions certified,
`main` in 10 kernels, as with Clang 18; 258 of the 396 loops of the kernels' own code
certified on the machine code (261 of 408 with Clang 18: Clang 23 emits other loops in
`minver`, 23 of 35 → 16 of 28, and `bsort`, 8 of 11 → 11 of 11); every certificate accepted,
no emulated run above a bound; stack bounds equal to the observed stack in 59 of 75 calls
(28 of 74).

## Deterministic limits (2026-11-25)

The producer stopped a linear program after 5 s of wall-clock time and the search of a
function after 600 CPU seconds, so that the certificates depended on the machine and on
its load: on TACLeBench's larger programs, the same code certified 100 loops of
`ammunition` on one machine and 635 on a faster one (all in `ammunition_arithm_test`, which
reached the budget; the cycle certificate, which does not contain that function, was the
same), and `epic_internal_filter` was cut at different points. The limits now count work:

- each function's search has a budget of `FUNC_WORK` = 600 million units
  (`CROSSCHECK_LOOP_WORK`, 0 = none), `binloops._work`: 715 per visit of a worklist, 655 per
  Farkas prover, 20,124 per linear program and one per 361 iterations × size of the linear
  programs (rows + columns + nonzeros); the weights are a least-squares fit of the CPU
  seconds of the 1,651 functions of the kernels and the larger programs (one unit is about a
  microsecond on the machine of the fit; median error 19% on the functions above 20 s);
- a linear program stops after `min(60,000, 3·10^9 / size)` iterations (`lp_maxiter`): the
  largest successful solves of these runs needed 53,912 iterations and 2.5·10^9 iterations
  × size;
- a limit in time remains, since the time of an iteration varies a thousandfold, but in CPU
  seconds, not wall-clock seconds: 60 CPU seconds per linear program (`LP_SAFETY_CPU`,
  since 2026-11-25; see below).

The work of every function is recorded in the results (`loops_detail`: `meter`, `seconds`).
Checks: the 29 kernels (compiler-rt, `--abi --frame`) give byte-identical certificates on a
40-core machine idle and overloaded (load average 41, `--jobs 29`), and the six slowest
(`pm`, `quicksort`, `ludcmp`, `binarysearch`, `fft`, `bitcount`) the same certificates on an
Intel Core i5-3360M laptop and on an Intel Xeon Silver 4410T; `compare_runs.py --check`
against the run with time limits: 261 kernel loops certified before and after, no bound
higher or lower.

### The time limit of a linear program, in CPU seconds (2026-11-25)

The 60 s limit of HiGHS (`time_limit`) counted wall-clock time, so whether a solve reached
it depended on the load (in the kernels, it was reached only under load). The 547 linear programs of a run of the larger programs that took
more than 2 s were saved (`CROSSCHECK_LP_DUMP=DIR`) and solved again alone, with the same
iteration limits and a limit of 300 s:

- the iteration limit does not bound the time: the same method ran at 30,000 iterations
  per second on some and 40 on others, and HiGHS failed on some with an error after 66 to
  485 s (given 600 s) without counting iterations (scipy's `linprog` then reports none), on programs of
  2,000 to 20,000 rows with constants near 2^32; `linprog` also gives the interior point
  the simplex's iteration limit, thousands of iterations where it needs fewer than 100;
- none of the solves that took more than 60 s succeeds within 300 s (nor 10 of them,
  the slowest, within 600 s): all end at an iteration limit, in a numerical failure, or in
  time; of the 20,029 solves of that run,
  the 585 that succeed take at most 20 s, and 97% of the time spent on linear programs
  went to solves that fail.

`binloops.highs_lp` now calls HiGHS itself (scipy's copy, `scipy.optimize._highspy`): the
same model and options as `linprog`, hence the same answers (`test_binloops.py
LinearPrograms`: statuses, iteration counts and solutions bit for bit on 240 programs), and
HiGHS's simplex and interior-point callbacks stop a solve after `LP_SAFETY_CPU` = 60 CPU
seconds of the process. A stopped solve is charged its full iteration limit in the work
meter, as if HiGHS had reached it, so that the budget of the function does not depend on
where it stopped. HiGHS's own wall-clock limit stays as a backstop at 600 s for phases
without callbacks (`lp_wall`, with a warning; never reached). The results give, per
function, the solves stopped (`lp_safety`) and the CPU seconds of the slowest successful
solve (`lp_ok_max_cpu`): a machine `LP_SAFETY_CPU / lp_ok_max_cpu` times slower would stop it.

With the CPU limit, the 8 configurations of the figures (the 7 kernel runs and the larger
programs) give byte-identical certificates to those of the wall-clock limit: 254 of 254.
The CPU limit stops 0 to 3 solves per kernel configuration (in `ludcmp_test`, `minver_mmul`,
`fft_bit_reduct`, `fft_float2fract`, now on an idle machine too) and 29 in the larger
programs; the backstop is never reached; the slowest successful solve takes 5.7 CPU
seconds in the kernels (`ludcmp_test`) and 19.7 in the larger programs
(`h264_dec_decode_one_macroblock`), a margin of 10 and 3 for a slower machine. CPU time
still depends somewhat on the load (two hardware threads share a core), much less than
wall-clock time. `ludcmp` gives the same certificate, with its stopped solve, on the
laptop and on the 40-core machine.

### Creeping widening: only the growing variables are forgotten (2026-11-25)

When the closure keeps tightening a widened zone again, the analysis of a loop head creeps
up and is stopped after `HARD_VISITS` = 200 widenings by `forget_growing`. It dropped the
whole row and column of every growing entry; when a pointer grows, its entry on the row of
the zero node grows too, so the upper bound of every variable was dropped, including that
of a counter whose range was stable. In `powerwindow_main`, 13 byte-copy loops
(`ldr r2, =977; ...; subs r2, #1; bne`) follow one another: the first was certified, the
seven whose heads the analysis visited more than 200 times while the copy pointers crept
up were not (`r2` in `[0, 2^32 - 1]` at their heads instead of `[1, 977]`). Now the
variables that cover the growing entries are chosen one at a time, the one in the most
growing entries first (never the zero node), and all their constraints are dropped; the
others keep theirs. The result is still closed, and each call that changes anything drops
a finite entry of the previous zone, so the iteration still stops (`test_binloops.py
ForgetGrowing`).

Run on the 8 configurations of the figures, `compare_runs.py --check` against the
committed runs: the 7 kernel configurations unchanged (143, 200, 260, 261, 146, 204, 261
loops); the larger programs 1,227 → 1,247 loops, no loop lost, one bound lower (a loop of
`h264_dec_decode_one_macroblock`, 2^32 − 1 → 1): `powerwindow` 7, `cjpeg_transupp` 6,
`ammunition` 3, `h264_dec` 2, `huff_enc` 1, `mpeg2` 1. The certified functions (344) and
entry functions (2) are the same.

### What keeps `main` uncertified (2026-11-25)

`run_cycles.py` records, for each program whose `main` has no certified cycle bound, the
functions reachable from it by calls that have no certificate for a reason of their own
(not only because a callee has none), with that reason (`main_blockers` in the JSON,
printed as `main blocked by ...`; a call of a routine without code, or of an address that
starts no function, under its name or address). For the 23 larger programs without a
certified `main` (run above): in 22, some function has a loop bounded neither by the
source analysis nor on the code (one such function in 9 programs, up to 11 in `ammunition`
and 10 in `susan`; the first such loop of each function is reported); besides, routines without code (`__aeabi_ldivmod` and `__aeabi_uldivmod`
in `ammunition`, `__aeabi_memcpy4` in `cjpeg_wrbmp` and `ndes`, `fabs` in `susan`),
irreducible control flow (`mpeg2_field_ME`, `susan_get_image`), a jump out of the function
(`mpeg2_frame_ME`), a linear program that HiGHS reports unbounded (`mpeg2_dist1`), and in
`petrinet_main`, its only obstacle, a `bl` to an address inside the function itself. LLVM uses `bl` as a long
branch in Thumb-1 functions beyond the reach of `b` (2 KB): the 25 programs have 15 such
branches (`petrinet_main` 6, `mpeg2_field_ME` 7, `rijndael_dec_decrypt` and
`rijndael_enc_encrypt` 1 each). The checker's `decode` treats every `bl` as a call that
returns to the next instruction, so these functions are refused.

The `__aeabi_memcpy4` calls of `ndes` copy local arrays from constant tables, 65 to 2,304
bytes: the length is a constant at every call, but the loop of a `memcpy` is bounded by
its argument, which needs bounds that depend on the call. Of the 7 programs blocked by one
function, the loops left (read on the code, or as grouped by `classify_loops.py`):
`powerwindow_main`, its outer loop `while (powerwindow_main_inputcyclecounter <
powerwindow_input_length)` on a global counter that `powerwindow_init` sets to 0 before
the call (the source analysis gives calling contexts for arguments only); `adpcm_dec`'s
`main` and `adpcm_enc_init`, series that end when an integer division returns 0;
`dijkstra_find`, two loops over data in memory and a counter whose initial value is loaded
from the literal pool; `h264_dec_decode_one_macroblock`, a counter
stepped by 7 up to 28 with an exit on equality (a congruence modulo 7; the checker's are
modulo powers of two) and a shifted counter; `gsm_dec_RPE_Decoding`, counters through
`SXTH`; `g723_enc_main`, a counter whose initial value is loaded from the literal pool.

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

The stack pointer may also be set from a register: `add sp, r` with `r` a constant of the
literal pool (`ldr r, =-size; add sp, r`, for frames larger than `sub sp, #imm` can
reserve) and, since 2026-11-24, `mov sp, r` with `r` the stack pointer at entry minus a
constant, as when Clang restores it from the frame pointer (`add r7, sp, #12` after the
`push`, then `subs r6, r7, #7; subs r6, #5; mov sp, r6` before the `pop`). Every
instruction gets, with its depth, the registers whose value is known on every path to it
(`ldr r, =c`; `add r, sp, #i`, `mov r, sp`, then `adds`/`subs` by constants and `mov`
between registers); where paths meet, a register stays known only if its value is the same
on all of them. A call keeps a register known only if the callee preserves it on its own
code (`StackAnalysis.preserved`): its entry `push` saves the register and every return is a
`pop` of it, or neither it nor its callees write it; like the calling convention, this
assumes that the saved words are not overwritten during the call. `test_stack.py` (CI):
the frame pointer followed and the bound compared with a run on `m0.py`; a callee that
writes `r7` without saving it, `r7` changed or overwritten before the call, and two values
of `r7` meeting at a join get no bound.

| | |
|---|---:|
| functions with a stack bound | **151 of 267** |
| entry functions (`main`) with a stack bound | 12 of 29 |
| calls compared with the run | 29, **no violation** |
| of which the bound equals the observed stack | 24 |

| Kernel | Stack bound of `main` (bytes) | Observed |
|---|---:|---:|
| binarysearch | 56 | 56 |
| bitcount | 104 | 104 |
| bsort | 28 | 28 |
| countnegative | 64 | 64 |
| fac | 24 | 24 |
| insertsort | 32 | 32 |
| isqrt | 52 | 52 |
| jfdctint | 104 | 104 |
| matrix1 | 36 | 36 |
| md5 | 584 | 552 |
| prime | 56 | 56 |
| sha | 8,648 | 8,648 |

(`fac` is recursive in the source; at `-O1` the compiler turns its recursion into a loop.)

No bound, by cause (116 functions): a call to a software floating-point helper, which the
interpreter provides in Python, without code (86); a call to such a function or to a
recursive one (26); recursion in the binary (4: `bitonic`, `quicksort`, `recursion`). The
stack pointer written from a register no longer stops any function (five did before it
was restored from the frame pointer, three of them in `sha`).
With compiler-rt the frame pointer adds the entry functions of `filterbank`, `ludcmp`,
`minver` and `sha` (stack bounds 244 → 256, all four within 4 bytes of the observed stack);
with libgcc `sha` (244 → 247). A recursive function could be bounded
from a recursion depth (`Stack.highWater_le_depth`); this is not implemented.

What the bound covers: the stack of the program's own code. Not counted: exception frames
(8 words per interrupt taken on this processor), and anything a real run-time library
would add. The decoder and the control-flow graph are those of the cycle analysis, and
the check is against the same interpreter: it tests the path analysis, not the decoder.

## History

The changes that moved the figures above, newest first (each run: no loop lost, no
certified bound higher, every certificate accepted, no emulated run above a bound, unless
said otherwise).

- **2026-11-25, creeping widening.** `forget_growing` drops the constraints of the growing
  variables only ("Creeping widening"): larger programs 1,227 → 1,247 certified loops; kernel
  figures unchanged.
- **2026-11-25, time limit in CPU seconds.** HiGHS called directly (`highs_lp`), stopped
  after 60 CPU seconds by its callbacks instead of 60 s of wall-clock time; a stopped solve
  is charged its iteration limit ("The time limit of a linear program, in CPU seconds");
  all 254 certificates of the figures byte-identical.
- **2026-11-25, deterministic limits.** Work units instead of seconds for the search of a
  function and for each linear program ("Deterministic limits"); kernel figures unchanged.
- **2026-11-24, analysis time.** Exact speed-ups of the loop analysis, `--func-jobs`, the
  interpreter in C, the QEMU comparison ("Analysis time, the interpreter in C, QEMU and
  Clang 23"); kernel certificates byte-identical.
- **2026-11-24, stack pointer restored from the frame pointer.** `stack.py` follows
  registers known on every path (`mov sp, r` from the frame pointer). Stack bounds 148 /
  244 / 244 → 151 / 256 / 247, entry functions 11 / 22 / 22 → 12 / 26 / 23; no violation.
- **2026-11-24, indices bounded by the loop analysis.** Jumps whose index only the certified
  invariant bounds are followed (`bitcount`, `sha`); shift congruences. Kernel loops 257 →
  260 / 261 / 261, stack bounds 143 / 239 / 239 → 148 / 244 / 244; certified functions
  unchanged. GCC binaries: kernel loops 40 / 65 / 74 → 40 / 66 / 75 (no earlier run kept to compare
  loop by loop), certified functions unchanged.
- **2026-11-24, read-only data and masked indices.** The certificate's code includes the
  read-only data after it, and jumps whose index is bounded by `ANDS`, `LSRS`, `UXTB` or
  `LDRB` are followed. Kernels without a library or with compiler-rt unchanged (121 / 187
  certified); with libgcc 173 → 187, entry functions 8 → 10.
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

