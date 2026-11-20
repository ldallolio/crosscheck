# Cycle bounds on a Cortex-M0

`run_cycles.py` turns CrossCheck's source loop bounds into **cycle bounds of compiled
code** for a processor whose instruction timings do not depend on the execution history:
the Arm Cortex-M0 (in order, no cache, no branch prediction), with zero-wait-state
memory. It is step S5 of `docs/proposals.md`.

```bash
python3 benchmarks/cycles/run_cycles.py --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13 \
    [--only bsort] [--json out.json] [--check] [--mul-cycles 32] \
    [--certify DIR --checker formalization/.lake/build/bin/crosscheck-check]
```

For each TACLeBench kernel (the single-file unit of `benchmarks/tacle/run_tacle.py`):

1. **Source loop bounds**: CrossCheck analyses the kernel (no annotation) and gives each
   loop a bound in the calling contexts of `main` (else for every call).
2. **Compilation**: Clang 18, `--target=thumbv6m-none-eabi -mcpu=cortex-m0 -O1 -g
   -fno-unroll-loops -ffreestanding -fno-builtin`, one object file.
3. **Static bound** (`wcet.py`): for each function, the control-flow graph of the code
   reachable from its entry (`m0.decode`, ARMv6-M Thumb); it must be reducible, without
   indirect jumps. Each natural loop is matched with the source loops through the debug
   line table (the source loop whose line occurs among the loop's own instructions; the
   largest bound if several do; no bound if none does), and its back edges are bounded by
   that source bound. The bound is the timing schema on the binary: a loop costs
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

## Results (2026-11-16)

29 kernels compiled; 28 return 0 when run (`fft` returns 1: it converts negative floats to
`unsigned long`, undefined behaviour in C, which Arm's conversion saturates and x86's wraps;
it is listed in `EXPECTED_FAILURE`). 156 s in total.

- **107 of the 267 kernel functions** receive a cycle bound (`runtime.c` not counted).
- **6 entry functions** (`main`) are bounded:

| Kernel | Bound (cycles) | Observed | Bound / observed |
|---|---:|---:|---:|
| binarysearch | 32,686 | 24,241 | 1.35 |
| bsort | 369,779 | 148,668 | 2.49 |
| countnegative | 449,615 | 327,923 | 1.37 |
| isqrt | 1,005,075 | 689,071 | 1.46 |
| jfdctint | 75,652 | 60,911 | 1.24 |
| matrix1 | 63,722 | 48,548 | 1.31 |

- **Checks**: 11 calls of bounded functions (the others are inlined at `-O1`) and 45 binary
  loops were compared with the run: **no violation**; over 10 of the calls, bound/observed is
  between 1.02 and 2.49. The eleventh, a function of `fft` bounded since logarithmic potentials
  (2026-11-15), has a bound 970 times its observed cycles: its three nested loops are
  bounded by the product of their bounds, while at each outer iteration the count of one
  inner loop doubles and that of the other halves. `bsort`'s factor comes from its triangular nested loops, bounded
  as a rectangle (no amortisation).
- **Not bounded**, by cause: software floating point (`__aeabi_f*`, `__aeabi_d*`: most of the
  numeric kernels), source loops without a bound (data-dependent: `insertsort`,
  `binarysearch`, `quicksort`), and their callers.

Matching rule: the first version, which took the largest bound among all lines of a
loop's instructions, gave `matrix1_main` 100 iterations instead of 10 (an instruction of
the loop's preheader inherits the line of another loop) and a bound 105 times the observed
cycles; trying the lines of the back-edge branches first gives 1.31.

## Certified cycle bounds (2026-11-17)

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
| bsort | 369,779 | 288,179 | 148,668 | 1.94 |
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

## Loop bounds certified on the machine code (2026-11-18)

`run_cycles.py --certify DIR --checker ... --certify-loops [--abi]`: the loop bounds are
also certified on the machine code where `binloops.py` finds a certificate (format
version 2, `docs/certificate-format.md`; Lean `ThumbData.data_sound`, Paper III
`thm:machine-loops`). Per instruction, the kind of operation that set the flags and an
invariant on `r0`-`r7` and the two operands of that operation (a zone analysis of
differences of registers, widening at loop headers, descending iterations) and congruences
modulo powers of two (Granger), with which the facts of a branch are rounded (a counter
stepped by 4 that leaves its loop at 80 gets `≤ 76`; checked by `congOk`, Lean
`congPE_sound`, `condFactsM_sound`); per loop, a
potential `±r_i` or `±(r_i − r_j)` plus per-instruction constants, scale 1, 2, 4 or 8, or,
when none is found, a potential with its own linear part at each instruction from one
linear program over the checker's obligations (`synth_lp`: Colón–Sipma, Alias et al.;
HiGHS, at most 5 s per program, rounded and proved again exactly); Farkas multipliers from
shortest paths, negative cycles or a linear program. What cannot be
proved is dropped; a dropped loop keeps its source row, trusted.

| run | loops certified (kernels' own code) | not certified | accepted | functions with a certified cycle bound |
|---|---|---|---|---|
| no assumption on callees | 142 of 403, and the 116 of the division routines | 261 + 0 (division routines) | all | 116 (107 before) |
| `--abi` (callees preserve r4-r7 and SP) | 199 of 403, and the 116 | 204 + 0 | all | 116 |
| `--abi --frame` (frames written only through SP, or through the frame pointer by loads only) | 256 of 403, and the 116 | 147 + 0 | all | 121 |

Wrap to zero (2026-11-20). Clang compiles some loops over arrays with a byte offset counted
from 2^32 − 16 up by 4 to zero (`adds r3, #4; bne`). In the case of the wrap-around the
loop continues only if `g1 + 4 ≥ 2^32 + 1`; the checker now rounds facts on sums with the
congruences too (`gExpS`, `tightenS`: when `g1 + g2 ≡ 0 mod 2^e`; Lean `tightenS_holds`,
`condFactsM_sound`; example `exZero_sound`, 3 iterations, and `exZero_needs_cong`), which
gives `g1 + 4 ≥ 2^32 + 4`, contradicted by `g1 ≤ 2^32 − 4`. The producer adds the
wrap-around values 2^32 − k − 1, 2^32 − k, 2^32 − k + 1 of each addition of k > 0 to its
widening thresholds, ignores `adds #0` (a move) as a wrap point, derives one-variable bounds
from premises on sums in its Farkas proofs (virtual premises mapped back to the real
multipliers), computes the constants of transported potentials by longest paths before the
linear program (`synth_transport`; HiGHS fails on these constants), and keeps searching
when a candidate is above the source bound, trying the tightest first. Counts 136 / 193 /
250 → 142 / 199 / 256 (+6 in every run: `bsort_init` and `main` of `bsort`, bound 99;
`fft_init` and `main` of `fft`; `fir2dim_pin_down` and `fir2dim_main`, bound 3, no source
bound); without frame pointers 140 / 198 / 252 → 146 / 204 / 258. 372 of the 519 loops
with both assumptions (374 without frame pointers); functions with a certified cycle bound
115 / 115 / 120 → 116 / 116 / 121 (`fir2dim_pin_down`); trusted loop rows 43 / 37 / 19 → 41
/ 35 / 17 (41 / 36 / 18 → 39 / 34 / 16 without frame pointers); with both assumptions 160 of
the 174 functions with loops have none. No loop lost, no bound higher, every certificate
accepted, no emulated run above a bound. One loop of the same form is left (`fir2dim`
0x242): its start comes from a frame word loaded outside the loop, which is not tracked.
Must-reject tests (`test_binloops.py`, class `WrapToZero`): a start of 14 instead of 15,
a step of 3, the congruences removed. The six runs took 7 to 19 minutes each with
`--jobs 4`, one at a time; the tests now take 29 s (the new test runs the producer).

Disjunctive invariants (2026-11-20). The run-time division routines (`runtime.c`, the
same four in every kernel) count `for (i = 31; i >= 0; i--)`, compiled as `subs r3, r3, #1;
adds r4, r3, #1; bhs exit`: the exit is taken once `r3` has wrapped around to 2^32 − 1, and
between the subtraction and the branch `r3 ≤ 30 ∨ r3 = 2^32 − 1`, which no conjunction of
linear constraints expresses. The checker (`ThumbDataCore`, proof in `ThumbData`, no new
assumption, no axiom beyond Lean's three) now accepts invariants that are disjunctions:
per instruction further disjuncts (`alt`) and, for each case of a transition (transition,
wrap case, fact of the branch, source disjunct), the disjunct of the successor it lands in
(`pick`; default the first). The producer splits the zone at an addition or subtraction
of a constant that may wrap around and carries the two cases along the straight line up
to the next conditional branch (trace partitioning, Mauborgne & Rival, ESOP 2005, merged
after the branch); the potential then follows the counter through its copies (`r3 + 1`,
the operand of the flags after the subtraction, `r4 + 1` at the branch). HiGHS failed on
these linear programs (constants from 1 to 2^32 in one row; it declared feasible programs
infeasible): the producer now detects contradictions of the one-variable bounds exactly,
leaves such cases out of the linear program, retries without presolve, then with each
constant split as `q·2^31 + r` and the two parts required separately, then with linear
parts fixed to a variable that follows a bounded header variable (`transport`), only the
constants unknown. Results: the 116 loops of the division routines are certified in all
six runs (none before; bound 31 back edges, source bound 32), the kernels' counts become
136 / 193 / 250 (+4 with both assumptions: `fft`, `matrix1`, two loops of `pm_kernel`
bounded by 2^31 − 2), without frame pointers 140 / 198 / 252; 366 of the 519 loops of the
binaries with both assumptions. Trusted loop rows in the certified cycle bounds: 159 / 153 /
137 → 43 / 37 / 19 (134 → 18 without frame pointers); with both assumptions 158 of the 173
functions with loops have none. No loop lost, no bound higher, every certificate accepted, no
emulated run above a bound. Must-reject tests (`test_binloops.py`, class `Disjunctions`):
one more iteration, a step of 2, the opposite exit, `alt` or `pick` removed, a disjunct
or a target changed. The six runs took 6 to 16 minutes each with `--jobs 4`.

Run time and development cycle (2026-11-20). Profile of a run with both assumptions (103
minutes before): `pm` alone took 77 minutes (`pm_kernel`: 902 instructions, 31 loops, zones
of 44 variables); in the slow functions the closure of zones (Floyd-Warshall, pure Python)
took 46-57 % of the time, HiGHS 20-54 % (badly scaled programs: the dual simplex often
reports a numerical failure or reaches `LP_SECONDS`), the rest the transfer functions and
joins. Changes that leave every certificate identical (the producer is untrusted; checked
with `BINLOOPS_CHECK_CLOSE=1`, which compares each shortcut with the full closure, and by
comparing the certificate files of whole runs): a join of closed zones is not closed again
(the pointwise maximum of closed difference-bound matrices is closed: Miné, PADO 2001), a constraint added to a closed zone is closed incrementally in O(n^2), the
image of a closed zone by the post-expressions is completed only on the variables with any
value, the analysis before the congruences (whose result was discarded) is gone, and the
empty results of the run-time division routines (the same code in every kernel) are
reused. With `--jobs` (kernels in parallel) the run with both assumptions takes 18 minutes
with 3 processes (103 before), its 29 certificate files identical to those of the previous
run. Elsewhere: the Lean checker takes 1.1 s at most per certificate (6 s for all), the
Clang analyser 100 s for the 29 kernels (92 % of it in Z3 implication checks, much of
that in the construction of a solver per query). Cycle:

1. `python3 -m pytest -q test_binloops.py test_ipet.py test_effect.py` (under a minute);
2. a subset: `run_cycles.py --certify-loops --abi --frame --jobs 4 --only bitcount --only
   bitonic --only countnegative --only fft --only st --only isqrt --only matrix1 --only
   insertsort --only filterbank --only iir --only md5 --only sha ...` (a few minutes), then
   `compare_runs.py OLD.json NEW.json --check` (fails on a loop lost or a bound higher);
3. the full run with both assumptions (`--jobs 4`), then `compare_runs.py --check`;
4. the six runs (default and `.nofp` builds; no assumption, `--abi`, both) only before the
   figures of the paper and of this file are updated.

Exact shift (2026-11-20): `LSLS rd, rm, #s` is exact in the checker's specification
(`Val.shl`: `rm·2^s` when it does not overflow, any value when it does, a case split like
the wrap-around of sums; `s = 0` is `MOVS rd, rm`; flags any) and in the producer's mirror;
the proof of `ThumbData.data_sound` was extended to the new value kind (no new assumption, no axiom
beyond Lean's three). The producer also solves Farkas multipliers exactly (Gaussian
elimination over the rationals on the premises the LP used) when the LP's multipliers are
too small to round, and adds the ranges of the goal's variables to that LP. Counts 131 /
183 / 229 → 136 / 193 / 246 (+5 / +10 / +17 in `fft`, `filterbank`, `st`, and `bitcount`
with both assumptions; 3 of the 17 without a source bound); without frame pointers 135 /
188 / 233 → 140 / 198 / 251. No loop lost, no certified bound higher (four of `bitcount`
lower, 2^31 − 2 → 255), every certificate accepted, no emulated run above a bound;
functions with a certified cycle bound with both assumptions 117 → 120 (`bitcount_init`,
`bitcount_init3`, `bitcount_init4`; 118 → 120 without frame pointers). A first run lost
`jfdctint` 0x172 (HiGHS again, a frame word holding `1 << 14`): the second analysis
(`lit_any`) now also gives shifts any value in the producer's own analysis. Must-reject
tests (`test_binloops.py`, `EXACT["shl"]`): the shift amount changed, the operand changed,
an overflowing shift, `LSRS` instead of `LSLS`, and `LSLS #0` (a move) that breaks the
congruence the certificate uses. The six runs took 17 to 103 minutes each, three at a time.

Exact effects (2026-11-19): `NEGS` (0 − x, flags of that subtraction), `MVNS`
(2^32 − 1 − x, flags any), the write-back of `STM`/`LDM` (base + 4 per register; `STM`
writes no register of its list; `LDM` gives any value to its list, base included if listed)
and the literal load `LDR rt, [pc, #i]` (the word of the certificate's code at that address;
assumes the code is not written during a run) are now exact in the checker's specification
(`ThumbDataCore.effect`; `data_sound` unchanged) and in the producer's mirror. Counts 121 /
173 / 215 → 131 / 183 / 229 (+10 / +10 / +14 in `bitonic`, `fft`, `fir2dim`, `quicksort`,
and `matrix1` with both assumptions; 6 of the 14 without a source bound); without frame
pointers 123 / 176 / 216 → 135 / 188 / 233 (also `isqrt`, `ludcmp`, `minver`). No loop
lost, no certified bound changed, every certificate accepted, no emulated run above a bound.
The literal constants (addresses near 2^32) made HiGHS fail numerically (status 4) on three
loops certified before (`fir2dim` 0x188, `jfdctint` 0x172, `lms_init` 0x9e, the losses of
the earlier experiment): the producer's own analysis now ignores constants above `BIG` =
2^20 in its zones, tries coarse linear programs (large constants as variables) after the
exact ones, and, when a loop of a function stays without a potential, analyses the function
again with literal loads as any value (`lit_any`), keeping the result with more loops.
Must-reject tests `ExactEffects` (`test_binloops.py`): a literal word changed (two ways), a
literal outside the code, an `STM` replaced by an `LDM` that loads the counter or the base,
an operand of `NEGS` or `MVNS` changed (and an `LDM` that does not load the base, accepted). The four runs took 32 to 156 minutes each, two at a time.

Frame pointer (2026-11-19): `--frame` is no longer refused because of the prologue
`add r7, sp, #i` alone; the checker (`frameUseOk`) then requires that no instruction may
read r7 except as the base address of a load or a `PUSH` at the entry (`regsRead`,
over-approximated by encoding). The assumption itself (`StackOk`) and the proof are
unchanged: the check only restricts where it may be stated. With both assumptions, 175 → 215 (before the exact effects)
loops (12 kernels: `minver` 10 → 22, `countnegative` 6 → 12, `pm` 29 → 34, ...), none lost,
no bound higher; `--frame` is refused in 26 of the 265 functions the producer analyses
(190 before), those that put another address of their frame in a register. The build
without frame pointers is unchanged (216). The run with both assumptions takes 58 minutes
(32 before; `pm` 48).

Potentials per instruction by linear programming (2026-11-18) raised these counts from 116,
167 and 169 (loops of `countnegative` and `isqrt`); no loop lost, no bound higher. A first
run without a time limit on HiGHS hung on a linear program of `jfdctint` (constants up to
2^32): hence `LP_SECONDS`.

Congruences (2026-11-18) raised these counts from 73, 105 and 107: most loops left
uncertified exited on equality (`bne`), which zones alone cannot bound when the counter
steps by more than 1. The same day, `ipet.py` stopped rounding the LP's multipliers up
when exact fractions give a smaller bound (rows of scale above 1): 10 certified cycle
bounds became lower (up to 8 %), none higher.

Stack slots (2026-11-18): the words of the frame accessed through SP are tracked (SP
offsets per instruction, `slots`); without them the counts were 72 and 94. Remaining failures with `--abi --frame` (kernels' own loops, with
congruences, potentials per instruction, the frame pointer, exact effects, the exact shift, disjunctive invariants and the rounding of sums): 86 counter tracked but no
potential (62 of them exit on equality), 21 compared value not tracked, 21 SP offset unknown, 12 flags from an
unmodelled instruction, 7 mixed (before the rounding of sums: 88, 25, 21, 12, 7; before the disjunctive invariants: 92, 25, 21, 12, 7; before the exact shift: 98, 36, 21, 12, 7; before exact effects: 106, 42, 21, 12, 7; before congruences: 210, 42, 24, 12, 8; before the linear
programs: 151, 42, 21, 12, 8; before the frame pointer: 145, 42, 21, 12, 8).

Classification of the 147 kernel loops not certified with `--abi --frame` (2026-11-20, after the rounding of sums; 153 after the disjunctive invariants, 157 after the exact shift, 174 after the exact effects, 188 before,
`classify_loops.py RUN.json`: for each exit, the instruction that set its flags and the
definitions reaching its operands inside the loop; heuristic, for diagnosis only):

| group | loops | what would be needed |
|---|---|---|
| A counter against a constant or a bounded limit | 43 (49 before the rounding of sums, 51 before the disjunctive invariants, 62 before the exact shift, 69 before the exact effects) | the counter's initial value: from a word of the frame, a constant (the loops that count from `mvns r1,#7` up by 4 to zero, 7 in `fft`, `fir2dim` and `bsort`, are certified since the rounding of sums except `fir2dim` 0x242, whose start is a frame word loaded outside the loop), by `LSR` of an argument (9), from an argument (8), by `AND` (3), ... |
| B counter against a limit without a bound (a parameter) | 19 (20, 26, 27) | bounds in the parameters, or calling contexts, on the binary |
| D exit on a value returned by a call | 22 | mostly soft-float comparisons (`for (i = 0.0f; i < 10; i += 0.1f)` in `cosf`) |
| F exit on data loaded from memory | 16 (17) | invariants on memory (string and search loops) |
| C exit on the flags of a shift | 12 | `x >>= 8` until zero (`bitcount`, `sqrtf`): logarithmic potentials on the code |
| E counter shifted | 11 | logarithmic potentials (binary search, bit reversal) |
| I other (two counters, sums of registers) | 10 (11) | |
| G word of the frame not tracked | 10 | SP offsets where they are unknown |
| H value through an approximated instruction | 4 (9) | not exact effects: the `ADCS` loops (3, `bsort`) test Clang's `rsbs; adcs` form of `x == 0`, bubble sort's "swapped" flag (termination depends on the data); the uncertified loops with `ANDS` include `x &= x - 1` (`bitcount`: as many iterations as set bits, no linear potential) |

The producer's own reasons: no potential found for 139 (145 before the rounding of sums, 149 before the disjunctive invariants, 166 before the exact shift, 181 before the exact effects), a potential whose bound (2^31 or
2^32) exceeds the source bound for 8 (8, 7). An experiment with exact effects, in the producer only
(not in the checker; since made exact in both, see "Exact effects" above), for `STM`/`LDM` (base advanced by 4 per register; STM does not
write its list), `MVN` (2^32 − 1 − x), `NEGS` (0 − x, flags of the subtraction) and `LDR`
from the literal pool (the word of the code), found potentials for 15 more loops (`bitonic`,
`fft`, `fir2dim`, `matrix1`, `quicksort`, `minver`; whether each is below its source bound was
not checked) and lost 3 (`fir2dim` 0x188, `jfdctint` 0x172, `lms_init` 0x9e; analysed since: HiGHS).
Before the exact effects, runs took 11 to 70 minutes (5 to 32 before the linear programs; `pm` alone up to 55).

Without frame pointers (`run_cycles.py --cflag=-fomit-frame-pointer --tag=.nofp`, a
separate build of the same kernels): `--frame` refused in 25 of the 265 functions the
producer analyses (190 in the default build); kernel loops certified 140 / 198 / 251
(no assumption / `--abi` / `--abi --frame`; 135 / 188 / 233 before the exact shift, 123 / 176 / 216 before the exact effects; default build: 136 / 193 / 246, 175 before the frame pointer; without the
linear programs 120 / 173 / 202, which add 14 loops in nine kernels), 120 functions with a certified cycle
bound; all certificates accepted, no emulated run above a bound. Before congruences that
build gave 77 / 109 / 129.

No back-edge count of the emulated runs exceeds a certified bound. 82 (114 with `--abi`, 151 with both) of
the certified bounds are below the source bound (typically by one: the binary counts back
edges), none above (the producer keeps the source row then), and 60 (85 with `--abi`, 105 with both)
certified loops have no source bound at all. The functions newly certified include `fac_fac`, `fir2dim_pin_down`, `md5_R_RandomInit`,
`md5_R_memset`, `md5_memcpy`, `md5_memset_x`, `pm_memcpy`, `pm_memset`, `sha_fread`, and
(with both assumptions) `bitcount_init`, `bitcount_init3`, `bitcount_init4`.

Trusted, in addition to the decoder and timing table: the effects of the instructions on
`r0`-`r7` and the flags, the flags of additions and subtractions and the conditions
(`Thumb.effect`, `flagsAdd`, `flagsSub`, `condHolds`), compared by `test_effect.py` (CI)
with `m0.py` on every 16-bit encoding in three random states, with and without the
assumption on callees: 297,244 executions, no difference. `test_binloops.py` (CI):
certificates altered in their bounds, scales, potentials, invariants, kinds, multipliers,
assumption on callees, or code must be rejected.

## OTAWA on the same binaries (2026-11-16)

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
| bound / executed, geometric mean (largest) | 2.36 (756: `fft_bit_reduct`, product of nested bounds) |
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
| bound / executed, geometric mean (largest) | 2.74 (1,054: `fft_bit_reduct`) |
| OTAWA's bound / timing schema's | never below; equal for 52, larger for 55 (median 1.005, largest 1.29: `matrix1` `main`) |

OTAWA's bound is above the schema's where a loop header gets one more execution than the
body and the schema counts only the exit path for it. **Why label and offset**: the FFX
that the plugin exports designates a loop by source file and line; on these `-O1`
binaries OTAWA could not place such facts (inlined callees, rotated loops: "no limit for
the loop at ..."), so the matching of binary loops to source loops is done by `wcet.py`,
as for the cycle bounds. That matching is checked on runs, not proved.

**The loops of OTAWA's graphs** (`--matching otawa`, 2026-11-17): the same run with the
binary loops taken from OTAWA's own control-flow graphs and matched by `otawa_flow.py` (the
matching used for the processors modelled by OTAWA, below), instead of `wcet.py`'s:
107 of 107 functions bounded, none refused by the matching, 11 calls compared with **no
bound below the executed instructions**, the same bounds per function as with `wcet.py`'s
matching for all 107 (99 flow facts, written for the functions reachable from those given to OTAWA; 199 with `wcet.py`'s matching, 108 of them for the loops of the run-time division functions, written for every kernel).

## Other processors: OTAWA's STM32 models (2026-11-17)

`otawa_flow.py` gives CrossCheck's source loop bounds to OTAWA on any binary it decodes:
in a container without network, `mkff` lists the loop headers of the code reachable from
a function and `dumpcfg --cfg-raw -S` its basic blocks; each natural loop is matched with
the source loops through the debug lines (back-edge branches first, then the header, then
the loop's own instructions; the largest bound if several match) and written as a flow
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
| with a WCET from OTAWA | **168** | **162** |
| ... entry functions `main` | 8 | 7 |
| of the 107 bounded on the Cortex-M0 (above) | 106 | 103 |
| bounded here and not on the Cortex-M0 | 62 | 59 |

Flow facts: 542. Not bounded (same for both, 99 functions): a reached loop matched with a
source loop without a bound, 56; a call of an undefined symbol (double-precision floating
point, `memcpy`...: no run-time library), 22; a loop that matches no source loop, 12;
recursion, 7; a jump table, 2. On the Cortex-M7, OTAWA gives no result within 300 s for 6
more functions (its cache analysis; `basicmath___ieee754_acosf` in three kernels and three
functions of `jfdctint`). Of the 62 functions bounded only on the Cortex-M4, 57 call a
single-precision floating-point function of the run-time library on the Cortex-M0 (no code
there; an FPU instruction on the M4) and 5 call a function without a bound. The one
function bounded on the Cortex-M0 and not here, `bsort_BubbleSort`, has an outer loop whose
instructions the debug lines attribute to the function's first line and to the `if (Sorted)
break;` after the inner loop, never to the loop's own line, so it is matched with no
source loop (no bound, which is the safe outcome). The run takes 29 minutes, most of it the
Cortex-M7 analysis (at most 300 s per function, `--timeout`).

Bounds of the `main` functions, in cycles:

| Kernel | Cortex-M0 (timing schema, above) | Cortex-M4 (OTAWA) | Cortex-M7 (OTAWA) |
|---|---:|---:|---:|
| binarysearch | 32,686 | 47,228 | 34,433 |
| bsort | 369,779 | 8,087,233 | 3,683,167 |
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

## Stack bounds (2026-11-16)

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
