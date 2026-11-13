# TACLeBench kernels

[TACLeBench](https://github.com/RTSYork/tacle-bench) (Falk et al., *TACLeBench: A
Benchmark Collection to Support Worst-Case Execution Time Research*, WCET 2016,
OASIcs 55, [doi:10.4230/OASIcs.WCET.2016.2](https://doi.org/10.4230/OASIcs.WCET.2016.2))
is a benchmark collection for WCET research, gathered from several earlier suites, among
them the Mälardalen WCET benchmarks (Gustafsson et al., WCET 2010). Its programs are self-contained C, and
every loop carries a flow fact `#pragma loopbound min X max Y`.

`run_tacle.py` fetches a pinned revision (`4e4fbf7`, 2020-10-15) into `.cache/`
(gitignored; the benchmark files carry various licences and are not copied here),
runs `crosscheck-tool --all` on each of the 29 kernel programs **without adding any
annotation**, and compares each loop bound the tool proves with the pragma's maximum.

```bash
# from the repository root, after building the plugin
python3 benchmarks/tacle/run_tacle.py --markdown=out.md --latex=out.tex --json=out.json
# on the author's machine (conda Clang), add:
#   --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13
```

The whole run takes about one minute. The same script runs in CI
(`.github/workflows/plugin_build.yml`), which uploads the JSON as a build artifact.

## Results (2026-11-13, with calling contexts)

Two bounds are reported for a loop (see the plugin's README, "Calls"):

- **for every call**: the bound holds for every call of the loop's function that meets
  its preconditions (columns "Derived" to "No bound");
- **in context**: the bound holds in the calling contexts through which the program's
  `main` reaches the function (`--opt=entry=main`; last two columns). This is the one
  comparable with the flow facts, which describe the program on its fixed input.

Columns: loops with a `loopbound` pragma; loops for which the tool proves a bound for
every call; of these, bound equal to / larger than / smaller than the pragma's maximum;
loops with no such bound; cost bound of the kernel's entry function `<kernel>_main`
(abstract units, unit weights), or "—" if any loop or call it reaches is unbounded;
loops bounded in context, and how many of those bounds equal the pragma's maximum
(in context, 7 bounds are larger and 2 smaller).

| Kernel | Loops | Derived | = max | > max | < max | No bound | `_main` bound | In context: derived | = max |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| binarysearch | 2 | 1 | 1 | 0 | 0 | 1 | — | 1 | 1 |
| bitcount | 4 | 2 | 1 | 1 | 0 | 2 | — | 2 | 1 |
| bitonic | 3 | 2 | 2 | 0 | 0 | 1 | — | 2 | 2 |
| bsort | 4 | 4 | 4 | 0 | 0 | 0 | 240 702 | 4 | 4 |
| complex_updates | 4 | 4 | 4 | 0 | 0 | 0 | 871 | 4 | 4 |
| cosf | 3 | 0 | 0 | 0 | 0 | 3 | — | 0 | 0 |
| countnegative | 4 | 4 | 4 | 0 | 0 | 0 | 5 752 | 4 | 4 |
| cubic | 6 | 0 | 0 | 0 | 0 | 6 | — | 0 | 0 |
| deg2rad | 1 | 0 | 0 | 0 | 0 | 1 | — | 0 | 0 |
| fac | 1 | 0 | 0 | 0 | 0 | 1 | — | 0 | 0 |
| fft | 12 | 10 | 8 | 2 | 0 | 2 | — | 10 | 8 |
| filterbank | 14 | 11 | 11 | 0 | 0 | 3 | — | 11 | 11 |
| fir2dim | 17 | 9 | 9 | 0 | 0 | 8 | — | 9 | 9 |
| iir | 6 | 6 | 6 | 0 | 0 | 0 | 210 | 6 | 6 |
| insertsort | 4 | 2 | 2 | 0 | 0 | 2 | — | 2 | 2 |
| isqrt | 5 | 1 | 1 | 0 | 0 | 4 | — | 2 | 2 |
| jfdctint | 4 | 4 | 4 | 0 | 0 | 0 | 2 699 | 4 | 4 |
| lms | 7 | 4 | 4 | 0 | 0 | 3 | 115 950 | 7 | 7 |
| ludcmp | 12 | 12 | 3 | 9 | 0 | 0 | 4 903 | 12 | 12 |
| matrix1 | 7 | 7 | 7 | 0 | 0 | 0 | 15 496 | 7 | 7 |
| md5 | 9 | 2 | 2 | 0 | 0 | 7 | — | 5 | 5 |
| minver | 21 | 17 | 8 | 9 | 0 | 4 | — | 20 | 20 |
| pm | 30 | 5 | 5 | 0 | 0 | 25 | — | 5 | 5 |
| prime | 1 | 0 | 0 | 0 | 0 | 1 | — | 0 | 0 |
| quicksort | 16 | 4 | 3 | 0 | 1 | 12 | — | 4 | 3 |
| rad2deg | 1 | 0 | 0 | 0 | 0 | 1 | — | 0 | 0 |
| recursion | 0 | 0 | 0 | 0 | 0 | 0 | — | 0 | 0 |
| sha | 17 | 10 | 6 | 4 | 0 | 7 | — | 11 | 6 |
| st | 5 | 5 | 5 | 0 | 0 | 0 | 65 074 | 5 | 5 |
| **Total** | **220** | **126** | **100** | **25** | **1** | **94** | **9 of 29** | **137** | **128** |

## Reading the results

- **Flow facts are a reference, not ground truth.** They describe each program on its
  fixed built-in input, and some are not tight. The one bound *below* a pragma is
  `quicksort_init`, `for (j = 0; j < 20 - 1; j++)`: at most 19 iterations, while the
  pragma says 20. The tool's bound is the correct one.
- **Larger than the pragma (25 loops for every call, 7 in context).** A bound for
  every call covers every admissible argument (`ludcmp`: 99 instead of 5; `minver`: 500
  instead of 3, from its test `side > 500`); in context both become exact, and the bound
  of `ludcmp_main` drops from 22 961 019 to 4 903. What remains in context: `fft` loops
  whose true bound is logarithmic while potentials are linear (1023 instead of 10), four
  `sha` loops and one `bitcount` loop whose flow facts hold for the built-in input only.
- **Smaller than the pragma in context (2 loops).** `quicksort_init` (above) and a
  `sha` loop bounded by 8 where the flow fact says 16; the run observes 8.
- **No bound (94 loops for every call, 83 in context).** By inspection of the sources,
  in decreasing order of frequency:
  - the bound is a struct field or a global, or a parameter with no range known at the
    call either (most of `pm`, `md5`, `sha`), which annotations (`CROSSCHECK_RANGE` /
    `CROSSCHECK_REQUIRE`) would supply; calling contexts supply the parameters of
    `lms`, `minver` and part of `md5`;
  - floating-point loop counters (`fir2dim` declares them `register float`; `cosf`,
    `cubic`, `deg2rad`, `rad2deg`, one loop of `pm`), which the analyser does not model;
  - `volatile` counters or bounds (`insertsort`, `fac`), and counters or bounds held
    in global variables, which the analyser does not track (`filterbank`, `bitcount`,
    `isqrt`);
  - loops whose bound is not affine in the program variables: halving or doubling
    (`binarysearch`, `fft`), `i * i <= n` (`prime`), loops driven by data
    (insertion sort, partitioning in `quicksort`, string comparison, bit
    normalisation in the soft-float library), and `while (1)` with `break`.
- **Recursion.** `recursion` (Fibonacci) and `fac` are rejected because the recursive
  argument has no range; `recursion` has no loops, so it does not appear in the totals.
- The 9 kernels with a `_main` bound are bounded with **no annotation and no
  assumption**. No timing is implied (see the plugin's README, "Limitations").

## Comparison with other tools (2026-11-13)

`compare_tools.py` compares CrossCheck with five existing analysers on the same 29
kernels (the same concatenated sources, no annotations):

| Tool | Version | What it computes | How it was run |
|---|---|---|---|
| LLVM ScalarEvolution | LLVM 18 | constant maximum trip count of each loop, intraprocedural | live, by `llvm_scev.py` (unoptimised IR + `mem2reg`) |
| KoAT2 | v2.1.0 Docker image | runtime-complexity bound of a function (callees inlined), on an integer program translated from C by llvm2kittel | `koat_in_container.sh`, 60 s per function, container without network |
| CoFloCo | Docker image `afloresmontoya/cofloco` (2021-09-25, digest `sha256:5f9d1664…`) | upper bound on the cost of a cost-equation system (Flores-Montoya & Hähnle, APLAS 2014); one unit per transition | on the **same** llvm2kittel integer programs as KoAT2 (`its_in_container.sh`), converted by CoFloCo's own `interfaces/C2ces`; `cofloco_in_container.sh`, 60 s per step, container without network |
| Infer cost analysis | v1.3.0 | symbolic execution cost of each function, interprocedural | `infer --cost-only`, in a container without network |
| oRange (OTAWA) | source repository `statinf-otawa/orange` at `b2b889f` (2022-11-21), FrontC from IRIT's repository at `635942a` (2023-11-17), OCaml 4.14 | loop bounds of the whole program from `main` (abstract interpretation; de Michiel et al., RTCSA 2008) | `orange_in_container.sh`, 600 s per kernel, container without network; the `loopbound` pragmas are blanked first, since oRange reads them |
| (measurement) | — | largest body-execution count per loop entry, on the built-in input | live, by `measure_loops.py` (instrumented IR, linked with `cc`) |

The answers of KoAT2, CoFloCo, Infer and oRange are stored in `results/` (`koat2/*.tsv`,
`cofloco/*.tsv`, `infer/*.json`, `orange/*.xml`); `results/comparison.json` is the script's output. The cost **units
differ** (CrossCheck: source operations; KoAT2: transitions of the translated
program; Infer: its own instruction count), so the function-level comparison is
only on *whether* a finite bound is found, not on its value.

**Loops** (220 loops with a flow fact; a ScalarEvolution bound of 2^24 or more is
counted as "type range only": it comes from the range of the integer type, which
CrossCheck never uses as a bound; 10 of the 220 loops are in static functions that
are never called, which Clang does not emit, so ScalarEvolution never sees them):

| | CrossCheck, every call | CrossCheck, in context | ScalarEvolution | oRange |
|---|---:|---:|---:|---:|
| bounded | 126 | 137 | 113 (+46 type range only) | 131 |
| equal to the flow fact | 100 | 128 | 108 | 127 |
| larger | 25 | 7 | 5 | 3 |
| smaller | 1 (loose flow fact) | 2 (loose flow facts) | 0 | 1 (wrong bound, see below) |

CrossCheck's bounds for every call and ScalarEvolution's are both obtained from one
function at a time. 103 loops are bounded by both; there the bounds agree on 99 and
CrossCheck's is smaller on 4 (loops left by `break`, which must be counted once more
from LLVM's backedge-taken count). 23 loops are bounded only by CrossCheck: 18 in
`ludcmp` and `minver` (where ScalarEvolution has only the type range, or nothing), two
whose guard combines the counter with another condition (`x && i < 64`,
`m >= 2 && j >= m`), two in `sha` and one empty loop. 10 are bounded only by ScalarEvolution: the 9 loops with
floating-point counters, which it evaluates exhaustively because start, step and
limit are constants, and one doubling loop in `fft`.

**Against executions.** `measure_loops.py` instruments the unoptimised LLVM IR of
each kernel (the loop's preheader resets a counter local to the function activation,
the loop's `for.body` / `while.body` / `do.body` block increments it) and runs the
kernel on its built-in input. This gives, for every loop, the largest number of
body executions in one entry of the loop. 208 of the 220 loops are reached (the
others are in code the input does not execute, e.g. 6 loops of `pm`).

| loops reached (208) | CrossCheck, every call | CrossCheck, in context | ScalarEvolution | oRange | flow fact |
|---|---:|---:|---:|---:|---:|
| bounded | 126 | 137 | 113 | 131 | 208 |
| below the observed count | **0** | **0** | **0** | 1 | 2 |
| equal to it | 100 | 129 | 107 | 127 | 198 |
| above it | 26 | 8 | 6 | 3 | 8 |
| bound / observed: median, geometric mean, max | 1.00, 1.93, 166.7 | 1.00, 1.06, 102.3 | 1.00, 1.02, 3.5 | 1.00, 1.00, 1.2 | 1.00, 1.01, 2.5 |

(Ratios are over the loops with a nonzero count.)

- No bound of CrossCheck (for every call or in context) or of ScalarEvolution is below
  an observed count; `compare_tools.py --check` fails otherwise. One of
  oRange's is: `filterbank` line 94, `while ( filterbank_numiters-- > 0 )` with
  `filterbank_numiters = 2` (set in `filterbank_init`), runs twice; oRange reports
  `maxcount="1"`.
- The two flow facts below the count (`md5` line 562: 256 vs 257, `quicksort` line
  745: 169 vs 170) are `while (1)` loops left by `break`; the flow facts are
  consistent with counting only the iterations that return to the loop head, not
  the last pass that leaves by `break`.
- The flow facts agree with the measurement on 198 loops, which is also a check of
  the instrumentation. Where they are above it (8 loops), the input does not reach
  the documented maximum, e.g. `quicksort_init`'s inner loop: 13 observed, flow fact
  20, CrossCheck 19 (the `for` guard; the `break` on `'\0'` comes earlier on this
  input).
- The observed counts are for one input, so a bound above them is not necessarily
  loose. For the bounds valid for every call, the large ratios are the distance between
  all admissible calls and the calls the program makes: `minver_minver` tests
  `side <= 500` and is called with `side = 3` (500 / 3); `ludcmp` likewise (99 / 5).
  In context these are exact; what remains is `fft`, a linear potential on a
  logarithmic loop (1023 / 10).

**oRange** analyses the whole program from `main`, propagating the values of the
built-in input: its bounds are bounds for the program as given, like the flow facts,
and it agrees with them on 127 of its 131 loops. The comparable CrossCheck bounds are
those in context. Compared loop by loop: 113 loops are bounded by both, with
**identical bounds on all 113** (against CrossCheck's bounds for every call: 87
identical, oRange tighter on 18, in `ludcmp` and `minver`). 18 loops are bounded only
by oRange: 12 with floating-point counters (`cosf`, `deg2rad`, `rad2deg`, `pm`, 8 in
`fir2dim`), loops on a global or `volatile` counter (`isqrt`, `insertsort`, and the
wrong `filterbank` bound), and `binarysearch`, `fft`, `insertsort` (data-dependent or
halving). 24 are bounded only by CrossCheck: 8 in kernels where oRange gives no
result, 6 with a guard `i < sizeof( a )` (`fir2dim`, `iir`), 3 in `fft`, 5 in `sha`,
1 in `isqrt` and 1 in `md5` (oRange reports `NOCOMP`). oRange gave no result on 5 kernels: `bitonic`, `quicksort` and
`recursion` are rejected ("complex recursivity"), `bitcount` raises an internal
error (`Failure("frontc/iftofor.ml : list_string_of_paire")`), and `cubic` did not
finish in 600 s. It took 251 s on `pm` and at most 7 s on the others.

**Functions** (entry function `<kernel>_main` of the 29 kernels; all 267 functions):

| | CrossCheck | KoAT2 | CoFloCo | Infer |
|---|---:|---:|---:|---:|
| entry functions with a numeric bound | 9 | 5 | 8 | 14 |
| entry functions with a symbolic bound | 0 | 5 | 0 | 2 |
| functions with a numeric / symbolic bound | 158 / 0 | 119 / 23 | 128 / 11 | 190 / 14 |

Reading this table:

- **Infer** bounds the most functions, mainly because it is interprocedural: a
  callee whose loop bound is a parameter (e.g. in `lms`) gets the
  bound from its call site. CrossCheck does the same through calling contexts (it now
  bounds `lms_main`), but the function-level counts here are its bounds for every call.
  But its cost analysis is not designed as a sound upper bound: its documentation
  says "We do not handle recursion", and it reports constant costs for the
  recursive `recursion_fib` (13) and `fac_fac` (10), so its result for the
  `recursion` kernel is wrong. It also relies on array accesses being in bounds
  (e.g. the inner loop of `insertsort`).
- **KoAT2** translates C through llvm2kittel (with the Clang 3.4 of the image), which
  keeps only integer variables: values in memory become unknown inputs, hence the
  symbolic bounds in variables `Arg_i` (e.g. `matrix1_main`: `4*Arg_0+2656`). 65
  functions could not be translated or timed out in the translation, and for 23
  KoAT2 timed out or failed. It bounds `prime`, whose guard `i * i <= n` is not affine, which
  neither CrossCheck nor ScalarEvolution does.
- **CoFloCo** analyses the same 202 integer programs as KoAT2, in the same unit
  (transitions), so the values can be compared: of the 117 functions both bound by a
  number, the bounds are equal on 97 and CoFloCo's is smaller on 20 (e.g. `bsort_main`
  40 798 vs 59 900), never larger. It has fewer symbolic answers (11 vs 23). Its 8
  entry-function bounds are CrossCheck's 9 kernels without `st` (timeout).
  Where the two disagree on finiteness, "Infinity" means no bound was found, not
  non-termination: `md5_R_RandomInit`'s program counts down from 16 to 0, CoFloCo
  gives 36, KoAT2 "Infinity".
- **No contradiction.** No function that CrossCheck bounds is reported unbounded
  ("Infinity") by KoAT2 or CoFloCo (where they give no bound, llvm2kittel failed or
  they timed out). Infer finds no bound for one of them,
  `bitcount_bit_shifter`, whose loop guard `i < sizeof(long) * 8` gives CrossCheck's
  bound of 64 (the flow fact says 31: it holds for the benchmark's fixed input).

What this comparison does not show: the tools were not designed for the same
question (WCET-style constant bounds vs. asymptotic complexity vs. cost regression
detection), the kernels are small, and no tool was given annotations or tuned.
