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

The whole run takes about four minutes (two and a half before the search for a potential was repeated with more candidate invariants, 2026-11-16). The same script runs in CI
(`.github/workflows/plugin_build.yml`), which uploads the JSON as a build artifact.

## Results (2026-11-15, with calling contexts, globals, fields, tables, C tests)

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
(in context, 7 bounds are larger and 2 smaller). Since 2026-11-15 the analysis tracks
globals and `static` variables, fields read through pointer parameters, constant tables
and C integer tests (`while (--j)`): `isqrt` gains a loop (a global counter), its entry
function a bound, and one more loop is bounded in context.

| Kernel | Loops | Derived | = max | > max | < max | No bound | Not reached | `_main` bound | In context: derived | = max | > max | < max |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| binarysearch | 2 | 2 | 1 | 1 | 0 | 0 | 0 | 386 | 2 | 1 | 1 | 0 |
| bitcount | 4 | 2 | 1 | 1 | 0 | 2 | 0 | — | 2 | 1 | 1 | 0 |
| bitonic | 3 | 2 | 2 | 0 | 0 | 1 | 0 | — | 2 | 2 | 0 | 0 |
| bsort | 4 | 4 | 4 | 0 | 0 | 0 | 0 | 240 702 | 4 | 4 | 0 | 0 |
| complex_updates | 4 | 4 | 4 | 0 | 0 | 0 | 0 | 871 | 4 | 4 | 0 | 0 |
| cosf | 3 | 1 | 1 | 0 | 0 | 2 | 0 | — | 0 | 0 | 0 | 0 |
| countnegative | 4 | 4 | 4 | 0 | 0 | 0 | 0 | 5 752 | 4 | 4 | 0 | 0 |
| cubic | 6 | 1 | 1 | 0 | 0 | 5 | 0 | — | 1 | 1 | 0 | 0 |
| deg2rad | 1 | 0 | 0 | 0 | 0 | 1 | 0 | — | 0 | 0 | 0 | 0 |
| fac | 1 | 0 | 0 | 0 | 0 | 1 | 0 | — | 0 | 0 | 0 | 0 |
| fft | 12 | 11 | 8 | 3 | 0 | 1 | 0 | 271 351 277 | 11 | 8 | 3 | 0 |
| filterbank | 14 | 11 | 11 | 0 | 0 | 3 | 0 | — | 11 | 11 | 0 | 0 |
| fir2dim | 17 | 9 | 9 | 0 | 0 | 8 | 0 | — | 9 | 9 | 0 | 0 |
| iir | 6 | 6 | 6 | 0 | 0 | 0 | 0 | 210 | 6 | 6 | 0 | 0 |
| insertsort | 4 | 2 | 2 | 0 | 0 | 2 | 0 | — | 2 | 2 | 0 | 0 |
| isqrt | 5 | 3 | 3 | 0 | 0 | 2 | 0 | 861 860 | 3 | 3 | 0 | 0 |
| jfdctint | 4 | 4 | 4 | 0 | 0 | 0 | 0 | 2 699 | 4 | 4 | 0 | 0 |
| lms | 7 | 4 | 4 | 0 | 0 | 3 | 0 | 115 950 | 7 | 7 | 0 | 0 |
| ludcmp | 12 | 12 | 3 | 9 | 0 | 0 | 0 | 4 903 | 12 | 12 | 0 | 0 |
| matrix1 | 7 | 7 | 7 | 0 | 0 | 0 | 0 | 15 496 | 7 | 7 | 0 | 0 |
| md5 | 9 | 2 | 2 | 0 | 0 | 7 | 0 | — | 5 | 5 | 0 | 0 |
| minver | 21 | 17 | 8 | 9 | 0 | 4 | 0 | — | 20 | 20 | 0 | 0 |
| pm | 30 | 5 | 5 | 0 | 0 | 25 | 0 | — | 5 | 5 | 0 | 0 |
| prime | 1 | 0 | 0 | 0 | 0 | 1 | 0 | — | 0 | 0 | 0 | 0 |
| quicksort | 16 | 5 | 4 | 0 | 1 | 11 | 0 | — | 5 | 4 | 0 | 1 |
| rad2deg | 1 | 0 | 0 | 0 | 0 | 1 | 0 | — | 0 | 0 | 0 | 0 |
| recursion | 0 | 0 | 0 | 0 | 0 | 0 | 0 | — | 0 | 0 | 0 | 0 |
| sha | 17 | 10 | 6 | 4 | 0 | 7 | 0 | — | 11 | 6 | 4 | 1 |
| st | 5 | 5 | 5 | 0 | 0 | 0 | 0 | 65 074 | 5 | 5 | 0 | 0 |
| **Total** | **220** | **133** | **105** | **27** | **1** | **87** | **0** | **12 kernels** | **142** | **131** | **9** | **2** |

## Certificates

With `--certificates=DIR` the script also emits a cost certificate for every function in
the certificate fragment (see `docs/certificate-format.md`), and with
`--checker=formalization/.lake/build/bin/crosscheck-check` it runs the verified Lean
checker on them and fails if one is rejected.

On 2026-11-14, after early exits, `switch`, `&&` tests and unsigned variables were added
to the generator: **156 of the 158 bounded functions** get a certificate, **all accepted
by the checker** (before: 142; 158 of 160 with logarithmic potentials on 2026-11-15, then 158 of 162 with growing logarithmic loops and exact unsigned division: `fft_bit_reduct` and `fft_main` are bounded but not certified, the generator's invariant does not show their logarithmic potential positive; `fft_main` brings the bounded entry functions to 11; since the retry with more candidate invariants of 2026-11-16, 161 of 165: the loop of `binarysearch` is bounded, linearly (29, flow fact 4), and `binarysearch_main` is the twelfth bounded entry function). The entry functions `<kernel>_main` of 9 kernels are
certified. 141 certified bounds equal the plugin's bound; 12 are smaller (9:
`__kernel_cosf` and its callers, in four kernels: the forward assertions show that an
expensive branch cannot follow an earlier test; 3 in `bsort`: the iteration that leaves
by `break` is counted without the increment and without the plugin's extra body); 3 are
larger (`ludcmp_main` and `main` of ludcmp: the entry bound of a loop is rounded up;
`pm_init_data`: a `?:` calls `pm_floor` in one arm and `pm_ceil` in the other, and the
certificate inlines both). Not certified: an assignment inside an expression
(`bitcount_bit_shifter`) and a loop whose potential has no upper bound in the
certificate's entry assertion (`ludcmp_test`). The script prints the reason for each
function that is not certified.

Since program certificates (2026-11-14) the figures are unchanged (156 of 158, 141 equal,
12 lower, all accepted); 120 calls are now checked against the callee's own certificate
(a summary) instead of being inlined. No kernel function has a summary that depends on its
parameters: the kernels' loops have constant bounds.

## Validation against the source (2026-11-15)

With `--minic` as well, every certified function is also exported as mini-C (option
`--opt=minic`, `clang-plugin/src/analysis/MiniC.cpp`) and the checker validates the
certificate's program against it (`MiniC.validated_sound`, Paper I `thm:validated`); the
script prints the counts and the exporter's reasons for refusing the others.

```bash
python3 benchmarks/tacle/run_tacle.py --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13 \
    --certificates=DIR --checker=formalization/.lake/build/bin/crosscheck-check --minic
```

Kernels (2026-11-16, 161 of 165 certified, all accepted): **144 certificates
validated, none failing validation** (93 before mini-C had quotients, remainders, shifts,
masks, unsigned stores and calls; 143 before `break`, `continue` and `return` inside
loops were exported with flag variables; 137 are validated together with every function
they call); 36 of them contain loops (60 of the 83 loops of the
certified programs), 8 are entry functions `<kernel>_main` (`binarysearch`, `bsort`, `complex_updates`,
`countnegative`, `iir`, `jfdctint`, `matrix1`, `st`; all but `st` with all
their callees); many of the others are small (initialisations, `*_return`). Refused by
the exporter: global or static tracked variables (6), `switch` (5; the earlier count
"`return` or `break` inside a loop (6)" hid them: only one of these functions,
`bsort_BubbleSort`, had a jump outside a `switch`), calls of functions without an entry
in the certificate file (4), calls in tests (2).

Sequential and application programs (`--category sequential --category app`): tables
unchanged (231 of 263 certified, all accepted); **170 validated, none failing** (2026-11-16; 113 before mini-C had division, unsigned
stores and calls), including
`petrinet_main` and `powerwindow_controlexclusion_main`. Refused: global or
static tracked variables (25), calls of functions without an entry in the certificate file
(8), divisions or shifts outside the modelled forms (9), `return` in loops or `switch` (7),
`switch` (4), `break`, `continue` (2), narrow unsigned variables (3), calls in tests (3).
One function (`gsm_enc_Weighting_filter`) was first exported and not validated: the
constant expression `8192 >> 1` was exported as a quotient where the generator folds it;
the exporter now folds constants first (and refuses that function for another statement).
The slowest program, `cjpeg_transupp`, needed 2,299 s on a shared machine (614 s on
2026-11-15, before the repeated search for potentials): set `CROSSCHECK_TACLE_TIMEOUT` above
the default 1,800 s when the machine is loaded.

## Sequential and application programs (2026-11-15)

```bash
python3 benchmarks/tacle/run_tacle.py --category sequential --category app \
    --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13 \
    --certificates=DIR --checker=formalization/.lake/build/bin/crosscheck-check
```

The 23 *sequential* and 2 *app* programs of TACLeBench (larger: up to 10,000 lines after
concatenation), without annotations, 572 loops with a flow fact:

| | Derived | = flow fact | > flow fact | < flow fact | No bound | Not reached |
|---|---|---|---|---|---|---|
| for every call | 275 | 258 | 8 | 9 | 287 | 10 |
| in context | 330 | 304 | 16 | 10 | | |

(2026-11-14, before globals, fields, tables and C integer tests: 263 / 252 / 7 / 4 for
every call, 317 / 297 / 15 / 5 in context.)

- **Below the flow fact (10 in context), none a counter-example.** Besides the five
  below, a loop of `lift` (`for (lift_level = 1; lift_level < 14; ++lift_level)`, 13
  iterations; flow fact 14) and four more loops of `h264_dec` under `if (smb)`, where
  `smb` is set to 0 and never changed (bound 0: the C test `if (smb)` is now a fact).
  The five of 2026-11-14: `h264_dec`: two loops
  `for (i = 0; i < sizeof(a); ++i)` over `signed char [65][65][2]` and
  `short [2][45][45]` run 8,450 and 8,100 times, the bounds derived; the flow facts say
  33,800 and 16,200. Two loops of `h264_dec_decode_one_macroblock` are in a branch that
  cannot run (`pred_dir = -1` just before `if (pred_dir != 2)`): bound 0. In
  `cjpeg_wrbmp`, the grayscale branch of `write_colormap` is not taken by the program's
  two calls (`cMap = 1`): bound 0 in context. Observed counts were not measured for these
  programs (`measure_loops.py` covers the kernels).
- **No bound** (297 loops for every call): mostly loops over data read from memory,
  global or `struct` counters, pointers and floating-point values, which the analysis
  does not track (see `docs/proposals.md` §4).
- **Entry functions** bounded without annotation: `adpcm_dec`, `adpcm_enc`, `petrinet`,
  `statemate`.
- **Certificates: 231 of 263 bounded functions, all 231 accepted by the checker**; 208
  equal to the plugin's bound, 13 smaller; 165 calls are checked against the callee's
  certificate. Not certified: assignments inside expressions (17), loop tests or conditions
  with a call or an assignment (10), calls with a trusted cost (5). (2026-11-14: 232 of 252.) Not certified: assignments inside expressions
  (15, `gsm_dec` and `gsm_enc`: the macros of the GSM code, e.g. `STEP`, use `*LARc++`
  inside an expression), calls to library functions
  with a trusted cost (5, `susan`: `sqrtf`, `atanf`, `cosf`, …).

## Flow facts compared with oRange's (2026-11-14)

```bash
python3 benchmarks/tacle/run_tacle.py --extra-arg=... --flow-facts=DIR   # FFX, in context
python3 benchmarks/tacle/compare_ffx.py DIR                             # vs results/orange/
```

Both FFX files are read the same way (every `<loop>` with `source`, `line` and a numeric
`maxcount`; for oRange the maximum over its calling contexts). On the 29 kernels:
**116 loops bounded in both files, 115 equal** (the loop of `binarysearch`: 29 against
oRange's 5); 29 only in CrossCheck's, 16 only in oRange's. (These are all loops of the files; `tab:tools` counts the 220 loops that have a
flow fact, 114 of them bounded by both.)

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
- **No bound (87 loops for every call, 78 in context).** `classify_unbounded.py` reads
  the reports of the last run and classifies these loops by the cause that the analyser
  states in its diagnostic (a hint computed where the loop starts, not a proof that no
  bound exists); `--list` prints every loop:
  - **55: a variable of the test has no known range where the loop starts**: a parameter
    with no range known at the call either, a global, a struct field or a value read
    from memory (most of `pm`, `md5`, `sha`; the loops of `lms`, `minver` and part of
    `md5` are bounded in context); annotations (`CROSSCHECK_RANGE` /
    `CROSSCHECK_REQUIRE`) would supply these ranges. The guard `i * i <= n` of `prime`
    and the bit normalisation of the soft-float library (`(ix & 0x00800000) == 0`) are
    in this class too, although a range would not be enough for them;
  - **27: the test does not depend on a tracked integer variable**. By reading the
    sources: 17 have a floating-point or `volatile` counter (`fir2dim` declares its
    counters `register float`; `cosf`, `cubic`, `deg2rad`, `rad2deg`, one loop of `pm`,
    one of `insertsort`), which the analyser does not model; 10 are driven by data
    (partitioning in `quicksort`, string comparison, a pointer comparison in `pm`,
    `while (1)` left by `break` in `md5` and `minver`);
  - **5: the variables of the test are bounded but no potential is found**: a limit held
    in a `volatile` global (`fac`) or in a `float` (`fft_exp2f`), a test combined with
    `&` (`filterbank`, 2 loops), insertion sort.
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
| bounded | 133 | 142 | 113 (+46 type range only) | 131 |
| equal to the flow fact | 105 | 131 | 108 | 127 |
| larger | 27 | 9 | 5 | 3 |
| smaller | 1 (loose flow fact) | 2 (loose flow facts) | 0 | 1 (wrong bound, see below) |

CrossCheck's bounds for every call and ScalarEvolution's are both obtained from one
function at a time. 104 loops are bounded by both; there the bounds agree on 99,
CrossCheck's is smaller on 4 (loops left by `break`, which must be counted once more
from LLVM's backedge-taken count) and ScalarEvolution's is smaller by one on the doubling
loop of `fft` (10, exact, against the logarithmic bound 11). 29 loops are bounded only by CrossCheck (one more since 2026-11-16: the loop of `binarysearch`): 18 in
`ludcmp` and `minver` (where ScalarEvolution has only the type range, or nothing), two
whose guard combines the counter with another condition (`x && i < 64`,
`m >= 2 && j >= m`), two in `sha`, one in `isqrt`, one empty loop, and four bounded since exact unsigned
division (2026-11-15: in `cosf`, `cubic`, `isqrt`, `quicksort`). 9 are bounded only by ScalarEvolution: the 9 loops with
floating-point counters, which it evaluates exhaustively because start, step and
limit are constants.

**Against executions.** `measure_loops.py` instruments the unoptimised LLVM IR of
each kernel (the loop's preheader resets a counter local to the function activation,
the loop's `for.body` / `while.body` / `do.body` block increments it) and runs the
kernel on its built-in input. This gives, for every loop, the largest number of
body executions in one entry of the loop. 208 of the 220 loops are reached (the
others are in code the input does not execute, e.g. 6 loops of `pm`).
`test_measure_loops.py` runs the instrumentation on a program whose 13 counts are known
by construction (`do` loops, `break`, `continue`, a loop entered several times, nested
loops, recursion, a body that never runs, `while (n-- > 0)`); it is run in CI.

| loops reached (208) | CrossCheck, every call | CrossCheck, in context | ScalarEvolution | oRange | flow fact |
|---|---:|---:|---:|---:|---:|
| bounded | 131 | 142 | 113 | 131 | 208 |
| below the observed count | **0** | **0** | **0** | 1 | 2 |
| equal to it | 103 | 132 | 107 | 127 | 198 |
| above it | 28 | 10 | 6 | 3 | 8 |
| bound / observed: median, geometric mean, max | 1.00, 1.85, 166.7 | 1.00, 1.04, 7.2 | 1.00, 1.02, 3.5 | 1.00, 1.00, 1.2 | 1.00, 1.01, 2.5 |

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
those in context. Compared loop by loop: 115 loops are bounded by both, with
**identical bounds on 114** (the exception: `binarysearch`, oRange 5, CrossCheck 29, the flow
fact 4) (against CrossCheck's bounds for every call: 87
identical, oRange tighter on 18, in `ludcmp` and `minver`). 16 loops are bounded only
by oRange: 12 with floating-point counters (`cosf`, `deg2rad`, `rad2deg`, `pm`, 8 in
`fir2dim`), loops on a global or `volatile` counter (`insertsort`, and the
wrong `filterbank` bound), and `fft`, `insertsort` (data-dependent or
halving). 27 are bounded only by CrossCheck: 10 in kernels where oRange gives no
result, 6 with a guard `i < sizeof( a )` (`fir2dim`, `iir`), 4 in `fft`, 5 in `sha`,
1 in `isqrt` and 1 in `md5` (oRange reports `NOCOMP`). oRange gave no result on 5 kernels: `bitonic`, `quicksort` and
`recursion` are rejected ("complex recursivity"), `bitcount` raises an internal
error (`Failure("frontc/iftofor.ml : list_string_of_paire")`), and `cubic` did not
finish in 600 s. It took 251 s on `pm` and at most 7 s on the others.

**Functions** (entry function `<kernel>_main` of the 29 kernels; all 267 functions):

| | CrossCheck | KoAT2 | CoFloCo | Infer |
|---|---:|---:|---:|---:|
| entry functions with a numeric bound | 12 | 5 | 8 | 14 |
| entry functions with a symbolic bound | 0 | 5 | 0 | 2 |
| functions with a numeric / symbolic bound | 165 / 0 | 119 / 23 | 128 / 11 | 190 / 14 |

Reading this table:

- **Infer** bounds the most functions, mainly because it is interprocedural: a
  callee whose loop bound is a parameter (e.g. in `lms`) gets the
  bound from its call site. CrossCheck does the same through calling contexts (it now
  bounds `lms_main`), but the function-level counts here are its bounds for every call.
  But its results are not upper bounds in every case: its documentation
  (https://fbinfer.com/docs/checker-cost, section "Limitations", read 2026-11-16)
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
