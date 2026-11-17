# TPDB complexity programs (C)

The [Termination Problem Database](https://github.com/TermCOMP/TPDB) holds the
benchmarks of the Termination and Complexity Competition (Giesl et al., TACAS 2019,
[doi:10.1007/978-3-030-17502-3_10](https://doi.org/10.1007/978-3-030-17502-3_10)).
Its directory `Complexity_C_Integer` contains the C programs on which complexity
analysers such as KoAT2 and CoFloCo are evaluated: 553 programs at the pinned
revision (`bf19a3c`, 2025-08-19), in six families. They are functions of integer
parameters, often with nondeterministic values (`__VERIFIER_nondet_int()`,
`nondet()`), and their costs are symbolic (`O(n)`, `O(n^2)`, …).

Unlike TACLeBench, these programs are written for complexity analysers, not for
CrossCheck's question (numeric bounds for real-time code). They show where
CrossCheck is weak.

```bash
# from the repository root, after building the plugin (about 10 minutes)
python3 benchmarks/tpdb/run_tpdb.py --json=out.json
#   on the author's machine add --extra-arg=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13
# KoAT2 and CoFloCo answers (stored in results/; to regenerate, several hours with 4 jobs):
benchmarks/tpdb/tools_in_containers.sh 4
```

## How each tool is run

- **CrossCheck, as is**: the file unchanged, compiled as C, `--all`.
- **CrossCheck, inputs in [-1000, 1000]**: a script (`harness()` in `run_tpdb.py`)
  adds `CROSSCHECK_RANGE(-1000, 1000)` to every `int` parameter,
  `CROSSCHECK_ASSUME(-1000 <= v && v <= 1000)` after every assignment from a declared
  but undefined function (the nondeterministic values), and `CROSSCHECK_COST(1)` to
  those functions; compiled as C++ for the annotation macros (2 of 553 programs do not
  compile as C++). A bound in this mode holds **for these inputs only**: it is not an
  asymptotic bound, and it is compared with the other tools only on *whether* a
  program gets a bound.
- **KoAT2 and CoFloCo**: as for TACLeBench (`../tacle/koat_in_container.sh`,
  `its_in_container.sh`, `cofloco_in_container.sh`): llvm2kittel per function, 60 s
  timeouts, containers without network. Their bounds hold for all inputs.

The *entry function* of a file is the defined function that no other function of the
file calls (the last one if there are several).

## Results (2026-11-17)

Programs whose entry function gets a bound:

| Family | Programs | CrossCheck as is | CrossCheck, inputs in [-1000, 1000] | KoAT2 | CoFloCo |
|---|---:|---:|---:|---:|---:|
| Benamram_2025 | 14 | 0 | 0 | 8 | 0 |
| Flores-Montoya_2017 | 458 | 11 | 207 | 254 | 246 |
| Lommen_22 | 20 | 0 | 1 | 1 | 1 |
| Lommen_23 | 15 | 0 | 1 | 6 | 1 |
| Lommen_24 | 20 | 0 | 0 | 1 | 0 |
| Sinn_2016 | 26 | 0 | 6 | 18 | 16 |
| **Total** | **553** | **11** | **215** | **288** | **264** |

(2026-11-13: 165 with ranges; then one more in `Sinn_2016`; five more in
`Flores-Montoya_2017` since logarithmic potentials and exact unsigned division, 2026-11-15;
36 more on 2026-11-16, since the search for a potential is repeated with more candidate
invariants (`docs/proposals.md`, step 9). One program, `sipmamergesort2`, exceeded the 120 s
limit in both modes in that run, on a machine shared with other work; it had no bound before.
2026-11-17: 8 more, since conditional expressions keep the facts true in both arms
(`len -= min(len, 64)`) and a disequality in a loop guard is split into two paths
(`while (p != q)`); all 8 are also bounded by KoAT2 or CoFloCo.)

KoAT2 or CoFloCo bound 305 programs. CrossCheck with ranges against them:

| | KoAT2 or CoFloCo: bound | no bound |
|---|---:|---:|
| CrossCheck (ranges): bound | 198 | 17 |
| no bound | 107 | 231 |

Reading the results:

- **As is**, the analysis bounds only the 11 programs whose loops have constant bounds
  (for bounds in the parameters without ranges, see the last section).
- **The 17 programs bounded only by CrossCheck.** Eleven (`CookSeeZuleger-TACAS2013-Fig1`,
  `Fig7a`, `Fig7b`, `Nyala-2lex`, `PastaC9`, `PodelskiRybalchenko-TACAS2011-Fig4`, and since
  2026-11-16 `ChenFlurMukhopadhyay-SAS2012-Ex2.22`, `Ex3.09`, `NonTermination2`, `aaron3`,
  `realheapsort`)
  assign a nondeterministic value to a variable inside the loop: they terminate, but
  their cost has no bound in terms of the inputs, so KoAT2 and CoFloCo are right to
  report none; CrossCheck bounds them only because the harness also restricts those
  values. `NonTermination2` does not terminate for unbounded inputs; with
  the nondeterministic value in [-1000, 1000] it does (a variable at least doubles at every
  iteration). `Sinn_2016/CPU2006_ApplyBndRobin` (four nested loops) is
  bounded for the given ranges; KoAT2 and CoFloCo timed out on it. Five have no
  nondeterministic value in a loop and are not bounded by the two tools:
  `ChenFlurMukhopadhyay-SAS2012-Ex2.13`, `Ex3.01`, `LeikeHeizmann-TACAS2014-Ex7`, `PlusSwap`
  and `C4B_examples/t30`. Their potentials (`1000 - y`, `1000 - x`, `q + z/2 + 500`,
  `x + y + 1000` twice) are in certificates that the Lean checker accepts (run on 2026-11-16 for these five):
  each decreases by 1 per iteration and is at least 1 under the loop test, using the
  ranges of the variables as invariants.
- **History.** The first run of this comparison gave 141 programs in the ranged mode.
  Keeping the facts of each `break` path at a loop exit, joining intervals where paths
  merge, and recognising `x = x + 1` as an increment (for invariant candidates) added
  24 programs and lost none; all 24 are also bounded by KoAT2 or CoFloCo.
- **The 107 programs bounded by KoAT2 or CoFloCo and not by CrossCheck** (147 when the first sample below was drawn, 115 for the second). Almost all of
  CrossCheck's failures in this mode are "cannot derive an iteration bound" (the
  others: unstructured control flow in 3, a missing definition in 1, and the 2 programs
  that do not compile as C++). A sample of ten was drawn (`random.seed(1)`) from the
  171 programs of the first run; two of them are bounded now
  (`speed_popl10_sequential_single`, `HeizmannHoenickeLeikePodelski-ATVA2013-Fig1`).
  In the sample, the missing ingredients:
  - bounds not given by one linear potential: guards `x != y` (`svcomp_a.10`),
    `x - y > 2 || y - x > 2` (`wise`), counters that are reset (`speedpldi2`), a
    loop that changes direction (`GopanReps-CAV2006-Fig1a`);
  - relations carried from one loop to the next: `Loopus2015_ex2` needs `x <= m + 2n`
    from the first loop; nested loops sharing counters (`nested_loop`, `alain`,
    `sendMTFValues`) need amortisation;
  - (now handled) a fact needed after a loop that may exit by `break`
    (`speed_popl10_sequential_single`), and an invariant on a variable that grows
    (`HeizmannHoenickeLeikePodelski-ATVA2013-Fig1`).
- **A second sample (2026-11-16)**, to check that the first one is representative: ten
  programs drawn (`random.seed(2026)`) from the 115 of that day, classified by reading them.
  Guards that one linear potential does not handle: `y1 != y2` with subtractions
  (`BradleyMannaSipma-CAV2005-Fig1`), `p != q` (`LeikeHeizmann-TACAS2014-Ex9`, whose
  potential `p + q` decreases on every path that the guard allows, but the analysis does
  not split `p != q` in the body), `x - y > 2 || y - x > 2` (`wise`, drawn in both
  samples). Nested loops that share counters and need amortisation: `Loopus2014_ex1`,
  `Loopus2014_ex2` (pushes and pops), `rank2`, `cBench_s_SFD_process` (a counter that
  moves back), `cBench_subsetdump` (an inner loop that advances the outer counter). A
  relation carried out of an inner loop: `gcd1` (`r < y` after the inner loop makes `y`
  decrease). A conditional expression: `cBench_zwritehexstring_at` (`len -= min(len, 64)`),
  which the analysis did not relate to its arms; it now keeps the facts true in both arms
  (`m <= a` and `m <= b` for `a < b ? a : b`) and bounds it. The two samples give the same
  picture: disequalities and disjunctions in guards, and amortisation across nested
  loops, account for most of the programs that the other tools bound and CrossCheck does
  not.
- KoAT2's classes for the 305 programs it or CoFloCo bounds are mostly `O(n)` and
  `O(n^2)`; for the 165 that CrossCheck bounded on 2026-11-13, KoAT2 gives `O(n)` for 109, `O(n^2)` for
  29 and `O(1)` for 18.

What this does not show: the bounded mode answers a different question (a bound for
inputs in a range), and the ranges also make the nondeterministic values bounded, which
the other tools do not assume. Stored: `results/koat2/`, `results/cofloco/` (one
`.tsv` per program, named after its path), `results/tpdb.json` (the script's output).

## Certificates (2026-11-14, program certificates)

```bash
python3 benchmarks/tpdb/run_tpdb.py --extra-arg=... --certificates=DIR \
    --checker=formalization/.lake/build/bin/crosscheck-check
```

In the second mode (inputs in [-K, K]), **159 of the 215 bounded entry functions are
certified, all accepted by the checker** (2026-11-17): 97 with a *summary* affine in their
parameters (e.g. `c + a*max(0,n)`, valid for every input in the ranges), 62 with a
constant bound, 56 not certified. For 74 of the 97, KoAT2 also reports a linear bound.
(2026-11-16: 114 summaries, 45 constant, 48 none, of 207; 156, 42 and 51 before `do` loops
were certified.) Since the amortised loop rules (prompts 47 and 48), 17 functions get a
constant amortised bound instead of a summary: the generator compares its candidates at
the largest admissible inputs, where the amortised bound is about half the summary
(`jama_ex2`: 2,009,003 against `7003 + 4000*max(0,n)` = 4,007,003 at `n = 1000`), but
it no longer depends on the parameters (the amortised node needs a constant entry
bound), so for small inputs the summary was the better bound. The harness's
`CROSSCHECK_COST(1)` declarations become assumed contracts (46 entries). The analysis still
needs the ranges to bound a loop: in the first mode ("as is") the figures are unchanged.

## Without input ranges: certified bounds in the parameters (2026-11-17)

```bash
python3 benchmarks/tpdb/run_tpdb.py --extra-arg=... --certificates=DIR \
    --checker=formalization/.lake/build/bin/crosscheck-check --symbolic [--only-symbolic]
```

A third mode, with the tool's option `symbolic`: no range is added. A loop needs only a
ranking potential; the analysis gives no numeric bound, and the certificate generator
derives a bound in the parameters (in `max(0, x)`, `max(0, -x)` and `max(0, x - y)` of
the integer parameters), affine or, since 2026-11-17, quadratic (products of two such
terms, from a nest of two loops over parameters or from a call), which the checker
accepts or not. The harness
of this mode does two things to a file: undefined functions get a unit cost (as in the
bounded mode), and, in the entry function, **a value read from an undefined function
before the first loop becomes a parameter** (`x = nondet();` is replaced by `x = in_k;`,
and `main` is renamed `main_`). The competition's tools treat these values as inputs of
the program as well; a certified bound can only mention parameters. Values read inside or
after a loop stay unknown.

| Entry functions (553 programs) | |
|---|---:|
| certificate accepted, bound in the parameters | **133** |
| certificate accepted, constant bound | 14 |
| potentials for every loop, no certificate | 95 |
| a loop without a potential, or another error | 311 |
| timeout | 0 |

- All 147 certificates are accepted by the checker: these bounds hold **for all inputs**,
  with no annotation and no assumption on ranges (signed overflow is assumed absent, as
  everywhere). All 147 programs are also bounded by KoAT2 or CoFloCo; on the 133 with a
  bound in the parameters KoAT2 answers `O(n)` for 96, `O(n^2)` for 34 and `O(1)` for 3
  (there our bound is looser than necessary). Before quadratic terms (2026-11-16): 103
  (89 + 14), and KoAT2 `O(n)` for 86 of the 89; (101 = 87 + 14 before `do` loops were
  certified.)
- Before the two changes that followed the first run of this mode the count was 59 (45 +
  14): logical variables for `-x` and `x - y` (a loop `while (a < 30)` costs
  `max(0, -a)`), and nondeterministic inputs as parameters.
- No certificate, of the 135 of the run before `do` loops were certified (139 on 2026-11-17, after the analyser changes above): a product of two symbolic quantities, as in nested loops
  both bounded by parameters (47: certified bounds are affine); a potential with no
  bound of that form on entry (36); a loop test with a call or an assignment (28); the
  generator's invariants too weak (16); `do` loops and labels (6); other (2).
- KoAT2 or CoFloCo bound 305 programs: 158 of them have no certificate here (202 before quadratic terms).
