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

## Results (2026-11-13, analyser with facts kept across `break`)

Programs whose entry function gets a bound:

| Family | Programs | CrossCheck as is | CrossCheck, inputs in [-1000, 1000] | KoAT2 | CoFloCo |
|---|---:|---:|---:|---:|---:|
| Benamram_2025 | 14 | 0 | 0 | 8 | 0 |
| Flores-Montoya_2017 | 458 | 10 | 161 | 254 | 246 |
| Lommen_22 | 20 | 0 | 1 | 1 | 1 |
| Lommen_23 | 15 | 0 | 1 | 6 | 1 |
| Lommen_24 | 20 | 0 | 0 | 1 | 0 |
| Sinn_2016 | 26 | 0 | 2 | 18 | 16 |
| **Total** | **553** | **10** | **165** | **288** | **264** |

KoAT2 or CoFloCo bound 305 programs. CrossCheck with ranges against them:

| | KoAT2 or CoFloCo: bound | no bound |
|---|---:|---:|
| CrossCheck (ranges): bound | 158 | 7 |
| no bound | 147 | 241 |

Reading the results:

- **As is**, CrossCheck bounds only the 10 programs whose loops have constant bounds:
  it has no symbolic bounds.
- **The 7 programs bounded only by CrossCheck.** Six (`CookSeeZuleger-TACAS2013-Fig1`,
  `Fig7a`, `Fig7b`, `Nyala-2lex`, `PastaC9`, `PodelskiRybalchenko-TACAS2011-Fig4`)
  assign a nondeterministic value to a variable inside the loop: they terminate, but
  their cost has no bound in terms of the inputs, so KoAT2 and CoFloCo are right to
  report none; CrossCheck bounds them only because the harness also restricts those
  values. The seventh, `Sinn_2016/CPU2006_ApplyBndRobin` (four nested loops), is
  bounded for the given ranges; KoAT2 and CoFloCo timed out on it.
- **History.** The first run of this comparison gave 141 programs in the ranged mode.
  Keeping the facts of each `break` path at a loop exit, joining intervals where paths
  merge, and recognising `x = x + 1` as an increment (for invariant candidates) added
  24 programs and lost none; all 24 are also bounded by KoAT2 or CoFloCo.
- **The 147 programs bounded by KoAT2 or CoFloCo and not by CrossCheck.** Almost all of
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
- KoAT2's classes for the 305 programs it or CoFloCo bounds are mostly `O(n)` and
  `O(n^2)`; for the 165 that CrossCheck bounds, KoAT2 gives `O(n)` for 109, `O(n^2)` for
  29 and `O(1)` for 18.

What this does not show: the bounded mode answers a different question (a bound for
inputs in a range), and the ranges also make the nondeterministic values bounded, which
the other tools do not assume. Stored: `results/koat2/`, `results/cofloco/` (one
`.tsv` per program, named after its path), `results/tpdb.json` (the script's output).
