# Plans and perspectives

Working notes on where CrossCheck stands against other tools and what to do next, kept by the
author and the assistant (re-introduced on 2026-11-28 at the author's request; the planning
documents of November 2026 were removed on 2026-11-22 and are in git history). This is a
planning document, not part of the papers or of the review record (`AI_USAGE.md` keeps no
list of open items). Each idea says what was measured and where the figures come from; update
or delete an entry when it is done or abandoned.

## Where CrossCheck stands (2026-11-28)

What no other tool gives: every bound comes with a certificate that a checker proved in Lean 4
accepts independently (source bounds, Cortex-M0 cycle bounds, loop bounds on the machine code).

| Benchmark | CrossCheck | Others | Source of the figures |
|---|---|---|---|
| TACLeBench loop bounds, 208 loops reached, in context | 142 bounded, 131 equal to the flow fact | oRange 131 / 127; LLVM ScalarEvolution 113 | `benchmarks/tacle/README.md`, Paper II `tab:tools` |
| TACLeBench functions with a bound (of 267) | 165 numeric | Infer 190 + 14 symbolic; KoAT2 119 + 23; CoFloCo 128 + 11 | same |
| TPDB `Complexity_C_Integer`, 553 programs | 11 as is; 249 with inputs in [-1000, 1000] (215 before the size bounds, 2026-11-28), 195 of them certified (166 before `whileSz` and `assume`); 147 certified for all inputs (`symbolic`) | KoAT2 288; CoFloCo 264 | `benchmarks/tpdb/README.md` |
| Cortex-M0 cycle bounds of the kernels | certified, every bound checked against emulated runs | OTAWA on the same flow facts | `benchmarks/cycles/README.md`, Paper III |
| Processors with caches and pipelines | Cortex-M0 model only; Cortex-M4/M7 through OTAWA, uncertified | aiT, OTAWA | — |

## Next: the TPDB gap (chosen 2026-11-28)

The programs bounded by KoAT2 or CoFloCo and not by CrossCheck with input ranges: 107 on
2026-11-28, **75 since the size bounds** (19 the other way). Their answers are stored
(`benchmarks/tpdb/results/`); `run_tpdb.py --jobs 30` reruns all modes in under a minute on
a 40-core machine, so every change can be measured.

Done (2026-11-28):

1. **Classified** the 107 by the analyser's diagnostics and by reading the sources: in 58 a
   variable of a loop test had no range where the loop starts, in 42 a loop had bounded
   variables and no potential, 7 other.
2. **Size bounds** (KoAT's, Brockschmidt et al., TOPLAS 2016, Section 4.2; read): a loop
   with at most k complete iterations, each changing v by an amount in [l, h], changes v by
   an amount in [k·min(0, l), k·max(0, h)]. In the analyser at the exits (16 programs) and, over
   a ghost count n <= k from a trial run of the body, at the head of a loop with a loop in its
   body (18 more): 215 -> 249, none lost; TACLeBench kernels and parallel category
   unchanged, larger programs 330 -> 333 loops bounded in context. Lean: `size_bound`, `size_bound_of_le` (`Certificate`). Tests: `SizeBounds.*`,
   `Unsound.SizeBound*`.

Open, by expected effect:

- **Certify the size bounds** (7 of the 34 new programs are certified, by other means).
  Done on 2026-11-28 (the author asked for the Paper I route): checker node `whileSz`
  (size facts `f <= U` on entry, growth `<= h` per iteration proved with one ghost logical
  variable per fact, `f <= U + max(h,0)(N-1)` in the body, `f <= U + max(h,0)N` after,
  `N = floor(k/d)`, constant `k`), Lean `sizeloop_sound` and the general rule
  `valid_whileSize`, Paper I `prop:size-facts`. The generator emits `whileSz` from the
  analyser's per-iteration changes (`LoopPotential::sizes`), only in a second attempt at a
  function whose certificate failed (`preferSize`), so other certificates are unchanged;
  example `clang-plugin/tests/certificates/sizes.cpp` (after a loop, inside a loop).
- **The 38 with no potential**: disequalities and disjunctions in guards (`wise`:
  `x - y > 2 || y - x > 2`), loops in phases or that change direction (`GopanReps`),
  counters that are reset (`speedpldi2`). Multiphase / disjunctive potentials: read
  the prior work first (Ben-Amram and Genaim on multiphase ranking functions; Gulwani et al.,
  SPEED) before any Paper I result.
- **The 29 still without a range**: exponential growth in an earlier loop (8: `size14`
  `b = b*b`, sums of variables; KoAT's "scaled sums"), relations between two variables
  (`end <= i`: `Loopus2015_big`, `CPU2006_XNU`), an inner loop's effect on a value that the
  outer loop resets (`perfect`, `Nested`), amortisation (`Loopus2014_ex1`), an `unsigned`
  parameter without a range in the harness (`CPU2006_SingleLinkCluster`).
- **How to report bounds in the parameters** (unchanged): the comparison "as is" (11
  programs) is unfair; complexity tools give bounds in the parameters, CrossCheck numeric
  bounds with ranges and symbolic ones only as certificates (`symbolic`, 147). Decide how to
  report them before comparing again.
- The trial run costs time on deep nests: `cjpeg_transupp` 197 s -> 278 s (TACLeBench
  sequential category).

Rules that stay: never make the checker accept more without a Lean proof (three standard
axioms); figures in papers and READMEs from the scripts' output; a new loop feature needs a
must-be-rejected test.

## Other directions, by expected effect on the comparisons

- **Across calls** (Infer bounds 25 more TACLeBench functions): summaries in the parameters.
- **Machine code**: 278 of 403 kernel loops certified (Clang, both assumptions); the others are
  grouped by `benchmarks/cycles/classify_loops.py` (exit on a value returned by a call 22, on
  data loaded from memory 16, a counter against a parameter 20, ...).
- **aiT**: a direct comparison needs a licence (academic licences have existed; the author's
  request to make).
- **Hardware**: `benchmarks/hardware/hw.py` on an STM32F0 board when it arrives (timing of the
  emulator and certified bounds against the board).

## Packaging (deferred by the author on 2026-11-28)

Goal: redistribution in distributions and integration in compilers and linkers. Done:
install rules and `--version` for the plugin (`166fb19`); the checker without `Lean.*`
(`JsonCore`, `e8ccebc`: 6.5 MB instead of 124 MB, 5 ms instead of 54 ms per run).

1. The checker without a Lean toolchain: ship its Lean-generated C (about 118,000 lines,
   `formalization/.lake/build/ir`) and Lean's runtime sources (Apache-2.0) with a CMake build,
   and a C interface (`@[export]`, e.g. `check_certificate(const char *json)`) for in-process
   use. The Lean sources stay the preferred form for modification.
2. The IPET cycle-certificate producer (`m0.py`, `wcet.py`, `ipet.py`, about 2,000 lines)
   ported to C++ with HiGHS's C++ API (MIT; untrusted: it only proposes multipliers);
   byte-identical certificates on TACLeBench required.
3. `binloops.py` (3,800 lines) ported the same way.

Integration model: the producer inside the compiler or linker (C++, Z3 and HiGHS optional)
emits certificates; the checker stays small and independent (like `llvm-objdump` beside the
compiler).

## Measured and set aside

- **Finer frame model** (2026-11-27): an address of the frame allowed in any register used
  only as a load base: +1 loop on the Clang kernels, 0 on GCC and on the larger programs; the
  loops that forcing `--frame` gained are in functions that do write their frame through other
  registers (`benchmarks/cycles/README.md`). Revisit only with a points-to model of the frame.
