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
| TPDB `Complexity_C_Integer`, 553 programs | 11 as is; 215 with inputs in [-1000, 1000] | KoAT2 288; CoFloCo 264 | `benchmarks/tpdb/README.md` |
| Cortex-M0 cycle bounds of the kernels | certified, every bound checked against emulated runs | OTAWA on the same flow facts | `benchmarks/cycles/README.md`, Paper III |
| Processors with caches and pipelines | Cortex-M0 model only; Cortex-M4/M7 through OTAWA, uncertified | aiT, OTAWA | — |

## Next: the TPDB gap (chosen 2026-11-28)

107 TPDB programs are bounded by KoAT2 or CoFloCo and not by CrossCheck with input ranges (17
the other way). Their answers are stored (`benchmarks/tpdb/results/`), so every change can be
measured without running them again. Plan:

1. Classify the 107 by cause, from CrossCheck's own diagnostics (report `errors`, the loop
   that has no bound) and by reading the programs: multi-phase or lexicographic loops,
   non-linear guards, bounds that need the parameters symbolically, nested loops whose inner
   bound depends on the outer counter, recursion, other.
2. Pick the cause that is both frequent and scientifically interesting (a result that belongs
   in Paper I, with a Lean theorem and a checker case, not a special case), and check prior
   work on it first (`check-prior-work`: read and cite where the idea was introduced).
3. The comparison "as is" (11 programs) is unfair: complexity tools give bounds in the
   parameters, CrossCheck gives numeric bounds only with ranges and symbolic ones only as
   certificates (option `symbolic`). Decide how to report bounds in the parameters before
   comparing again.

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
