# CrossCheck

[![Lean 4 CI](https://github.com/ldallolio/crosscheck/actions/workflows/lean_build.yml/badge.svg)](https://github.com/ldallolio/crosscheck/actions/workflows/lean_build.yml)
[![Clang plugin CI](https://github.com/ldallolio/crosscheck/actions/workflows/plugin_build.yml/badge.svg)](https://github.com/ldallolio/crosscheck/actions/workflows/plugin_build.yml)

**CrossCheck** is a dual-layer semantic framework for formal verification, optimization, and compile-time constraint enforcement for imperative programs. By bridging **intensional execution traces** (operational semantics and cost models) with **extensional state equations** (algebraic valuation models), CrossCheck enables verified static analysis, bounded execution checks, and real-time profile enforcement.

---

## Architecture Overview

CrossCheck operates across two distinct semantic layers:

1. **Intensional Domain (Operational Traces & Cost Models)**
   * Extracts program execution paths into formal instruction traces ($\Sigma^*$) and computation trees ($\mathcal{T}_\Sigma$).
   * Captures fine-grained resource metrics, worst-case execution time (WCET), memory allocations, and recursion profiles.
   * Formalizes a strict partial order *order-by-composition* ($\sqsubseteq$) over trace monoids and operadic tree algebras.

2. **Extensional Domain (State Valuation & Algebraic Constraints)**
   * Maps operational control-flow structures into closed-form systems of state equations.
   * Leverages an SMT solver (Z3) to prove bounds, state invariants, and termination properties at compile time.

---

## Project Structure

```text
crosscheck/
├── paper/                       # Research paper source files (LaTeX)
│   ├── theory/crosscheck-theory.tex   # Paper I: theory and Lean
│   ├── tool/crosscheck-tool.tex       # Paper II: the plugin and its evaluation
│   └── crosscheck.bib
├── formalization/               # Lean 4 machine-checked proofs
│   ├── lakefile.lean
│   ├── lean-toolchain
│   ├── formalization.yaml       # Paper statement <-> Lean theorem map
│   ├── ImperativeOptimization.lean
│   ├── ImperativeOptimization/
│   │   ├── State.lean           # Pointed state spaces & transitions
│   │   ├── Trace.lean           # Trace monoid, prefix/subsequence orders, cost, minimal exiting trace
│   │   ├── Tree.lean            # Computation trees, grafting, tree prefix order, tree powers
│   │   ├── Dominance.lean       # Asymptotic dominance, tropical branch collapsing
│   │   ├── FixedPoint.lean      # Trace valuation homomorphism
│   │   ├── OperationalSemantics.lean # Recurrence systems, minimal iteration
│   │   ├── WhileLoop.lean       # Big-step loop semantics = trace minimisation
│   │   ├── Ranking.lean         # Ranking potentials, termination, WCET envelopes
│   │   ├── Recursion.lean       # Linear & branching recursion = trace/tree minimisation
│   │   ├── Certificate.lean     # Soundness of the plugin's certificates (ranking, Farkas, loop cost)
│   │   ├── Arity.lean           # Call trees of arbitrary arity: depth and size-potential bounds
│   │   ├── Language.lean        # Cost logic for a small language with procedures; soundness
│   │   ├── CheckerCore.lean     # The certificate checker (no mathlib, compiled into crosscheck-check)
│   │   ├── Checker.lean         # Its soundness: check_sound, program_sound
│   │   ├── MiniCCore.lean, MiniC.lean   # Mini-C and validation of certificates against the source
│   │   ├── ResponseCore.lean, Interrupts.lean, ForkJoin.lean   # Response times, greedy scheduling
│   │   ├── Stack.lean           # Stack depth as a high-water mark
│   │   └── Examples.lean        # Machine-checked proofs of paper examples
│   ├── CheckerMain.lean         # The checker program (reads certificate files)
│   └── test/                    # Certificate files, mutation test, interpreter of certificates
├── AI_USAGE.md                  # Record of AI assistance (AGMAI guidelines)
├── clang-plugin/                # Clang plugin: real-time profile + cost bounds (see its README)
│   ├── CMakeLists.txt
│   ├── include/crosscheck/attributes.hpp   # source annotations
│   ├── src/core/                # affine expressions, Z3 back-end (Farkas), certificates
│   ├── src/analysis/            # AST walker: profile, cost, symbolic state, certificates, mini-C export
│   ├── src/plugin/, src/tool/   # compiler plugin and standalone driver
│   ├── scripts/                 # cost diff for CI, whole-project driver, ACSL export
│   └── tests/                   # GoogleTest / CTest suite, random-program test
├── frontends/rust/              # Rust front-end on rustc's MIR (translated to C)
├── benchmarks/                  # Annotated real-time example programs
│   ├── tacle/                   # TACLeBench: loop bounds vs. flow facts, observed counts, other tools
│   ├── tpdb/                    # TPDB complexity programs: comparison with KoAT2 and CoFloCo
│   ├── cmsis/                   # CMSIS-DSP: coverage of an embedded library
│   └── cycles/                  # Cortex-M0: cycle and stack bounds checked against emulated runs
├── docs/
│   ├── guide/                   # Companion guide: concepts, papers, plugin, Lean, bibliography, Q&A
│   ├── certificate-format.md, contracts.md, implementation-plan.md, proposals.md
│   └── qualification/           # Requirements of the checker with their evidence (skeleton)
├── references/                  # What was read of each cited paper (no PDFs in the repository)
└── README.md

````

-----

## Prerequisites

### 1\. Formal Proofs (Lean 4)

  * **Lean 4 Toolchain Manager (`elan`)**: Install via `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh`
  * **Build Tool (`lake`)**: Bundled with Lean 4.

### 2\. Compiler & Verification Engine (C++)

  * **LLVM / Clang**: Version 18+ development libraries.
  * **Build System**: CMake 3.22+, Ninja.
  * **SMT Solver**: Z3 C++ API bindings.
  * **C++ Standard**: C++20 compatible toolchain.

-----

## Quick Start

### Building the Lean 4 Formalization

``` bash
cd formalization
lake exe cache get
lake build

```

### Building the Clang Plugin & Test Suite

``` bash
cd clang-plugin
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release
ninja -C build
ctest --test-dir build --output-on-failure

```

See [`clang-plugin/README.md`](clang-plugin/README.md) for dependencies (including a
conda-based setup), options, the cost model and the limitations.

-----

## Usage Example

Annotate real-time functions; the plugin rejects the build if the real-time profile is
violated or the worst-case cost bound exceeds the deadline:

``` cpp
#include <crosscheck/attributes.hpp>

CROSSCHECK_DEADLINE(500)   // budget in abstract cost units
int sum(const int* a, CROSSCHECK_RANGE(0, 64) int n) {
    int s = 0;
    for (int i = 0; i < n; ++i) s += a[i];   // bound 64 derived from the range
    return s;
}

```

``` console
$ clang++ -std=c++20 -fplugin=clang-plugin/build/libCrossCheckPlugin.so -Iclang-plugin/include -c sum.cpp
sum.cpp:4:5: remark: crosscheck: 'sum': worst-case cost bound 453 units (deadline 500), under 1 assumption(s)

```

Worked examples (FIR filter, PID controller, CAN decoder, UART interrupt handler, CRC,
stepper ramp, recursive divide-and-conquer) are in [`benchmarks/`](benchmarks/README.md).

-----

## Development Status & License

  * **Current Status**: Active research. The Lean formalization is machine-checked; the Clang plugin is a research prototype (cost bounds are abstract operation counts, not timing guarantees).
  * **License**: Open-source release planned upon completion of compiler tooling.

<!-- end list -->

