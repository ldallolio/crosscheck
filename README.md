# CrossCheck

[![Lean 4 CI](https://github.com/ldallolio/crosscheck/actions/workflows/lean_build.yml/badge.svg)](https://github.com/ldallolio/crosscheck/actions/workflows/lean_build.yml)

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
   * Leverages SMT solvers (Z3/CVC5) to prove bounds, state invariants, and termination properties at compile time.

---

## Project Structure

```text
crosscheck/
├── paper/                       # Research paper source files (LaTeX)
│   └── main.tex
├── formalization/               # Lean 4 machine-checked proofs
│   ├── lakefile.lean
│   ├── lean-toolchain
│   ├── ImperativeOptimization.lean
│   └── ImperativeOptimization/
│       ├── State.lean           # Pointed state spaces & transitions (Def 1)
│       ├── Trace.lean           # Trace monoids, prefix order & Thm 1
│       ├── Tree.lean            # Computation trees, operadic grafting & cost envelopes
│       ├── FixedPoint.lean      # Trace evaluation & extensional soundness (Thms 2-3)
│       ├── OperationalSemantics.lean # Recurrence system reduction
│       └── Examples.lean        # Machine-checked proofs of paper examples
├── clang-plugin/                # C++ Clang/LLVM AST matchers & SMT generator
│   ├── CMakeLists.txt
│   ├── include/
│   ├── src/
│   └── tests/                   # GoogleTest / CTest suite
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
  * **C++ Standard**: C++20 / C++26 compatible toolchain.

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
mkdir build && cd build
cmake -G Ninja -DCMAKE_BUILD_TYPE=Release ..
ninja
ctest --output-on-failure

```

-----

## Usage Example

Annotate critical function scopes or loops in C++ using custom attributes to enforce execution constraints:

``` cpp
#include <crosscheck/attributes.hpp>

[[crosscheck::enforce(realtime)]]
void process_telemetry(const SensorData& input) {
    // CrossCheck verifies bounded loop iterations and zero dynamic memory allocation
    for ([[crosscheck::bounded(128)]] std::size_t i = 0; i < input.size(); ++i) {
        // Core execution loop
    }
}

```

-----

## Development Status & License

  * **Current Status**: Active research & machine-checked formalization.
  * **License**: Open-source release planned upon completion of compiler tooling.

<!-- end list -->

