# CrossCheck

[![Lean 4 CI](https://github.com/ldallolio/crosscheck/actions/workflows/lean_build.yml/badge.svg)](https://github.com/ldallolio/crosscheck/actions/workflows/lean_build.yml)
[![Clang plugin CI](https://github.com/ldallolio/crosscheck/actions/workflows/plugin_build.yml/badge.svg)](https://github.com/ldallolio/crosscheck/actions/workflows/plugin_build.yml)
[![Paper I DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24444576.svg)](https://doi.org/10.5281/zenodo.24444576)
[![Paper II DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24444646.svg)](https://doi.org/10.5281/zenodo.24444646)

CrossCheck derives upper bounds on the execution cost of imperative programs (loops, linear
and branching recursion) from ranking potentials, and lets a small checker, proved sound in
Lean 4, accept or reject each bound. It consists of:

- a **theory** with its **Lean 4 formalization**: execution traces and computation trees
  ordered by composition, loops and recursion as constrained optimization problems, a cost
  logic with procedures and assumed contracts, and a checker of cost certificates whose
  soundness is a Lean theorem (Paper I);
- a **Clang 18 plugin** (research prototype) that bounds the loops and recursion of C and C++
  functions without annotations where it can, enforces a real-time profile, and emits the
  certificates, flow facts for WCET tools and SARIF; evaluated on TACLeBench, TPDB and
  CMSIS-DSP and compared with other tools (Paper II);
- **cycle bounds of Cortex-M0 machine code** certified by the same checker, including loop
  bounds proved on the instructions themselves where a certificate is found (Paper III).

What is and is not proved, and what is trusted, is stated in each paper and in
`formalization/formalization.yaml`. The analyser itself is unverified; the cost bounds of
Papers I and II are in abstract units, not time.

## Papers

| | Source | Content | Preprint |
|---|---|---|---|
| I | `paper/theory/crosscheck-theory.tex` | theory, cost logic, certificate checker, Lean formalization | [doi:10.5281/zenodo.24444576](https://doi.org/10.5281/zenodo.24444576) |
| II | `paper/tool/crosscheck-tool.tex` | the Clang plugin, certificate generation, evaluation | [doi:10.5281/zenodo.24444646](https://doi.org/10.5281/zenodo.24444646) |
| III | `paper/binary/crosscheck-binary.tex` | certified cycle bounds of machine code, loop bounds included | not published |

Build Paper I first (Papers II and III refer to its numbered results), then II, then III;
`python3 paper/make_arxiv.py theory tool binary` makes self-contained source bundles.
How AI assistance was used is recorded in [`AI_USAGE.md`](AI_USAGE.md), following the AGMAI
recommendations on the release of AI-assisted mathematics.

## Repository

```text
crosscheck/
├── paper/                 # Papers I-III (LaTeX), shared bibliography, make_arxiv.py
├── formalization/         # Lean 4 + mathlib: 33 modules, no sorry, Lean's three standard axioms only
│   ├── ImperativeOptimization/   # traces, trees, loops, recursion, cost logic, checker,
│   │                             # mini-C validation, concurrency, stack, Cortex-M0 (Thumb*)
│   ├── CheckerMain.lean   # the checker program crosscheck-check
│   └── formalization.yaml # paper statement <-> Lean theorem map
├── clang-plugin/          # the Clang plugin and standalone tool (see its README)
├── frontends/rust/        # Rust front-end on rustc's MIR (translated to C)
├── benchmarks/            # example programs; tacle/, tpdb/, cmsis/ (Paper II);
│                          # cycles/ and hardware/ (Paper III)
├── docs/                  # guide, slides, certificate format, contracts, release record, qualification skeleton
└── AI_USAGE.md
```

## Building

Lean 4 (toolchain `leanprover/lean4:v4.16.0`, mathlib `v4.16.0`):

```bash
cd formalization
lake exe cache get
lake build
lake build crosscheck-check
```

Clang plugin (LLVM/Clang 18 development libraries, Z3, CMake, Ninja, GoogleTest, C++20):

```bash
cd clang-plugin
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release
ninja -C build
ctest --test-dir build --output-on-failure
```

See [`clang-plugin/README.md`](clang-plugin/README.md) for dependencies (including a
conda-based setup), options, the cost model and the limitations.

## Example

The plugin rejects the build if a function violates the real-time profile or its cost
bound exceeds its budget:

```cpp
#include <crosscheck/attributes.hpp>

CROSSCHECK_DEADLINE(500)   // budget in abstract cost units
int sum(const int* a, CROSSCHECK_RANGE(0, 64) int n) {
    int s = 0;
    for (int i = 0; i < n; ++i) s += a[i];   // bound 64 derived from the range
    return s;
}
```

```console
$ clang++ -std=c++20 -fplugin=clang-plugin/build/libCrossCheckPlugin.so -Iclang-plugin/include -c sum.cpp
sum.cpp:4:5: remark: crosscheck: 'sum': worst-case cost bound 453 units (deadline 500), under 1 assumption(s)
```

Worked examples (FIR filter, PID controller, CAN decoder, UART interrupt handler, CRC,
stepper ramp, recursive divide-and-conquer) are in [`benchmarks/`](benchmarks/README.md).

## Status and license

Research work. The Lean formalization is machine-checked; the Clang plugin, the
certificate generators and the binary analyses are research prototypes. Released under the
MIT license (`LICENSE`). Release v1.0 is archived at Zenodo
([doi:10.5281/zenodo.24425070](https://doi.org/10.5281/zenodo.24425070); all versions: [doi:10.5281/zenodo.24425069](https://doi.org/10.5281/zenodo.24425069)) and at
Software Heritage (`swh:1:rel:70c77563037e6db2a55b48b3ad4963c86a67773f`). To cite, see [`CITATION.cff`](CITATION.cff).
