# CrossCheck Clang plugin

A compile-time checker for real-time C++ code. For every annotated function it

1. enforces a **real-time profile** (no dynamic allocation, no exceptions, no
   virtual or indirect calls, no unbounded loop or recursion), and
2. derives a **worst-case cost bound** in abstract cost units, and compares it
   with a deadline if one is given.

A violation is a compile error. The bounds are computed without running or
unrolling the code: loops and recursion are bounded by affine *ranking
potentials* found by an SMT solver (Z3), and costs are combined with the
classical timing-schema rules (sequence = sum, branch = max, loop = bound × body).

> **Status: research prototype.** The cost unit is an abstract instruction
> count, not time (see [Cost model](#cost-model) and [Limitations](#limitations)).
> The analyser itself is not formally verified; what is machine-checked in Lean
> is the mathematics its certificates rely on (see [Soundness](#soundness)).

## Example

```cpp
#include <crosscheck/attributes.hpp>

CROSSCHECK_DEADLINE(500)
int sum(const int* a, CROSSCHECK_RANGE(0, 64) int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) s += a[i];
  return s;
}
```

```console
$ clang++ -std=c++20 -fplugin=libCrossCheckPlugin.so -Iclang-plugin/include -c sum.cpp
sum.cpp:4:5: remark: crosscheck: 'sum': worst-case cost bound 453 units (deadline 500), under 1 assumption(s)
```

Raise the range to `CROSSCHECK_RANGE(0, 100)` and the build fails:

```console
sum.cpp:4:5: error: crosscheck: worst-case cost bound 705 of 'sum' exceeds its deadline 500
```

More examples, taken from typical embedded code, are in
[`../benchmarks`](../benchmarks/README.md).

## Building

Requirements: LLVM/Clang 18 (development libraries), Z3 (C++ API), CMake ≥ 3.22,
Ninja, a C++20 compiler, GoogleTest (for the tests).

```bash
cd clang-plugin
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release
ninja -C build
ctest --test-dir build --output-on-failure
```

This produces `build/libCrossCheckPlugin.so` (the compiler plugin) and
`build/crosscheck-tool` (a standalone driver).

If the dependencies are not installed system-wide, a conda environment works:

```bash
conda create -n crosscheck -c conda-forge clangdev=18 llvmdev=18 clangxx=18 cmake ninja libz3 gtest
E=$CONDA_PREFIX/../envs/crosscheck     # or the path printed by conda
cmake -S . -B build -G Ninja -DCMAKE_PREFIX_PATH=$E \
      -DCMAKE_EXE_LINKER_FLAGS="-L$E/lib -Wl,-rpath,$E/lib" \
      -DCMAKE_MODULE_LINKER_FLAGS="-L$E/lib -Wl,-rpath,$E/lib"
```

If Clang must be pointed at a particular libstdc++ for the tests, pass for
instance `-DCROSSCHECK_CLANG_EXTRA_FLAGS=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13`.

## Usage

### As a compiler plugin

```bash
clang++ -fplugin=/path/to/libCrossCheckPlugin.so [plugin options] file.cpp
```

The plugin must be loaded by the same Clang major version it was built against.
Options are passed as `-fplugin-arg-crosscheck-<option>`:

| Option | Meaning |
|---|---|
| `report=FILE` | write a JSON report (bounds, loop potentials, assumptions, errors) |
| `all` | analyse every function defined in the main file, not only annotated ones |
| `weight-CLASS=N` | weight of an instruction class (see [Cost model](#cost-model)) |
| `max-paths=N` | symbolic paths kept through a loop body before joining (default 16) |
| `entry=NAME` | entry function for the report's in-context results (see [Calls](#how-bounds-are-derived)) |
| `certificates=FILE` | write a cost certificate for every analysed function in the certificate fragment; check them with `crosscheck-check` (see [Certificates](#certificates)) |
| `flowfacts=FILE` | write the derived loop bounds as flow facts for WCET tools (see [Flow facts, SARIF and CI](#flow-facts-sarif-and-ci)) |
| `flowfacts-format=ffx\|ais\|ais2` | FFX (OTAWA), AIS or AIS2 (aiT); default from the extension (`.ais`: AIS2, otherwise FFX) |
| `flowfacts-context=every-call\|program` | export the bounds valid for every call (default) or in the program's calling contexts |
| `sarif=FILE` | write a SARIF 2.1.0 log (errors, bounds, assumptions) |
| `sarif-base=DIR` | write file paths under `DIR` relative to it (`%SRCROOT%`), e.g. the repository root |

### As a standalone tool

```bash
crosscheck-tool [--summary] [--report=FILE] [--all] [--opt=weight-memory=3] file.cpp -- -std=c++20 -Iinclude
```

Exit status 0 if every analysed function is accepted, 1 otherwise.

## Annotations

All annotations are macros from `<crosscheck/attributes.hpp>`. They expand to
`[[clang::annotate]]` (or to an unevaluated `sizeof`) and have no run-time
effect; other compilers ignore them.

| Annotation | Where | Meaning | Trusted? |
|---|---|---|---|
| `CROSSCHECK_REALTIME` | function | enforce the profile, report a bound | – |
| `CROSSCHECK_DEADLINE(n)` | function | same, and reject if the bound exceeds `n` | – |
| `CROSSCHECK_RANGE(lo, hi)` | integer parameter | precondition `lo <= p <= hi` | proved at analysed call sites; assumed for external callers |
| `CROSSCHECK_REQUIRE(cond)` | first statements of a body | precondition relating parameters, e.g. `lo < hi` | as above |
| `CROSSCHECK_ASSUME(cond)` | statement | fact usable from this point on (e.g. after reading a register) | **yes** |
| `CROSSCHECK_LOOP_BOUND(n)` | first statement of a loop body | the loop runs at most `n` times | **yes**, unless a tighter bound is derived |
| `CROSSCHECK_BOUNDED(n)` | variable of a `for` init-statement | same | **yes**, unless a tighter bound is derived |
| `CROSSCHECK_COST(n)` | function declaration | cost of a function whose body is not analysed | **yes** |

Everything trusted is listed under `assumptions` in the report, so a reviewer
sees exactly what the bound depends on. Only conjunctions of linear integer
comparisons are used from `REQUIRE`/`ASSUME`; other conditions are ignored
(neither assumed nor checked).

## Real-time profile

Rejected inside an annotated function and in everything it calls:

- `new` / `delete`, `malloc`, `calloc`, `realloc`, `free`, `alloca`, … (placement `new` is allowed);
- `throw`, `try`/`catch`, `dynamic_cast`;
- virtual calls that cannot be devirtualised, calls through function pointers;
- `goto`, variable-length arrays, coroutines;
- local variables and temporaries with non-trivial destructors (hidden cost);
- loops and recursion for which no bound is derived or stated; mutual recursion;
- calls to functions with neither a body nor `CROSSCHECK_COST`.

Calls are followed into their definitions, including the standard library, so
`v.push_back(x)` is rejected because it reaches `operator new`. A violation found
inside a system header is reported once, at the call site in user code.

## Cost model

The cost of a path is a weighted count of abstract instructions; every weight
defaults to 1 and can be changed with `weight-CLASS=N`.

| Class | Counted for |
|---|---|
| `arith` | each arithmetic, bitwise, comparison or logical-negation operator |
| `assign` | each assignment, increment, initialisation of an integer variable |
| `memory` | each array subscript, pointer dereference, `->` |
| `call` | each call (the callee's bound is added) |
| `branch` | each evaluated `if`/loop/`switch`/`?:`/`&&`/`||` test, `break`, `continue` |
| `ret` | each `return` |
| `convert` | each integer ↔ floating-point conversion |

Reads of local variables, literals and `.` member accesses are free.
Composition rules:

| Construct | Bound |
|---|---|
| `A; B` | `cost(A) + cost(B)` |
| `if (c) A else B` | `cost(c) + max(cost(A), cost(B))` |
| `if (c) return x; rest` | `cost(c) + max(cost(return x), cost(rest))` |
| `switch` | test + sum of all cases (sound with fall-through) |
| loop with at most `K` iterations | `K · (test + body + step) + test` (+ one body if the loop can be left by `break`/`return`) |
| `do body while (c)` | `body + K · (test + body) + test`, `K` bounding the iterations after the first; the report's loop bound is `K + 1`, the number of executions of the body |
| function recursing with at most `N` activations | `N · (cost of one activation)` |

These are upper bounds, not exact counts: infeasible paths are not excluded and
nested loops are multiplied without amortisation.

## How bounds are derived

**State.** Each tracked local integer variable is mapped to an affine expression
over symbols; path conditions and invariants are linear constraints over the
same symbols. A local is tracked if its address is never taken and it is not
captured or bound to a reference. Everything else (globals, fields, memory,
results of calls) is an unknown value.

**Loops.** For each loop the analyser

1. replaces the variables modified in the loop by fresh symbols (the state at the
   loop head);
2. proposes simple invariants — a variable that is only incremented stays above
   its entry value, `a != b` with `a <= b` initially stays `a <= b` — and keeps
   those that Z3 proves inductive;
3. executes the guard and body symbolically, path by path (up to `max-paths`);
4. asks Z3 for `V(x) = w·x + c0` with, on every path, `V(x) − V(x') ≥ 1` and
   `V(x) ≥ 1`, and for the smallest `K` with `V(entry) ≤ K`. The universally
   quantified conditions are turned into linear constraints by Farkas' Lemma.
   The loop then runs at most `⌊K⌋` times.

After the loop, the state keeps what is known on each way out: through the guard,
the proved invariants and the negated guard; through a `break`, the facts of the
path that reaches it (each `break` path is one exit state). Where paths are joined,
a variable keeps the constant interval that holds on all of them.

**Calls.** While a call is evaluated, the analyser asks Z3 for the interval of
each integer argument in the current state, and joins these intervals over all the
states in which the call is evaluated (all paths, and the generic iteration of
every enclosing loop). The callee is then analysed with these intervals as facts
on its parameters — a *calling context* — in addition to its declared
preconditions, and that analysis gives the cost of the call. So
`sum(a, 8)` is bounded although `sum` alone, with an unconstrained `n`, is not.
Details:

- an argument contributes only if its expression already has the parameter's type
  (no conversion in between) and Z3's bounds are confirmed by an entailment check;
- a function that calls itself is never analysed in a context: the context holds
  for the first activation only;
- at most 8 contexts are analysed per function; further calls use the analysis
  without context;
- nothing is assumed: a context is proved at the call it is used for.

The report keeps both views of a function: `wcet` and the loops' `bound` hold for
*every* call that meets the declared preconditions; `wcet_in_context` and the
loops' `in_context` hold for the calls through which the entry functions reach it
(the function named by the option `entry=NAME`, or else every analysed function
that no analysed function calls), and `contexts` counts those analyses.

**Recursion.** Two certificates are tried and the better one is kept:

- a *depth potential* over the parameters, decreasing at every self-call, which
  bounds the depth `D`; with at most `b` self-calls per activation there are at
  most `1 + b + … + b^D` activations;
- a *size potential* `U` with `U(x) ≥ 1 + Σ U(args of the self-calls)` on every
  path, which bounds the number of activations by `U(x)` directly. This gives
  linear bounds for divide-and-conquer (`2·(hi − lo) − 1` activations for a
  recursive split of a range).

**Arithmetic.** Signed overflow is undefined behaviour and is assumed not to
happen. Unsigned arithmetic wraps: an unsigned result is used only if Z3 proves
it does not wrap, otherwise it becomes an unknown value. The limits of 32- and
64-bit types are never used as bounds.

## Soundness

What a bound means: *if* the assumptions listed in the report hold, the code has
no undefined behaviour, and the analyser is correct, then every execution of the
function performs at most the reported number of weighted abstract instructions.

The mathematical steps are machine-checked in Lean 4 (`../formalization`):

| Step in the analyser | Lean theorem |
|---|---|
| potential decreasing by ≥ 1 and ≥ 1 on each step ⇒ at most `⌊V⌋` steps (relational, rational-valued) | `ranking_bound_floor`, `ranking_bound_of_le` (`Certificate`) |
| the same when the conditions hold only under proved loop invariants and the facts of a calling context | `ranking_bound_floor_of_invariant`, `ranking_bound_of_context` (`Certificate`) |
| invariants hold at every loop head, hence at every exit (guard or `break`) | `run_invariant` (`Certificate`) |
| a bound proved under a context holds for every call whose arguments satisfy it | `call_bound_of_context` (`Certificate`) |
| Farkas multipliers imply the universally quantified condition | `farkas_sound_affine` (`Certificate`) |
| loop cost `K·(test + body) + test` | `while_cost_bound` (`Certificate`) |
| branch = max | `branch_supremum_bound`, `condTrace_cost_le` (`Dominance`) |
| depth `D`, branching `b` ⇒ at most `1 + b + … + b^D` activations | `callTree_size_le_geom`, `geom_closed` (`Arity`) |
| size potential ⇒ at most `⌊U⌋` activations | `callTree_size_le_potential` (`Arity`) |
| an accepted certificate (nodes `assign`, `havoc`, `seq`, `ite`, `while`, `whileAnd`, `weaken`, `dead`) ⇒ its bound holds for its program | `check_sound` (`Checker`) |

**Not verified:** the C++ implementation (the translation from the Clang AST to
constraints, the invariant generation, the cost counting) and Z3. The tests in
`tests/` include a set of loops that must be rejected, as regression tests for
soundness.

## Certificates

With `certificates=FILE` (tool: `--opt=certificates=FILE`) the plugin writes, for each
function in the fragment, a certificate in the format of
[`docs/certificate-format.md`](../docs/certificate-format.md): the function lowered to a
small integer program, annotated with assertions, loop invariants, potentials and
Farkas multipliers. The checker is compiled from its Lean definition:

```bash
(cd ../formalization && lake build crosscheck-check)
../formalization/.lake/build/bin/crosscheck-check --print FILE
```

An accepted certificate bounds every execution of its program
(`Checker.check_sound`): the bound then does not depend on this analyser or on Z3, only
on the checker and on the lowering from C++ to the certificate's program, which is not
verified. The report says, per function, `certificate: "emitted"` with the certified
bound, or why there is none. The ctest `certificates_accepted_by_lean_checker` runs this
on the example programs and on `tests/certificates/*.cpp` (early exits, `switch`, `&&`
tests, unsigned counters) when CMake is given `-DCROSSCHECK_CHECKER=<path>`.

The fragment covers assignments, conditionals, `for`/`while` loops (with `break`,
`continue` and `return` inside, and `&&` tests), `switch` (with fall-through), calls
to analysed functions (inlined in their calling context), and signed and unsigned
integer variables. Unsigned stores carry an explicit wrap-around test whose wrapping
branch the checker must prove dead. How each construct is lowered:
[`docs/certificate-format.md`](../docs/certificate-format.md).

## Flow facts, SARIF and CI

**Flow facts for WCET tools.** `flowfacts=FILE` writes the loop bounds the analysis
derived (not those stated by `CROSSCHECK_LOOP_BOUND`, which are assumptions):

| Format | Loop designated by | Bound | Sources |
|---|---|---|---|
| FFX (OTAWA, oRange) | `source` file and `line` of the loop keyword, at top level of `<flowfacts>` (every context) | `maxcount`: iterations per entry of the loop | Bonenfant et al., RTNS 2012; OTAWA's `flowfact_FlowFactLoader.cpp` |
| AIS (aiT) | `loop "R" + n loops max k;`: n-th loop of routine `R` (linker name) | `max k` | Heckmann & Ferdinand, AbsInt white paper |
| AIS2 (aiT) | `loop "R.Ln" { bound: 0 .. k; }` | `bound` | AbsInt release notes (a³ 15.10) |

The bound counts executions of the loop body per entry of the loop, the convention of
the report and of oRange's FFX output (on TACLeBench our in-context FFX values equal
oRange's on all 114 loops both bound: `benchmarks/tacle/compare_ffx.py`). Each file starts
with what the bounds hold for (every call, or the program's contexts with
`flowfacts-context=program`) and the analysis' assumptions. FFX elements carry extension
attributes (`crosscheck-function`, `crosscheck-potential`, `crosscheck-certified`), which
FFX readers ignore.

**Caveats.** aiT numbers the loops of a routine in the executable; we number them in
source order. They agree only if the compiler keeps the loops of a function in source
order and does not inline, unroll or split them: check against aiT's loop list. FFX source
locations are resolved by OTAWA through debug information (compile with `-g`), and OTAWA
warns and ignores a loop whose line has no code. Neither file has been loaded into OTAWA or
aiT here: they are checked against the formats' documentation and OTAWA's loader, and read
back by `tests/check_exports.py`. SWEET is not a target: it computes flow facts itself and
has no documented input format for loop bounds.

**SARIF.** `sarif=FILE` writes a SARIF 2.1.0 log for code-scanning interfaces: rule
`rejected` and `deadline` (errors, at the offending statement), `bound` (a note per
bounded function, with `wcet`, `wcetInContext`, `certificateBound` as properties) and
`assumption` (notes). The ctest `exports_read_back` validates it against the SARIF schema
when CMake is given `-DCROSSCHECK_SARIF_SCHEMA=<sarif-schema-2.1.0.json>` (CI does).

**Cost diff.** `scripts/cost_diff.py BASE HEAD` compares two sets of reports (files,
directories or snapshots) function by function and exits 1 when a function is newly
rejected or loses its bound, when a bound grows by more than `--max-increase PCT`
percent, or, with `--exact`, on any change; `--markdown FILE` writes a table for a
pull-request comment. `--snapshot` stores the compared fields only, without machine paths.
The ctest `bounds_equal_baseline` compares the example programs with
`benchmarks/bounds-baseline.json` (the figures of `tab:plugin`).

A GitHub Actions job for a project that uses the tool:

```yaml
- run: |
    for f in $(git ls-files 'src/*.c'); do
      crosscheck-tool --report=reports/$(basename $f).json --opt=sarif=sarif/$(basename $f).sarif \
        --opt=sarif-base=$PWD "$f" -- -Iinclude || true
    done
    python3 cost_diff.py baseline.json reports --max-increase 5 --markdown cost-diff.md
- uses: github/codeql-action/upload-sarif@v3   # needs permissions: security-events: write
  with: { sarif_file: sarif }
```

## Limitations

- **Cost is not time.** Turning the bound into a time bound needs per-instruction
  worst-case durations for the target, which depend on caches, pipelines and the
  compiler's code generation. The analysis works on the source AST, before
  optimisation.
- **Linear potentials only.** A loop or recursion that terminates by a
  logarithmic, lexicographic or non-linear argument gets a linear bound (binary
  search: depth `≤ n` instead of `log n`) or is rejected; state the bound with
  `CROSSCHECK_LOOP_BOUND`.
- **No amortisation.** Nested loops are multiplied; a recursive function is
  charged the worst-case cost of one activation for every activation (merge sort
  is bounded by `O(n²)`).
- **Calling contexts are intervals of integer arguments.** Relations between
  arguments, values of globals, and what a callee leaves in memory are not passed
  to the callee or back; recursive functions get no context. Bounds are numbers,
  not expressions in the parameters.
- **Integers only.** Loop counters that are pointers, iterators or floating-point
  values are not tracked; iterate by index or state the bound. Range-`for` is
  supported over C arrays and `std::array`.
- **Not supported:** `goto`, mutual recursion, concurrency, condition variables in
  `while`/`for`, `if consteval`.

## Source layout

```
include/crosscheck/attributes.hpp   annotations (the only file user code includes)
src/core/LinExpr.{hpp,cpp}          affine expressions, linear constraints
src/core/Cost.hpp                   saturating cost arithmetic, tree-size bound
src/core/Solver.{hpp,cpp}           Z3: entailment, ranking and size potentials (Farkas)
src/analysis/Analyzer.{hpp,cpp}     the AST walker: profile, cost, symbolic state
src/analysis/Consumer.{hpp,cpp}     Clang ASTConsumer shared by plugin and tool
src/analysis/Report.{hpp,cpp}       structured report and JSON output
src/analysis/Export.{hpp,cpp}       flow facts (FFX, AIS, AIS2) and SARIF, from a report
scripts/cost_diff.py                cost diff of two sets of reports (CI)
src/plugin/Plugin.cpp               plugin registration
src/tool/Main.cpp                   crosscheck-tool
tests/core_test.cpp                 solver and arithmetic (no Clang needed)
tests/analyzer_test.cpp             end-to-end tests on C++ snippets
tests/benchmarks_test.cpp           expectations on ../benchmarks
```

`src/core` does not depend on Clang, and `src/analysis` does not depend on how
the analysis is launched.
