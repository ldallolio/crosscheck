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
| `report=FILE` | write a JSON report (bounds, loop potentials, assumptions, errors; each loop's first and last source line, `line` and `end_line`, used to match the binary's loops) |
| `all` | analyse every function defined in the main file, not only annotated ones |
| `weight-CLASS=N` | weight of an instruction class (see [Cost model](#cost-model)) |
| `max-paths=N` | symbolic paths kept through a loop body before joining (default 16) |
| `entry=NAME` | entry function for the report's in-context results (see [Calls](#how-bounds-are-derived)) |
| `certificates=FILE` | write a cost certificate for every analysed function in the certificate fragment; check them with `crosscheck-check` (see [Certificates](#certificates)) |
| `interrupt-overhead=N` | cost of entering and leaving an interrupt handler, added per activation (assumption) |
| `minic` | with `certificates`: also export each certified function as mini-C, which the checker validates against the certificate (see [Validation against the source](#validation-against-the-source-minic)) |
| `budget=N` | search budget per function, in solver work (constraints sent to the solver; default 500000, `0`: none). Once spent, the optional searches stop (the retry with more candidate invariants, the certificate candidates in the enclosing potentials and the amortised nests) and the refinement of candidate invariants stops after two rounds, dropping a set that is not yet inductive. Never unsound, only less precise; the report says so (`search_budget_exhausted`, with `solver_work`). Counted in work, not seconds, so that results do not depend on the machine; for the same reason each Z3 query is limited by Z3's resource counter (`rlimit`, 50 million units; an exhausted query counts as not proved), with a 10 s timeout only as a backstop (some Z3 versions, such as Ubuntu 24.04's 4.8.12, do not stop every query by the counter): the report's `solver_timeouts` counts the queries it stopped, whose answers may depend on the machine (0 on every function of the TACLeBench kernels with Z3 5.1.0 and with 4.8.12, which give the same bounds); `CROSSCHECK_Z3_DUMP=DIR` writes those queries to DIR |
| `input-range=LO,HI` | assume every integer input without a declared range in `[LO,HI]` (unsigned) or `[-HI,HI]` (signed); listed as an assumption |
| `contracts=FILE` | library contracts: trusted costs linear in the arguments (see [`docs/contracts.md`](../docs/contracts.md)) |
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
| `CROSSCHECK_DEADLINE_CYCLES(n)`, `CROSSCHECK_DEADLINE_US(n)` | function | same, and a time budget, recorded in the report and checked after compilation on the binary ([Time budgets](#time-budgets-checked-after-compilation)) | the processor model (see there) |
| `CROSSCHECK_RANGE(lo, hi)` | integer parameter | precondition `lo <= p <= hi` | proved at analysed call sites; assumed for external callers |
| `CROSSCHECK_REQUIRE(cond)` | first statements of a body | precondition relating parameters, e.g. `lo < hi` | as above |
| `CROSSCHECK_ASSUME(cond)` | statement | fact usable from this point on (e.g. after reading a register) | **yes** |
| `CROSSCHECK_LOOP_BOUND(n)` | first statement of a loop body | the loop runs at most `n` times | **yes**, unless a tighter bound is derived |
| `CROSSCHECK_BOUNDED(n)` | variable of a `for` init-statement | same | **yes**, unless a tighter bound is derived |
| `CROSSCHECK_COST(n)` | function declaration | cost of a function whose body is not analysed | **yes** |
| `CROSSCHECK_INTERRUPT(T)` | function | interrupt handler, activated at most once every `T` units; other functions get a response time (see [Interrupts](#interrupts)) | **yes** (`T`) |

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
nested loops are multiplied without amortisation. The certificate (not the report's
`wcet`) of a triangular nest, whose inner loop runs from the outer counter to a constant
limit or from `0` to the outer counter, carries the amortised bound instead (the sum over
the outer iterations, about half the product; Lean `triOk`, `triloop_sound`, and node
`whileUp`, `uploop_sound`); the report's `certificate_bound` shows it.

## How bounds are derived

**State.** Each tracked integer variable is mapped to an affine expression
over symbols; path conditions and invariants are linear constraints over the
same symbols. A local is tracked if its address is never taken and it is not
captured or bound to a reference. Memory and results of calls are unknown values,
except for the following, each with the assumption it needs listed in the report:

| Value | How | Assumption (listed) |
|---|---|---|
| global or `static` variable (non-`volatile`, non-`const`, address never taken in the translation unit) | tracked; unknown at entry; after a call, the globals the callee may write (transitively) become unknown, also inside loops | not modified by interrupts, other threads, functions without an analysed body or inline assembly while the function runs |
| field `p->f` read through a pointer parameter, if the function neither writes `p->f` nor changes `p` | one symbol: its value at entry | not modified while the function runs (aliasing pointers, callees, inline assembly, interrupts) |
| `tab[i]` from a `const` integer array with a constant initializer | an unknown value in [min, max] of the entries | none (an out-of-bounds read is undefined behaviour, like signed overflow) |
| `y >> k`, `y / c`, `y % c`, `y & m` with constants | facts `c·q ≤ y ≤ c·q + c − 1` etc., when `y ≥ 0` is proved | none |
| `while (--j)`, `if (x)` | tests `!= 0` (also in C, where they have no conversion to `bool`) | none |

The option `input-range=LO,HI` assumes every integer input without a declared range
(parameters and such fields) in `[LO, HI]` (unsigned) or `[-HI, HI]` (signed): a harness
for libraries whose sizes are parameters (CMSIS-DSP, `benchmarks/cmsis`); the
assumption names the inputs. Target intrinsics (`__builtin_arm_*`, behind the CMSIS
intrinsics) cost one arithmetic unit, straight-line GNU statement expressions `({ ... })`
are evaluated, and inline assembly costs one arithmetic unit per instruction of its
template (an assumption); `asm goto` is rejected. The annotations work in C and in C++
(`CROSSCHECK_*` expand to `__attribute__((annotate))` in C).

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
| an accepted certificate (nodes `assign`, `havoc`, `seq`, `ite`, `while`, `whileAnd`, `weaken`, `dead`, `call`; symbolic bounds) ⇒ its bound holds for its program, given its callees' specifications | `check_sound` (`Checker`) |
| an accepted program certificate ⇒ every function meets its summary, relative to the assumed contracts | `program_sound` (`Checker`) |
| logarithmic loops (`x >>= k`, `x /= c`: `b·v' ≤ v`, `v ≥ 1`): at most `⌊log_b K⌋ + 1` iterations, certified by `whileLog` | `log_ranking_bound` (`Certificate`), `logloop_sound` (`Checker`) |
| triangular nests (the inner loop's entry bound is the outer potential `γⱼ`, so the outer body costs `a + c·γⱼ`): the sum over the outer iterations, about half the product, certified by `while`/`whileAnd` in the amortised form (`triOk`) | `valid_whileSum` (`Language`), `triloop_sound` (`Checker`) |
| triangular nests with increasing cost (an inner loop from `0` to the outer counter: in the outer body `γⱼ = k − pot`, what the outer potential has lost, so the outer body costs `a + c·γⱼ`): the sum over the outer iterations, certified by `whileUp` | `valid_whileMono` (`Language`), `uploop_sound` (`Checker`) |
| growing loops (`len <<= 1`: `v ≥ 1` on entry, `v' ≥ b·v`, `v ≤ K` under the test): at most `⌊log_b K⌋ + 1` iterations, certified by `whileGrow` | `growloop_sound` (`Checker`) |
| a certificate validated against the function's mini-C source (`minic`) ⇒ its bound holds for the source program | `validated_sound`, `nf_equiv` (`MiniC`) |
| response time under sporadic interrupt handlers | `response_time_bound`, `rtaHolds_sound` (`Interrupts`) |

**Not verified:** the C++ implementation (the translation from the Clang AST to
constraints, the invariant generation, the cost counting) and Z3; for a certificate, the
lowering of C to the certificate's program, or, for a validated certificate, the export of
C as mini-C. The tests in
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

The certificate file holds one *program certificate* per translation unit: every
certified function has a bound in its parameters (`certificate_summary` in the report,
e.g. `5 + 7*max(0,n)`), and a call of a function certified before it is checked against
that summary instead of inlining the callee; functions with a trusted cost
(`CROSSCHECK_COST`, contract files) are assumed contracts, printed `ASSUMED` by the checker.

The fragment covers assignments, conditionals, `for`/`while` loops (with `break`,
`continue` and `return` inside, and `&&` tests), `switch` (with fall-through), calls
(as summaries, or inlined in their calling context), contracts, and signed and unsigned
integer variables. Unsigned stores carry an explicit wrap-around test whose wrapping
branch the checker must prove dead. How each construct is lowered:
[`docs/certificate-format.md`](../docs/certificate-format.md).

### Validation against the source (`minic`)

With `--opt=minic` as well, each certified function is also exported as a *mini-C*
program (`src/analysis/MiniC.cpp`), written from the C syntax alone: it does not use the
certificate generator or any analysis result, only the variable numbering and the cost
model. The checker lowers it with the Lean definition of mini-C and compares it with the
certificate's program (without annotations); it prints `VALIDATED f` when they agree.
Then the bound holds for the mini-C program (`MiniC.validated_sound`): the generator is
no longer trusted, the exporter is. The exporter is short and meant to be read: reads of
untracked variables and of memory are unknown values, writes to them only cost, signed
arithmetic is exact (no overflow, an assumption), tracked globals are ordinary variables
(assumed: nothing else writes them during the function), `break`, `continue`, `return`,
`switch` and `do` are written as they are (`"jsource"`) and eliminated by the checker
(`MiniC.elim`, proved by `MiniC.validatedJ_sound`), and it refuses what it cannot model:
calls in tests, `goto`, static locals, narrow unsigned or address-taken tracked variables,
and table reads. The ctest
`minic_sources_validated` runs `tests/c/minic.c`: functions `ok_*` must be validated, no
function `no_*` may be. The list of what is refused is in
[`docs/certificate-format.md`](../docs/certificate-format.md#mini-c-sources-validation-against-the-source).

## Interrupts

Handlers annotated `CROSSCHECK_INTERRUPT(T)` are analysed like real-time functions. Every
other bounded function then gets `response_time` in the report: the least `R` with
`C + Σₖ (cₖ + o)·⌈R/Tₖ⌉ ≤ R`, where `C` is its bound (in context if known), `cₖ` the
handlers' bounds and `o` the `interrupt-overhead` (Lean `Interrupts.response_time_bound`,
Paper I `thm:response-time`). A `CROSSCHECK_DEADLINE` is checked against the response time.
With certificates, when the function and all handlers have constant certified bounds, the
certificate file contains a response-time claim with those bounds, and `crosscheck-check`
prints `RESPONSE … completes within R` (`Interrupts.rtaHolds_sound`). Assumptions, listed
in the report: the `T`s, the overhead, no activation pending when the function starts, one
cost unit = one time unit (true only for a timing cost model of the target), and that
handlers do not write variables the function's bounds depend on. Example:
`tests/certificates/interrupts.cpp`. Fork-join is not supported by the plugin (only its
theory, `ForkJoin.lean`).

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

## Time budgets, checked after compilation

The cost bounds are in abstract units; a time budget belongs to the binary on a
processor. `CROSSCHECK_DEADLINE_CYCLES(n)` and `CROSSCHECK_DEADLINE_US(n)` put a function
under the real-time profile and record the budget in the report (`deadline_cycles`,
`deadline_us`); the plugin does not check them. `scripts/crosscheck_link.py` checks them
on the compiled code, from the plugin's loop bounds and a processor model:

```bash
crosscheck-tool --all --report=r.json prog.c -- -Iinclude ...
clang --target=thumbv6m-none-eabi -mcpu=cortex-m0 -O1 -g -c prog.c -o prog.o
python3 scripts/crosscheck_link.py --report r.json --binary prog.o --source prog.c --clock-mhz 48
```
```
ok    ok_sum: bound 462 cycles = 9.625 us, budget 5000 cycles
FAIL  no_too_slow: bound 462 cycles = 9.625 us, budget 1 us  [FAIL: budget exceeded]
```

The exit status is 1 if a budget is exceeded or a function with a budget has no cycle
bound, so the check can run as a post-build step, e.g. in CMake (one `--report`/`--source`
pair per translation unit, the binary being the linked program):

```cmake
add_custom_command(TARGET firmware POST_BUILD
  COMMAND python3 ${CROSSCHECK}/clang-plugin/scripts/crosscheck_link.py
          --report ${CMAKE_BINARY_DIR}/control.json --source ${CMAKE_SOURCE_DIR}/src/control.c
          --report ${CMAKE_BINARY_DIR}/filters.json --source ${CMAKE_SOURCE_DIR}/src/filters.c
          --binary $<TARGET_FILE:firmware> --clock-mhz 48)
```

**Whole programs.** The binary may be an object file or a linked executable, and contain
the code of several source files: a call is costed from the callee's code in the binary,
whatever file it comes from, with the loop bounds of that file's report (the debug lines
tell the files apart; two sources with the same file name are refused). Test: a program of
two files (`tests/c/time_budget_lib.c`, `time_budget_main.c`) linked at the addresses of a
microcontroller.

**Processors** (`--processor`):

| Processor | Timing model | Binary |
|---|---|---|
| `cortex-m0` (default) | `benchmarks/cycles`: `m0.py` (timing table of the Arm manual), `wcet.py` (binary loops matched with source loops through the debug lines, timing schema on the binary); checked against emulated runs by `run_cycles.py` | object, or executable with its code below 0x20000000 |
| `stm32f4` (Cortex-M4) | OTAWA, script `stm32` (`ARCH=0`): pipeline, no cache, memory latencies of OTAWA's model (its file says they are not from the datasheet) | executable linked at the board's addresses (flash from 0x08000000) |
| `stm32h7` (Cortex-M7) | OTAWA, script `stm32` (`ARCH=1`): pipeline, caches, branch history table | same |

For the OTAWA processors (`benchmarks/cycles/otawa_flow.py`), OTAWA runs in the Docker
image `--otawa-image` (default `otawa:dev`, built by the user; not distributed here)
without network; the loops of OTAWA's own control-flow graphs are matched with the source
loops through the debug lines and the bounds are given to it as flow facts (`maxcount` =
bound + 1, by function label and offset); OTAWA computes the WCET by IPET. A function gets
no bound if it reaches a loop without a matched bound, recursion, an indirect call or jump,
a jump table, a branch into another function, or code of an undefined symbol (an
executable with undefined symbols is refused). The STM32 bounds are not checked against
executions here (no simulator of these processors); the same matching on Cortex-M0
binaries is (`run_otawa.py --matching otawa --check`).

What is trusted is printed with the results: the timing model (for the Cortex-M0:
zero-wait-state memory), no interrupt during the function, that the compiler preserves
the source loops' iteration counts, and the plugin's loop bounds (for every call; with
`--context`, those of the calling contexts of the analysed program).

**Certified cycle bounds** (`--certify`, Cortex-M0): the bound is then the IPET bound of
the function's machine code with a certificate (`benchmarks/cycles/ipet.py`: the code,
the instruction addresses, one row per matched loop, an LP solver for the dual
multipliers; needs scipy) that the verified checker `crosscheck-check` must accept
(`--checker`, default `formalization/.lake/build/bin/crosscheck-check`): it decodes the
code and builds the control-flow graphs itself (Lean `Thumb.binary_sound`, Paper I
`thm:machine-cycles`; format in `docs/certificate-format.md`); `--cycle-certificate F`
keeps it. The analysis, the graph construction and the bound computation leave the
trusted base; the Lean specification of the processor (decoder and timing table,
`Thumb.decode`), the loading of the binary as the checker reads it (the code of the certificate is compared with the binary, `crosscheck-check --elf`) and the loop bounds stay in it,
and are printed as such:

```
ok    ok_sum: bound 460 cycles = 9.583 us, budget 5000 cycles
processor: cortex-m0 (certified cycle bounds); trusted: the Lean specification of the Cortex-M0 (Thumb.decode: ...); that the binary is loaded as the checker reads it (its code and function entries are checked against the certificate by crosscheck-check --elf; an object is placed by the checker); the Lean checker (theorem Thumb.binary_sound); ...
```

Not supported: aiT as a back end (the flow facts it needs are exported, `flowfacts=`);
certified bounds for the OTAWA processors. Test: `time_budgets_after_compilation` (ctest, `tests/c/time_budget*.c`;
the two-file program needs an LLVM linker, `ld.lld` or `rust-lld`).

## Bounds in the parameters, without ranges (`symbolic`)

By default a loop whose inputs have no range is an error: a real-time function needs a
number. With `--opt=symbolic` (plugin: `-fplugin-arg-crosscheck-symbolic`) such a loop is
accepted if it has a ranking potential, which needs no range. The function then has no
numeric bound (`ok` stays false, the summary line says `SYMB`), and with `certificates`
the generator derives a bound in the parameters, affine or quadratic, which the checker
proves for all inputs:

```
SYMB count: no numeric bound; certified 5 + 6*max(0,n) units
```

Nothing new is trusted: the analysis only proposes the potential; the bound is the
checker's. A product of two parameters (nested loops both bounded by parameters) gets a
quadratic certified bound (e.g. `5 + 7*max(0,n) + 6*max(0,m)*max(0,n)`, and a call
composes it); three nested loops over parameters (a cubic bound) get no certificate. The mode is meant for
measuring unannotated code and for library functions whose callers supply the ranges.

## Whole projects, ACSL, and explanations

**A project.** `scripts/crosscheck_project.py --tool crosscheck-tool -p BUILD --out OUT
[--checker crosscheck-check] [--filter REGEX] [--all] [--baseline SNAPSHOT]` analyses
every translation unit of `BUILD/compile_commands.json` in parallel and writes
`OUT/project.json` (one record per function), `OUT/index.html` (totals, then a row per
function with its bound, loops, certificate status, assumptions and errors) and
`OUT/snapshot.json` (the baseline for the next run, compared by `cost_diff.py`).

**ACSL.** The report gives, for each loop, the invariants the analysis proved at the loop
head and a variant, and for each function its preconditions on integer parameters
(`"invariants"`, `"variant"`, `"requires"`). `scripts/acsl_export.py REPORT... --out DIR`
writes copies of the sources with these as ACSL annotations, for a deductive verifier
(Frama-C/WP) to prove independently. They are claims in mathematical integers: the
verifier needs its own overflow checks. The export has not been run through Frama-C in
this repository; the annotations are executed as run-time checks by
`tests/fuzz_bounds.py`.

**Why a loop has no bound.** The error for an unbounded loop names a likely cause: a
variable of the test without a range where the loop starts (and which side is missing), a
test that reads memory, a floating-point value or a call result, or bounded variables
with no decreasing combination. It is a hint and plays no part in any bound.

## Tests of soundness beyond the unit tests

| Test | What it does | Fails when |
|---|---|---|
| `tests/fuzz_bounds.py` (ctest `random_loops_bounds_hold`) | generates random loop programs, analyses them, runs them instrumented on all or sampled inputs | a derived loop bound is below an executed count; an exported invariant or variant is false at run time; a certificate is rejected; the interpreted mini-C export counts other loop iterations than the compiled C |
| `formalization/test/mutate_certificates.py` (ctest `checker_mutants_rejected_or_sound`) | changes one integer of an accepted certificate; runs accepted mutants in an independent interpreter of certificate programs | the checker accepts a mutant of which a run exceeds the bound |
| `benchmarks/tacle/compare_tools.py --check` | runs the TACLeBench kernels instrumented | a loop bound is below an observed count |
| `benchmarks/cycles/run_cycles.py --check` | runs the kernels on a Cortex-M0 interpreter | a cycle bound or a binary loop bound is exceeded |

The random programs found two defects when first run (2026-11-16): a loop whose body can
never return to the loop head was reported with 0 executions of its body instead of 1
(the function itself was already rejected, but the loop bound and the exported flow fact
were wrong), and the mini-C exporter wrote a source for a loop whose test it cannot
express (the checker then refused to validate it, rightly).

A third defect was found by reading the code while extending the mini-C export
(2026-11-16): the declaration of a **static local** variable was analysed as an
assignment at every call, although C initialises it once, before the first call. A loop
bounded by a static counter that grows from call to call (`static int n = 0; n++; for (i
= 0; i < n; i++)`) received a bound, and a certificate of the wrong program that the
checker accepted (the translation from C to the certificate is the unverified step;
validation against the source would have refused the function, whose static local the
exporter refused). Now the declaration of a static local does nothing at a call and its
value on entry is unknown, as for a global; a C++ static local with a dynamic initialiser
is an error. Regression test `Unsound.StaticLocalCounterGrowsAcrossCalls`; static locals
are now exported to mini-C (`ok_static_local`, `no_static_escaped`).

Analysis time (2026-11-16): the answers of the solver queries `entails`, `isFeasible` and
`boundsOf` are cached under the closed premises (they are functions of them), with one Z3
context per thread; the slowest TACLeBench program, `cjpeg_transupp`, went from 2,277 s
of analysis to 742 s, and to 376 s with the default search budget, all with the same bounds; the
whole sequential and application category from 88 to 23 minutes.

## Limitations

- **Cost is not time.** Turning the bound into a time bound needs per-instruction
  worst-case durations for the target, which depend on caches, pipelines and the
  compiler's code generation. The analysis works on the source AST, before
  optimisation.
- **Affine and simple logarithmic potentials.** A variable divided, or multiplied up to
  a constant limit, by a constant gets a logarithmic bound. A lexicographic argument
  (an inner counter reset when the outer one advances) is found when the inner counter
  has constant bounds that are inductive: the combination is then affine. Other loops
  or recursions that terminate by a logarithmic or non-linear argument get a linear
  bound (binary search) or are rejected; state the bound with `CROSSCHECK_LOOP_BOUND`.
- **Analysis time.** When a loop has no potential the search is repeated with more
  candidate invariants, each round re-analysing the loop body. On the TACLeBench kernels
  this made the whole run about 1.5 times slower; on the largest sequential program
  (`cjpeg_transupp`, 68 loops, 30 of them without a bound) about three times (ten minutes
  to half an hour on a loaded machine). A limit on the size of the bodies for which the
  search is repeated would bound this cost; it is not implemented.
- **Little amortisation.** The analyser multiplies nested loops; a recursive function is
  charged the worst-case cost of one activation for every activation (merge sort
  is bounded by `O(n²)`). Only certificates amortise, and only two shapes: an inner loop
  whose entry bound is the enclosing loop's potential (`j` from `i` to a constant), or what
  that potential has lost (`j` from `0` to `i`), with a constant entry bound of the
  enclosing loop. An outer body that contains both shapes (cost quadratic in the outer
  counter, as in the first nest of `ludcmp_test`) or an entry bound in a parameter keeps the
  product bound. Trying the second shape lowers each loop body that contains a loop once
  more (the examples of `tests/certificates/triangular.cpp` take 12 s instead of 5).
- **Calling contexts are intervals of integer arguments.** Relations between
  arguments, values of globals, and what a callee leaves in memory are not passed
  to the callee or back; recursive functions get no context. The analysis' bounds are
  numbers (certificates add summaries in the parameters).
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
src/analysis/MiniC.{hpp,cpp}        export of C functions as mini-C (validation of certificates)
scripts/cost_diff.py                cost diff of two sets of reports (CI)
src/plugin/Plugin.cpp               plugin registration
src/tool/Main.cpp                   crosscheck-tool
tests/core_test.cpp                 solver and arithmetic (no Clang needed)
tests/analyzer_test.cpp             end-to-end tests on C++ snippets
tests/benchmarks_test.cpp           expectations on ../benchmarks
```

`src/core` does not depend on Clang, and `src/analysis` does not depend on how
the analysis is launched.
