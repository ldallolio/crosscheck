# CrossCheck — Project Context for Claude

## What this is
CrossCheck (formerly *"Imperative Programming as an Optimization Problem"*) derives sound, mechanical
WCET / execution-cost bounds by recasting imperative control flow (while loops, linear recursion,
non-linear branching recursion) as constrained optimization over execution traces (free monoid
`Σ*`) and computation trees (free term algebra `T_Σ`), with no step simulation or unrolling.

Two semantic layers, used consistently in prose and code comments:
- **Intensional layer** — traces/trees, the prefix order *order-by-composition* (`⊑`), cost.
- **Extensional layer** — state valuation, recurrence equations, closed-form terminal states.

Single author: Luca Dall'Olio. MIT licensed.

## Repository state (what actually exists)
| Path | Status |
|---|---|
| `formalization/` | Lean 4 + mathlib. **Builds clean (0 errors, 0 warnings), no `sorry`/`axiom`/`admit`.** 14 modules, 185 theorems. |
| `paper/theory/crosscheck-theory.tex` | **Paper I**: theory and Lean (framework, envelopes, cost logic, certificate checker, examples, mechanization; 29 pages). No measurements. |
| `paper/tool/crosscheck-tool.tex` | **Paper II**: the Clang plugin, certificate generation and the evaluation (TACLeBench, observed counts, five tools, related tools, TPDB; 13 pages). Refers to Paper I's numbered results through `xr` (`\externaldocument[I-]{../theory/crosscheck-theory}`): **build Paper I first**. |
| `paper/crosscheck.bib` | Shared bibliography (both papers use `\bibliography{../crosscheck}`; each lists only what it cites: theory-side related work in Paper I's `sec:related`, tool-side related work in Paper II's `sec:related`). Target venue: **arXiv**; both papers compile with no warnings. The combined single paper was split on 2026-11-14 (it is in git history). |
| `clang-plugin/` | Clang 18 plugin + standalone tool (C++20, Z3). Research prototype; 135 CTest tests pass (with `-DCROSSCHECK_CHECKER=…`). Emits cost certificates (`--opt=certificates=FILE`), flow facts for WCET tools (`flowfacts=FILE`: FFX, AIS, AIS2) and SARIF (`sarif=FILE`); `scripts/cost_diff.py` for CI; `benchmarks/bounds-baseline.json` must equal `tab:plugin`. See `clang-plugin/README.md`. |
| `benchmarks/` | 10 annotated real-time example programs (7 accepted, 3 that must be rejected), with `README.md`. |
| `benchmarks/tacle/` | `run_tacle.py`: fetches TACLeBench (pinned rev `4e4fbf7`) into `.cache/` (gitignored, never vendored), runs the tool unannotated on the 29 kernels, compares loop bounds with the `loopbound` pragmas. Results in its `README.md` and paper Table `tab:tacle`. `compare_tools.py` + `llvm_scev.py` + `measure_loops.py`: comparison with LLVM ScalarEvolution (run live), with loop counts observed by running the instrumented kernels (live; `--check` fails if a CrossCheck bound is below one, used in CI), KoAT2, CoFloCo (on the same llvm2kittel programs), Infer and oRange (answers stored in `results/`, produced in network-less containers; `koat_in_container.sh`, `its_in_container.sh`, `cofloco_in_container.sh`, `orange_in_container.sh`). Paper Table `tab:tools`. |
| `benchmarks/tpdb/` | `run_tpdb.py`: fetches TPDB `Complexity_C_Integer` (pinned rev `bf19a3c`, 553 programs) into `.cache/`, runs CrossCheck as is and with input ranges added by a script (`harness()`), compares with KoAT2/CoFloCo answers stored in `results/` (`tools_in_containers.sh`). Paper paragraph "Complexity benchmarks" in `subsec:tacle`. |
| `references/` | `fetch_papers.py` downloads open-access copies of cited papers into `references/pdf/` (gitignored: do not commit PDFs, most are copyrighted); `README.md` records, per entry, the source and what was actually read and checked. Update it when a paper is read. |
| `docs/proposals.md` | Argued proposals and order after the first certificate results: scientific (verified lowering, modular symbolic certificates…), industrial (flow-fact export, CI, qualification, contracts), legacy-language subset. |
| `docs/implementation-plan.md` | Hand-off from the theory phase: what is proved, the certificate format (= Lean type `ACmd`), and the ordered implementation tasks. Keep it current. |
| `AI_USAGE.md` | AI usage record required by the AGMAI guidelines (see below). |
| `docs/guide/` | Companion guide for the author, 7 parts, about 1,100 lines and 19 diagrams: background, Paper I, Paper II, plugin internals, Lean (tutorial + modules), bibliography map, expert Q&A. Quotes Lean names, plugin classes and paper labels: update it when they change; prefer a diagram or a table to prose. |
| `formalization/formalization.yaml` | Machine-readable paper-label ↔ Lean-name map (mirrors Table 1 of the paper). |
| `.github/workflows/lean_build.yml` | CI: elan → `lake exe cache get` → `lake build` on push/PR to `main`. |
| `.github/workflows/plugin_build.yml` | CI: Ubuntu 24.04 apt packages (LLVM/Clang 18, Z3, GTest) → CMake/Ninja build → full `ctest` → TACLeBench run and comparison (`compare_tools.py --check`) → certificates of TACLeBench and the examples; a second job builds `crosscheck-check` and checks every certificate. |
| `docs/certificate-format.md` | The certificate format (= Lean `ACmd`) and how the plugin produces certificates. |

Toolchain on this machine: `lake`, `lean`, `pdflatex`, `latexmk`, system `g++` 13. Clang 18, Z3,
CMake, Ninja and GoogleTest live in the conda env `crosscheck`
(`/home/ldallolio/miniforge3/envs/crosscheck`); there is no system clang/cmake/z3.
**Do not compile with that env's own GCC** (`x86_64-conda-linux-gnu-g++`): its binaries need a
newer CPU than this machine has ("CPU ISA level is lower than required"), and Clang 18 cannot
parse its libstdc++ headers. Use the system `g++` and point Clang at the system libstdc++.

## Commands
```bash
# Lean (from formalization/). Goal: 0 errors, 0 warnings.
lake exe cache get        # first time only: download prebuilt mathlib
lake build
lake build crosscheck-check   # the certificate checker program (CheckerMain.lean, no mathlib)

# Paper (from paper/)
(cd theory && latexmk -pdf crosscheck-theory.tex)   # first: Paper II reads its .aux
(cd tool && latexmk -pdf crosscheck-tool.tex)
# or: pdflatex crosscheck && bibtex crosscheck && pdflatex crosscheck && pdflatex crosscheck

# Clang plugin (from clang-plugin/), on this machine:
E=/home/ldallolio/miniforge3/envs/crosscheck
$E/bin/cmake -S . -B build -G Ninja -DCMAKE_MAKE_PROGRAM=$E/bin/ninja -DCMAKE_PREFIX_PATH=$E \
  -DCMAKE_C_COMPILER=/usr/bin/gcc -DCMAKE_CXX_COMPILER=/usr/bin/g++ \
  -DCMAKE_EXE_LINKER_FLAGS="-L$E/lib -Wl,-rpath,$E/lib" \
  -DCMAKE_MODULE_LINKER_FLAGS="-L$E/lib -Wl,-rpath,$E/lib" \
  -DCROSSCHECK_CLANG_EXTRA_FLAGS="--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13"
$E/bin/ninja -C build && (cd build && $E/bin/ctest --output-on-failure)
# Try it on one file:
./build/crosscheck-tool --summary ../benchmarks/fir_filter.cpp -- -std=c++20 -Iinclude \
  --gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13
```
Toolchain: `leanprover/lean4:v4.16.0`, mathlib pinned to tag `v4.16.0` in `lakefile.lean`.
Note `lake-manifest.json` is gitignored, so dependency revs are not locked in git.

## Lean formalization (`formalization/ImperativeOptimization/`)
Everything lives in `namespace ImperativeOptimization` (examples in `…Examples`).
Import graph: `State`, `Trace`, `Tree` import mathlib only; `Dominance`, `FixedPoint` → `Trace`;
`OperationalSemantics` → `Trace`, `Tree`; `WhileLoop` → `State`, `FixedPoint`, `OperationalSemantics`;
`Ranking` → `WhileLoop`; `Recursion` → `OperationalSemantics`; `Certificate` → `WhileLoop`; `Arity` and `Language` import mathlib only; `Checker` → `Language`;
`Examples` → `Ranking`, `Recursion`.
`ImperativeOptimization.lean` is the root that imports all modules — add new modules there.
Every file starts with the MIT copyright header; keep it on new files.

| Module | Key content |
|---|---|
| `State` | `PointedState S := Option S` (`none` = ⊥), `PartialTransition`, `extendToPointed`, `stateComp` |
| `Trace` | `Trace := List Instr`; `traceIter` (notation `t ^[n]`); `cost := length`; weighted `wcost`; `⊑` (prefix) refl/trans/antisymm, `order_cost_le`; `iter_monotone`, `iter_monotone_iff`; `exists_minimal_iteration`; `nestedTrace` + cost lemmas; `⊑_sub` (`List.Sublist`), `iter_subseq_nested`, `inner_subseq_nested` |
| `Tree` | `BTree` (binary), `size`, `leafCount`, `depth`, `graft` (`⊗`), `graft_size`, `graft_leafCount`, `graft_assoc`; `⊑_graft` (`GraftOrder`, uniform grafting); `⊑_tree` (`TreePrefix`, per-leaf substitution — **this is the paper's tree order**) refl/trans/antisymm(Unit), `treePrefix_size_le`, `treePrefix_fullTree`, `size_le_of_depth_le`; `fullTree`; `treePow` (`treePow b 0 = leaf`), `treePow_leafCount`, `treePow_size`, `treePow_cherry`, `treePow_chain` |
| `Dominance` | `≼_O` refl/trans; `branch_supremum_bound`; `add_dominated_by_max`, `max_dominated_by_add`; `condTrace`, `condTrace_cost_le` |
| `FixedPoint` | `evalTrace`, `evalTrace_concat`, `evalTrace_iter` (`⟦t^n⟧ = ⟦t⟧^n`) |
| `OperationalSemantics` | `MinimalIter` (+ `.unique`), `LoopConstraint`/`solveLoop`/`isLoopSolution`, `LinearRecurrence`/`solveLinearRecurrence` |
| `WhileLoop` | `WhileBigStep` (inductive big-step), `MinimalExit`, `whileBigStep_iff_minimalExit`, `while_trace_semantics`, `whileBigStep_total_iff`, `solveLoop_sound`; `runTrace` (state-dependent body traces), `runTrace_cost_le` |
| `Ranking` | `rankBound` (= ⌈V₀/Δ⌉), `ranking_descent`, `ranking_bound`, `ranking_terminates`, `wcet_bound`, `nested_wcet_bound` (ℤ-valued potentials, total update) |
| `Recursion` | `FramedRecurrence`/`unwind`/`FramedBigStep`, `framedBigStep_iff`, `linRec_iff`, `linear_recursion_cost`; `TreeRecurrence`, `IsExecTree`, `LeavesExit`, `evalTree`, `exec_least`, `exec_unique`, `TreeBigStep`, `treeBigStep_iff`, `exec_depth_le`, `exec_size_le` |
| `Certificate` | Soundness of what the plugin computes: `ranking_bound_floor` (relational, ordered-field-valued potential, bound `⌊V⌋`), `partial_ranking_floor`, `farkas_sound(_affine)`, `while_cost_bound`; invariants and contexts (`run_invariant`, `ranking_bound_of_context`, `call_bound_of_context`); `lex_ranking_bound`, `log_ranking_bound` |
| `Arity` | `RTree`/`Forest` (mutual, arbitrary arity), `geom`, `geom_closed`, `RTree.size_le_geom`; call trees of a scheme `calls : α → List α`: `callTree_size_le_potential` (size potential), `callTree_size_le_geom` |
| `Language` | Small imperative language `Cmd ι S` (atoms are weighted relations; calls of procedures with bodies `Φ`, recursion allowed), cost semantics `Exec` (terminating) and `Pre` (execution prefixes, so diverging runs are bounded too), `Valid` triples, rules `valid_seq`/`valid_ite`/`valid_while`/`valid_call`/`valid_conseq`/`valid_unreachable`, proof system `Derivable Φ Γ` (assumed triples `Γ` = contracts; rule `call` with a rank for recursion), **`soundness`**; symbolic bounds `ValidSym`, `validSym_call` (function summaries), `validSym_seq`; examples `countLoop_cost`, `down_cost` (recursion) |
| `Checker` | Concrete linear instance: `PExp`, `Lin` (constraints over program and logical variables), Farkas certificates `entails1`, annotated programs `ACmd` (incl. `whileAnd`: loop with a conjunctive test), executable **`check`**, **`check_sound`**, `certified_cost_le`; example `countCert_checks` (by `decide`). This type is the certificate format the plugin must emit (`docs/implementation-plan.md`) |
| `Examples` | Paper examples with minimality, big-step agreement and ranking/depth certificates |

### Paper ↔ Lean correspondence
Table 1 of the paper (Section "Mechanization in Lean 4") and `formalization/formalization.yaml`
list which Lean theorem backs which paper statement. **They are a contract:**
- If you rename, restate or delete a Lean theorem, update the `\lean{...}` mentions in
  `paper/theory/crosscheck-theory.tex`, Table 1, and `formalization.yaml` in the same change.
- If you change a paper statement, check the Lean statement still says the same thing
  (hypotheses included) — or move it to the "not mechanized" list.
- Refer to paper statements by `\label` (e.g. `thm:lyapunov-bound`), never by number.

Paper content that is **not** mechanized (the paper says so explicitly; keep that list honest):
- branching factor `b > 2` for the tree *order*, tree powers and minimality of the execution tree
  (binary in Lean); the *counting* bounds are mechanized for arbitrary arity (`Arity`);
- termination (existence of the minimal exit) for partial/nondeterministic updates — only the bound
  on run length is proved there (`ranking_bound_floor`);
- the equation-generating rules of Section "Application"; completeness of Farkas' Lemma;
- the Clang plugin itself (C++) and Z3; the translation from C++ to the commands and triples
  of `Language` and to the certificates of `Checker` (the lowering is unverified); parallel
  composition; lexicographic/logarithmic potentials as rules of the logic or of the checker
  (they are theorems on runs only); calls in the checker (the plugin inlines them). Conjunctive
  loop tests are in the checker (`whileAnd`); `break`/`continue`/`return` and `switch` are
  lowered by the plugin with flags and choice variables, so they need no checker rule.
`Dominance` still contains the `≼_O` preorder and `Trace` the subsequence order; the paper no
longer uses them (removed in the Nov 2026 simplification) — do not reintroduce them in the paper.

Axioms: only Lean's standard `propext`, `Quot.sound`, `Classical.choice` may appear in
`#print axioms`. Say "no axioms beyond Lean's three standard ones", not "zero axioms".

### Lean conventions & gotchas
- **No `sorry`, `admit`, or new `axiom`.** Keep `lake build` warning-free (unused hypotheses →
  prefix with `_`; the linter also flags tactics that do nothing).
- A theorem whose hypotheses cannot be satisfied proves nothing. When stating a bound, check
  that the hypotheses hold in at least one example (see `Examples.parametric_loop_ranking`).
- Prefer `omega` (handles `Int.toNat`, `/` and `%` by literals, `max`), `ring`, `linarith`,
  `simp`/`dsimp`, `push_cast`; induction with `generalizing` where needed.
- **Notation clash:** `Trace.lean` defines `t ^[n]` for `traceIter`, while mathlib's `f^[n]` is
  `Nat.iterate`. They resolve by type; if elaboration gets confused, write `traceIter t n`.
- Functions defined by structural recursion into `Prop` (`IsExecTree`, `LeavesExit`) unfold with
  `obtain ⟨…⟩ := h`, `exact h`, or `simp [IsExecTree]`.
- Pin to mathlib APIs available at v4.16.0 (e.g. `List.length_pos`, `Function.iterate_succ_apply'`).

## Papers (`paper/theory/`, `paper/tool/`)
- Paper I holds every theorem; Paper II holds every measurement (`tab:plugin`, `tab:tacle`,
  `tab:tools`, TPDB, certificate counts) and refers to Paper I as `\cite[Theorem~\ref{I-label}]{crosscheckTheory}`.
  A new result goes into Paper I; a new figure into Paper II. Paper I cites Paper II only as
  `\cite{crosscheckTool}`.
- For arXiv, Paper II must be uploaded with `crosscheck-theory.aux` (or the `I-` references
  replaced by numbers).
- Theorem environments share one counter: `thm`, `defn`, `prop`, `lem`; plus `defn*`, `rem*`.
  Use `\label{def:…}`, `prop:…`, `thm:…`, `sec:…`/`subsec:…` and reference via `\ref`.
- Math in standard LaTeX only (`$…$`, `\[…\]`); never unicode operators in `.tex`.
  Use `\sqsubseteq`, `\preceq_{\mathcal{O}}`, `\otimes`, `B^{\otimes d}`, `\Sigma^*`, `\mathcal{T}_\Sigma`.
- Terminology: "intensional layer", "extensional layer", "order-by-composition",
  "cost envelopes" (not "asymptotic dominance envelopes"), "timing schema" for the
  sum/max/bound×body rules (cite Shaw, Puschner & Koza), "ranking potential", "size potential".
- Removed on purpose in the Nov 2026 simplification (author-approved): the `Σ^∞` cpo / Kleene
  theorem (now a remark), the `≼_O` preorder, the subsequence order, operad / KAT / Higman
  remarks, the store-rule subsections, "Program Synthesis" in the title.
- Bibliography style `unsrt`. Every `\cite` key resolves. Entries added by AI come from model
  memory unless noted in `AI_USAGE.md`; never add a reference you cannot substantiate, and never
  guess a missing key silently — record the guess in `AI_USAGE.md`. On 2026-11-13 every entry
  was checked against Crossref, DataCite or Open Library (see `AI_USAGE.md`); check new entries
  the same way.
- Macros: `\lean{name}` for Lean identifiers (breakable), `\sem{t}` for the valuation,
  `\cost`, `\depth`, `\leaves`, `\lfp`, `\bigstep`; `\authortodo{...}` marks text the author
  must confirm — the paper must not be submitted while any `\authortodo` remains.
- Keep the file ASCII (it is loaded with `latin9` inputenc); write accents as `\"o`, `\'e`.
- Do not over-claim: the Clang plugin is an unverified research prototype; the evaluation is
  `tab:plugin` (our own small examples) plus `tab:tacle`/`tab:tools` (TACLeBench kernels compared
  with their flow facts, which hold for fixed inputs, with observed loop counts, and with LLVM, KoAT2, CoFloCo, Infer and oRange, untuned); cost bounds are not
  timing bounds (see the Limitations section).
- `tab:plugin` must match `benchmarks/README.md` and the tool's actual output; `tab:tacle` and the
  numbers in subsection `subsec:tacle` must match `run_tacle.py --latex` output (state for each
  figure whether it is a bound for every call or in context) and
  `benchmarks/tacle/README.md`; `tab:tools` and the paragraph "Comparison with other tools" must
  match `compare_tools.py` output; the paragraph "Complexity benchmarks" must match
  `run_tpdb.py` output and `benchmarks/tpdb/README.md`. Re-run before changing any figure; a change to the analyser
  that changes these figures must update the tables, the paper text and the READMEs together.
- Build artifacts (`.aux`, `.log`, `.pdf`, …) are gitignored; don't commit them.

## Clang plugin (`clang-plugin/`)
User documentation: `clang-plugin/README.md` (annotations, cost model, soundness, limitations).
Pipeline: annotated function → `Analyzer` walks the Clang AST → symbolic state (affine
expressions over immutable symbols + linear facts) → Z3 via Farkas (`src/core/Solver.cpp`).
- `src/core` must stay free of Clang headers (it is unit-tested alone, compiled with exceptions
  for the Z3 C++ API); `src/analysis` must not know whether it runs as plugin or tool.
- Annotations are macros expanding to `[[clang::annotate]]` or to an unevaluated
  `sizeof(crosscheck::detail::marker(...))`; there are no custom `[[crosscheck::...]]` attributes.
- **Soundness rules of the analyser — do not weaken them:**
  - every fact in a `State` must be true on that path forever (symbols are immutable);
  - candidate loop invariants are kept only if Z3 proves base case and inductive step;
  - unsigned results are used only when proved not to wrap; signed overflow is assumed absent (UB);
  - limits of 32/64-bit types are never given to symbols (`symbolRange`), so they cannot become bounds;
  - anything trusted (LOOP_BOUND, BOUNDED, ASSUME, COST, libm, external preconditions) goes into
    the report's `assumptions`;
  - a new loop/recursion feature needs a "must be rejected" test in `tests/analyzer_test.cpp`
    (suites `Unsound`, `UnsoundContext`);
  - certificates: never make the checker accept more without a Lean proof; the generator
    (Analyzer.cpp "Certificates", core/Cert.*) may do anything, the checker decides; lists
    that the checker compares syntactically must be built with the replicas in `Cert.cpp`;
  - calling contexts: expressions are evaluated on all states before they are costed; an
    argument counts only if it already has the parameter's type; functions that call
    themselves get no context; every interval end is re-checked by `entails`.
- Each kind of certificate has a Lean theorem (table in `clang-plugin/README.md`, section
  "Soundness"). When you add a cost rule or certificate, add the Lean theorem or say none exists.
- Known imprecision (documented, not bugs): linear potentials only (binary search gets a linear
  depth), no amortisation (merge sort is quadratic), calling contexts are intervals of integer
  arguments only (no relations, globals or callee effects; none for self-recursive functions),
  numeric bounds only, `switch` = sum of cases.

## Responsible release of AI-assisted mathematics (MANDATORY)
An objective of this project is publication on **arXiv**. All work on the paper, the
bibliography and the Lean code must respect AGMAI's *Responsible Release of AI-Generated
Mathematics* (<https://agmai.org/general-sep29/>, 29 Sept 2026). Concretely, whenever an AI
tool (including you) touches mathematical content:

1. **Human responsibility comes first.** The author must understand every argument, verify it
   personally and take full responsibility. Never write text asserting that the author has
   verified something; use `\authortodo{...}` and list what needs checking in `AI_USAGE.md` §3.
2. **Record the AI use** in `AI_USAGE.md`: date, tool, exact model name(s), the prompts
   verbatim, a summary of the reasoning and of what changed. Time and compute cost are filled in
   by the author. Keep the paper's "Statement on the Use of AI" consistent with that file.
3. **Literature.** Search for prior work and cite the papers where ideas were first introduced,
   even if rediscovered independently. Do not present classical results as new (see the
   "Positioning" subsection). Flag every reference taken from memory for author verification.
4. **Write-up.** Traditional style: precise statements, complete proofs, standard terminology.
5. **Formalize as far as possible** and state the formalization status precisely: what is
   machine-checked, what is not, and under which modelling choices. Keep Table 1 and
   `formalization.yaml` in sync with the Lean code.
6. **Repositories.** Released artifacts need a persistent, citable identifier and version
   history (arXiv for the paper; an archived, tagged revision for the Lean code).
7. **No marketing.** No superlatives or unverifiable claims ("uniquely", "fully", "zero ...").

Open items before submission are tracked in `AI_USAGE.md` §2 (audit table).

## Current focus
1. Pre-submission: resolve every open item of `AI_USAGE.md` (author verification, references,
   archived artifact, remaining `\authortodo`).
2. Plugin evaluation: TACLeBench kernels done (unannotated); next a run with minimal annotations,
   the sequential/app categories (done: observed loop counts, LLVM ScalarEvolution,
   KoAT2, CoFloCo, Infer, oRange, TPDB C complexity programs).
3. Roadmap agreed with the author (aims: industrial value and scientific result). The theory
   phase is done (Nov 2026): cost logic with procedures, recursion and assumed contracts
   (`Language`), verified certificate checker (`Checker`), lexicographic and logarithmic
   potentials (`Certificate`). **The implementation phase follows
   `docs/implementation-plan.md`**: checker executable, certificate emission by the plugin,
   checker extensions, symbolic bounds, library contracts, industrial C coverage, flow-fact
   export, Rust front-end. Split the paper in two before venue submission (theory + Lean;
   tool + evaluation).
   Plugin precision done so far (Nov 2026): calling contexts as argument intervals
   (`prop:context-bound`), facts kept across `break` exits, interval joins. Split of what
   remains, agreed with the author — **with theory and Lean** (new certificates): symbolic
   bounds in the parameters used as function summaries; lexicographic, multi-phase and
   max-of-affine potentials; logarithmic potentials; amortised recursion cost. **Engineering
   under existing certificates** (must-reject tests, assumptions listed): global variables;
   exact evaluation of constant float loops; pointer/iterator counters; relations between
   arguments in contexts.
4. Optional Lean extensions: tree order for arbitrary arity; termination for relational updates.
