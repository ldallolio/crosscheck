# Implementation plan: from the theory to the tools

This file is the hand-off from the theory phase (paper + Lean, November 2026) to the
implementation phase. It says what is proved, what the implementation must produce to
connect to it, and in which order. Read `CLAUDE.md` first: its soundness rules and AGMAI
obligations apply to everything below.

See `docs/proposals.md` (2026-11-14) for the argued order of the next steps after tasks
1 and 2; it refines tasks 3 to 8 below.

## 1. What is proved (and where)

| Result | Paper | Lean |
|---|---|---|
| Cost logic for a language with nondeterministic atoms, loops, procedures (recursive too), assumed contracts; sound for terminating **and** non-terminating executions | `subsec:cost-logic`, `thm:cost-logic-soundness` | `Language`: `Derivable`, `soundness` |
| Symbolic bounds (bound = function of the initial state) and the call rule for summaries | `prop:summary-call` | `Language`: `ValidSym`, `validSym_call`, `validSym_seq` |
| Linear certificates and an executable checker; an accepted certificate bounds every execution | `subsec:checker`, `def:certificate`, `thm:checker-soundness` | `Checker`: `ACmd`, `check`, `check_sound`, `certified_cost_le` |
| Bound under an invariant and a calling context | `prop:context-bound` | `Certificate`: `ranking_bound_of_context`, `call_bound_of_context` |
| Lexicographic and logarithmic potentials (bounds on run length only) | `prop:lex-log` | `Certificate`: `lex_ranking_bound`, `log_ranking_bound` |

Not proved, and to be kept out of any claim: the translation from C/C++ (or Rust) to
`ACmd`; parallel composition; time on real processors.

## 2. The certificate format

See `docs/certificate-format.md`.

## 3. Tasks, in order

Each task ends with: tests (including must-reject cases), figures re-run
(`run_tacle.py`, `compare_tools.py --check`, `run_tpdb.py`), paper/README/guide/
`AI_USAGE.md` updated together.

1. **Checker executable** (Lean). **Done (Nov 2026)**: `lake build crosscheck-check`. `lake exe crosscheck-check cert.json`: parse the JSON
   into `ACmd`, run `check`, exit status. The parser is untrusted in the sense that a
   wrong parse can only make `check` examine a different certificate, so print the
   program it checked. No `native_decide` in proofs; the executable just runs `check`.
2. **Certificate emission** (plugin). **Done (Nov 2026)**: `--opt=certificates=FILE`;
   TACLeBench 142 of 158 bounded functions, all accepted by the checker; the example
   programs 7 of 13; calls (by inlining) and early returns are handled on the generator
   side, without changing the checker. Then (2026-11-14) early exits from loops, `switch`,
   `&&` tests (checker node `whileAnd`, proved in `check_sound`) and unsigned variables
   (wrap-around branches proved dead by the checker): TACLeBench 156 of 158, examples 10
   of 15 bounded functions. Original description: For a function whose analysis used only what the
   fragment covers (tracked integer locals, single linear guards, assignments, unknown
   values, affine potentials, invariants found by the Houdini step), emit the `ACmd`.
   Count how many TACLeBench / TPDB / example functions get a certificate that the
   checker accepts; that count is the headline result. The analyser's merge of paths
   corresponds to `weaken`; its `havoc` of loop-modified variables to the loop rule.
3. **Extend the checker** (Lean + paper), driven by what task 2 could not express, in
   this expected order: conjunctive guards (rule of disjunction of preconditions for the
   false branch); procedure calls with contexts (`Derivable.call`, non-recursive first);
   assumed contracts (`Derivable.assume`) for `CROSSCHECK_COST` and library contracts;
   **Done (2026-11-14)**: conjunctive guards (`whileAnd`), calls with summaries (`call`,
   `program_sound`, non-recursive), assumed contracts (functions without a body), symbolic
   bounds affine in the parameters (`SB`). Recursion (rule 9) is not a checker case yet.
   `break`/`continue`/`return` (flag variables or an exit-postcondition logic); recursion
   with a rank; lexicographic and logarithmic loop rules (`prop:lex-log`).
4. **Symbolic bounds in the plugin.** Costs become expressions over the entry values of
   the parameters instead of numbers; a callee's summary is instantiated at each call
   (`validSym_call`). This removes the limit of 8 contexts per function and gives
   bounds for the TPDB programs as they are. Needed by task 5.
5. **Library contracts.** Three tiers: analyse the implementation when its source is
   visible (already done for inline and template code); a contract file per library and
   version giving a cost expression in sizes, trusted and listed in the assumptions
   (formally: assumed triples); reject what is amortised, average-case or allocating
   (`vector::push_back`, hash containers). The C++ standard states complexities without
   constants, so a contract cannot be derived from the standard alone.
6. **Front-end coverage for industrial C** (MISRA C / AUTOSAR C++ subsets): global
   variables (unsound if another thread or an interrupt writes them: keep `volatile` and
   atomics untracked, require an annotation for shared globals); struct fields and
   arrays indexed by constants; pointers used as iterators; exact evaluation of loops
   with constant floating-point bounds (IEEE semantics of the target).
7. **Export of flow facts** in the formats of WCET tools (aiT annotations, OTAWA FFX), with
   the in-context bounds; then machine-level costing for cores without caches, using the
   proved loop bounds on the compiled code. **Export done (2026-11-14)**: `flowfacts=FILE`
   (FFX, AIS, AIS2), `sarif=FILE`, `scripts/cost_diff.py`; not yet loaded into OTAWA or
   aiT on compiled binaries (next: an OTAWA run on a cross-compiled TACLeBench kernel).
8. **Rust front-end** on MIR, emitting the same certificates.

## 4. Things to keep in mind

- A certificate is only as good as its link to the source: until the translation from
  the Clang AST to `ACmd` is argued (or tested against executions, as
  `measure_loops.py` does for loop counts), say "the certificate's program", not "the C
  function".
- Never weaken the checker to accept more: extend the logic, prove it, then extend
  `check`.
- Weights are parameters of the certificate; a certificate checked with unit weights says
  nothing about another cost model.
- Split the paper in two before a venue submission (theory + Lean; tool + evaluation).
