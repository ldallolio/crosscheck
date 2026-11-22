# Release checklist for Papers I and II (arXiv)

Prepared by the AI assistant on 2026-11-21 (prompt 83 of `AI_USAGE.md`). It separates
what has been done and checked mechanically from what only the author can do. Nothing
here says that the author has verified anything.

## A. Done and checked by the AI (2026-11-21)

| Check | Result |
|---|---|
| Lean build | `lake build`: 0 errors, 0 warnings; no `sorry`, `admit` or new `axiom`; `#print axioms` of the new theorems: only `propext`, `Quot.sound`, `Classical.choice` |
| Table 1 against Lean (`AI_USAGE.md` §3 item 1, pre-check) | Every label of `formalization.yaml` exists in Paper I and every Lean name exists. Each paper statement was read next to its Lean statement. Gaps found and **closed by new Lean proofs** (module `Norms`): the bounds for every subadditive cost norm (`prop:worst-case-step`, `prop:tropical-dominance`, `thm:lyapunov-bound`; the Lean statements were for the instruction count and the weighted cost only), the `k`-block form of `prop:tropical-collapse` (only one block was in Lean), the least element and well-foundedness of the prefix order (`prop:poset-properties`), the least exiting trace (`thm:minimal-trace`, `prop:min_x`). Two existing lemmas were added to the table (`treePrefix_depth_le`, `exec_size_min`). No mismatch found in the other rows; the gaps that remain are those listed in "Scope of the mechanization" (branching factor above 2, termination for partial updates, ...). |
| Figures of Paper II | Re-run on this machine: `tab:tacle` (identical to `run_tacle.py --latex`), `tab:tools` (every figure equal to `compare_tools.py`), the run with minimal annotations (10 -> 23 entry functions, 84 annotations in 18 kernels), TPDB, sequential/app/parallel programs, `ctest`: see section E |
| Bibliography data | The 69 entries cited by Papers I and II checked against Crossref (and the 4 DOIs of LIPIcs/OASIcs against DataCite): no wrong author, title, year or DOI; the flags are formatting (subtitles, article numbers) or Crossref matching an unrelated record (book reviews, reprints) |
| Citations of web documentation | `clangeffects` and `infercost` read: both citing sentences are supported (`references/README.md`) |
| Wording | No superlatives or priority claims ("first", "novel", "uniquely", "fully"...) in Papers I and II |
| AI statement | Models corrected: Claude Haiku 5.5 also appears in the transcripts (inside the component that reads web pages); added to the three statements and to `AI_USAGE.md` |
| Time and compute | Measured from the local transcripts and recorded in `AI_USAGE.md` §2 (about 76 hours of active session time, 5.8 million output tokens); cost left to the author |
| arXiv bundles | `python3 paper/make_arxiv.py theory tool binary`: each paper with its `.bbl`, references to the other papers' results replaced by their numbers (no `xr`, no `.aux` of another paper), compiled alone three times without warnings; the text of each bundle's PDF is identical to the normal build. Files in `paper/arxiv/` (gitignored) |
| Defects found and fixed | (1) CI: the two certificate-checking steps of `plugin_build.yml` piped the checker into `tee`, which hides its exit status (no `pipefail`): a rejected certificate would not have failed CI. They now test the checker's output (tested locally with a mutated certificate). (2) DEBIE's `Switch_SU_State` is exported and not validated (the generator tracks a field read through a pointer, the exporter writes an unknown value); the checker is right to refuse it; Paper II and `benchmarks/tacle/README.md` now say so (they gave the 309 validated without it). |
| Clean-up (prompts 86-88) | `main` = the working branch, CI green on GitHub (first run since 2026-11-12); copyright headers everywhere; no lint finding, no compiler warning; READMEs give current figures, history in a final section; planning documents marked historical |
| Repository metadata | `CITATION.cff`, `.zenodo.json`, `README.md` rewritten (the old one claimed "operadic tree algebras", removed from the papers, and that the open-source release was "planned" although the code is MIT-licensed) |

## B. Decisions and actions that only the author can take

1. ~~Make the repository public~~: done by the author (2026-11-21).
2. ~~Tag the released revision~~: tag `v1.0` on `c518c1a` (2026-11-21). The commits carry
   the author's personal email address, now public (GitHub's noreply address is an option
   for future commits).
3. ~~Archive with a persistent identifier~~: Zenodo, release v1.0 `doi:10.5281/zenodo.24425070`, all versions
   `doi:10.5281/zenodo.24425069`; Software Heritage `swh:1:rel:70c77563037e6db2a55b48b3ad4963c86a67773f`. In Paper I's paragraph "Artifact", in a section
   "Artifact" of Papers II and III, in `CITATION.cff` and in `README.md` (2026-11-21). These
   changes come after the tag: the archived revision does not hold its own identifiers, and
   the papers point to it.
4. **arXiv account and endorsement**: a first submission in a category (cs.LO or cs.PL)
   may need an endorser. Upload `paper/arxiv/theory.tar.gz` first, then put its arXiv
   identifier into the `crosscheckTheory` entry of `paper/crosscheck.bib`, rebuild, rerun
   `make_arxiv.py tool`, and upload Paper II.
5. **Compute cost** in `AI_USAGE.md` §2 (from the billing), and confirm the measured time.
6. **Your statement in each paper** ("I have read the text and take full responsibility")
   must be true when you upload: section C is the reading it presupposes. Then set the
   status of item 2.A in `AI_USAGE.md` §2.

## C. What the author must read or decide for Papers I and II

Ordered by weight. The numbers are those of `AI_USAGE.md` §3; items 26, 40-50 concern
Paper III only.

1. **Proofs not in Lean** (item 2): the Farkas/template paragraph, the decidability
   remark, the fixed-point remark (since 2026-11-22 the tree statements for every
   branching factor and the absence of infinite executions are in Lean, and the scope list
   of Paper I holds only modelling hypotheses, cited classical results and two remarks
   marked as not formalized); and the proofs written by the AI in the text of
   Paper I (cost logic, checker, mini-C validation, amortised loops: items 17, 19, 21, 23,
   24, 28, 29, 31, 35, 36, 37, 39). The Lean theorems are machine-checked; what needs you
   is that each Lean statement says what the paper says (the AI's comparison is in
   section A; sample it) and the paper's prose proofs.
2. **Novelty and attributions** (items 7, 9, 18, 36, 37): the papers must not present
   classical ideas as new. `references/README.md` says, per entry, what the AI read. On
   2026-11-22 the AI read the cited passages of 16 works the author provided; Paper I now
   says it uses the prefix order (Courcelle 1983 for trees) and cites Tarjan 1985 for the
   size potential. Of the 71 cited works, 6 are still unread (Kahn, Manna, Winskel,
   Diekert, Matiyasevich, Podelski and Rybalchenko's transition invariants; all cited for
   well-known results) and about 20 were read in the abstract and the passage the citation
   relies on. Done the same day at the author's request: Nielson 1987's rule [R-4] and its
   bubble-sort recurrence cited as an earlier form of `prop:amortised-loop`, whose claim is
   now the checker case and the Lean proof; Atkey 2010 cited; Kincaid 2019 moved to loop
   acceleration; the satisfiability premise of the affine Farkas lemma stated; Floyd
   cited for lexicographic tuples. To read yourself: Nielson 1987 ([R-4], Section 5),
   Healy et al. Section 5, Albert, Genaim and Masud, Atkey Section 1, Courcelle Section 2.4,
   and the closest prior work, Sinn et al. 2014 and Carbonneaux et al. 2015.
3. **Statements only you can confirm** (items 3, 5): the sentence of Paper I, Section
   "Examples", on the prototype was reworded on 2026-11-21 to what `history/revenge/` shows
   (its tests include the infinite loop and the linear recursion); confirm the wording. Items 6 (old title) and 17 (an `\authortodo`
   that no longer exists) are out of date.
4. **Fairness of the comparisons** (items 11-15): default options of KoAT2, CoFloCo, Infer;
   the oRange build and the `filterbank` counterexample; the TPDB bounded-mode harness.
5. **The trusted translations** (items 20-24, 27, 31, 34): the plugin's lowering and the
   mini-C exporter are unverified C++ written by the AI; read `MiniC.cpp` and the
   hypotheses (no signed overflow, no aliasing of tracked variables, no concurrent writes),
   which the papers state.

## D. Optional before upload

- One external reader (WCET or resource analysis) for the introduction, the positioning
  and the main theorems of Paper I.
- `docs/qualification/README.md`: read by someone who knows DO-330 before it is shown to
  an industrial partner (item 30); it is not part of the papers.

## E. Reproduction on 2026-11-21

Run on the author's machine with the commands of each benchmark's README; every figure below
equals the one in Paper II.

| Part of Paper II | Result |
|---|---|
| `tab:plugin` | the 12 rows equal `benchmarks/bounds-baseline.json`, which `ctest` compares with the tool |
| `ctest` | 183 of 183 tests pass |
| `tab:tacle` | identical to `run_tacle.py --latex` (220 loops; 133 / 105 / 27 / 1; in context 142 / 131 / 9 / 2) |
| TACLeBench certificates | 161 of 165 bounded functions certified, all accepted; 152 validated, 1 not (`isqrt_main`, documented) |
| `tab:tools` | every figure equal to `compare_tools.py --check` (SCEV 113, oRange 131, flow facts below the count 2; functions 165 / 119+23 / 128+11 / 190+14) |
| minimal annotations | 10 -> 23 entry functions, 84 annotations in 18 kernels |
| sequential and app programs | 572 loops, 275 / 258 for every call, 330 / 304 in context, 9 and 10 below the flow fact; 231 certificates accepted |
| ROSACE and DEBIE | 476 bounded functions, 475 certified, 480 certificates accepted, 309 validated (1 not: `Switch_SU_State`, now stated) |
| TPDB | as is 11; with ranges 215 (KoAT2 288, CoFloCo 264, 305 by one of them, 198 of the 215 also by them); symbolic mode 147 certified (133 in the parameters, 14 constant), all accepted, KoAT2 96 / 34 / 3 |
| CMSIS-DSP | as is 161 functions, 363 loops; with ranges and context 616 functions, **1,069** loops: every file was analysed within the time limit this time (Paper II said 1,044, from runs where one or two files timed out; Paper II and the CMSIS README updated) |
| Rust front-end | `test_rust.py` passes (rustc 1.100.0) |
