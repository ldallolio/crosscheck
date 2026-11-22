# Release record of Papers I and II (arXiv) and of the code

Prepared by the AI assistant (prompts 83 and 107 of `AI_USAGE.md`). It records the checks
made and the reproduction of Paper II's figures. The author's review of the papers is the
subject of the statement in each paper, not of this file.

## Archive

Release `v1.0` of the repository (tag on `c518c1a`, 2026-11-21): Zenodo
`doi:10.5281/zenodo.24425070` (all versions `doi:10.5281/zenodo.24425069`), Software
Heritage `swh:1:rel:70c77563037e6db2a55b48b3ad4963c86a67773f`; cited in the three papers,
`CITATION.cff` and `README.md`.

## Checks made by the AI (2026-11-21 and 22)

| Check | Result |
|---|---|
| Lean build | `lake build`: 0 errors, 0 warnings; no `sorry`, `admit` or new `axiom`; `#print axioms` of the new theorems: only `propext`, `Quot.sound`, `Classical.choice` |
| Table 1 against Lean | Every label of `formalization.yaml` exists in Paper I and every Lean name exists. Each paper statement was read next to its Lean statement. Gaps found and **closed by new Lean proofs** (module `Norms`): the bounds for every subadditive cost norm (`prop:worst-case-step`, `prop:tropical-dominance`, `thm:lyapunov-bound`; the Lean statements were for the instruction count and the weighted cost only), the `k`-block form of `prop:tropical-collapse` (only one block was in Lean), the least element and well-foundedness of the prefix order (`prop:poset-properties`), the least exiting trace (`thm:minimal-trace`, `prop:min_x`). Two existing lemmas were added to the table (`treePrefix_depth_le`, `exec_size_min`). No mismatch found in the other rows. On 2026-11-22 the statements on trees of any branching factor (`Branching`) and the absence of infinite executions (`prop:no-divergence`, `Divergence`) were mechanized; the list "Scope of the mechanization" of Paper I now holds only modelling hypotheses, cited classical results and two remarks marked as not formalized. |
| Figures of Paper II | Re-run on this machine: `tab:tacle` (identical to `run_tacle.py --latex`), `tab:tools` (every figure equal to `compare_tools.py`), the run with minimal annotations (10 -> 23 entry functions, 84 annotations in 18 kernels), TPDB, sequential/app/parallel programs, `ctest`: see section E |
| Bibliography data | The entries cited by Papers I and II checked against Crossref (and the 4 DOIs of LIPIcs/OASIcs against DataCite): no wrong author, title, year or DOI; the flags are formatting (subtitles, article numbers) or Crossref matching an unrelated record (book reviews, reprints). On 2026-11-22: the three new entries (Courcelle, Tarjan, Atkey) checked on Crossref; `matiyasevich1970enumerable` (no DOI) corrected against Math-Net.ru and the JSL review to the English translation whose title it gives (Soviet Mathematics Doklady 11(2):354-357) |
| Reading of cited works | 16 works provided by the author read on 2026-11-22 (cited passages); attributions changed accordingly in Paper I (Courcelle, Tarjan, Nielson 1987, Atkey, Kincaid, Farkas premise, Floyd) |
| Citations of web documentation | `clangeffects` and `infercost` read: both citing sentences are supported |
| Wording | No superlatives or priority claims ("first", "novel", "uniquely", "fully"...) in Papers I and II |
| AI statement | Models corrected: Claude Haiku 5.5 also appears in the transcripts (inside the component that reads web pages); added to the three statements and to `AI_USAGE.md` |
| Time and compute | Measured from the local transcripts and recorded in `AI_USAGE.md` §2 (about 76 hours of active session time, 5.8 million output tokens); cost left to the author |
| arXiv bundles | `python3 paper/make_arxiv.py theory tool binary`: each paper with its `.bbl`, references to the other papers' results replaced by their numbers (no `xr`, no `.aux` of another paper), compiled alone three times without warnings; the text of each bundle's PDF is identical to the normal build. Files in `paper/arxiv/` (gitignored) |
| Defects found and fixed | (1) CI: the two certificate-checking steps of `plugin_build.yml` piped the checker into `tee`, which hides its exit status (no `pipefail`): a rejected certificate would not have failed CI. They now test the checker's output (tested locally with a mutated certificate). (2) DEBIE's `Switch_SU_State` is exported and not validated (the generator tracks a field read through a pointer, the exporter writes an unknown value); the checker is right to refuse it; Paper II and `benchmarks/tacle/README.md` now say so (they gave the 309 validated without it). |
| Clean-up (prompts 86-88) | `main` = the working branch, CI green on GitHub (first run since 2026-11-12); copyright headers everywhere; no lint finding, no compiler warning; READMEs give current figures, history in a final section; planning documents marked historical |
| Repository metadata | `CITATION.cff`, `.zenodo.json`, `README.md` rewritten (the old one claimed "operadic tree algebras", removed from the papers, and that the open-source release was "planned" although the code is MIT-licensed) |

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
