# AI usage record

This file documents how AI was used in the CrossCheck paper and Lean development,
following AGMAI's *Responsible Release of AI-Generated Mathematics*
(<https://agmai.org/general-sep29/>, version of 29 September 2026).
It must be kept up to date whenever an AI tool changes the paper, the bibliography
or the Lean code, and it must be complete before any arXiv submission.

## 1. Sessions

### Session of 2026-11-11

| Item | Value |
|---|---|
| Tool | Claude Code (Anthropic) |
| Models | Claude Opus 5.5 (`claude-opus-5-5`), then Claude Fable 5.2 (`claude-fable-5-2`) |
| Wall-clock time | not recorded — **author to fill in** |
| Estimated compute cost | not recorded — **author to fill in** |

Prompts (verbatim):

1. "You are inside the repository for the crosscheck project. I put a @CLAUDE.md please
   read it, also read @README.md and all the other files, improve CLAUDE.md"
2. "Improve the latex paper, bibliography and lean code as you suggest. Once done, use a
   critical approach to make this paper solid, complete, coherent and relevant, to
   prevent peer review critics. Take your time to do a precise and quality work."
3. "Verify this paper using the "Responsible Release of AI-Generated Mathematics" by
   AGMAI you can find it here : https://agmai.org/general-sep29/ note in CLAUDE.md that
   these guidelines must be respected (one objective of this project is to publish on
   arvix)"

Summary of the AI's reasoning and of what it changed:

- **Review.** The assistant read the paper against the Lean sources as a hostile
  referee would and found: a vacuous Lean theorem (`ranking_bound` assumed an
  unsatisfiable hypothesis); a false claim (the valuation was called a continuous
  homomorphism on infinite traces); an example system infeasible for even `R`;
  an "iff" proved in one direction only; `treePow` off by one with respect to the
  paper; a Lean tree order different from the paper's; no link between "minimal n" and
  an actual loop semantics; loop bodies with branches treated as a fixed trace;
  missing and uncited bibliography entries; over-claims about the (non-existent)
  compiler plugin and about "zero postulates".
- **Lean (written by the AI, checked by the Lean kernel).** New modules `WhileLoop`,
  `Ranking`, `Recursion`; extensions of `Trace` (weighted cost, `iter_monotone_iff`,
  subsequence embeddings), `Tree` (prefix order `⊑_tree`, depth, corrected `treePow`),
  `Dominance` (`condTrace_cost_le`, `add_dominated_by_max`), `FixedPoint`
  (`evalTrace_iter`), `OperationalSemantics` (`MinimalIter`), `Examples` (minimality,
  big-step results, ranking certificate). The old `ranking_bound` was replaced.
  The old `TreeOrder`/`⊑_tree` was renamed `GraftOrder`/`⊑_graft`.
- **Paper (rewritten by the AI).** New sections: Positioning, Related Work,
  Bodies with data-dependent paths, Mechanization, Limitations, Statement on the Use
  of AI. Restated and re-proved: Propositions on monotonicity, tree order, tree powers,
  linear recursion (now frame-dependent), tree optimisation; Theorems on extensional
  equivalence and the Lyapunov bound (now integer-valued, with termination). The
  parametric-loop equation system was corrected. Claims about tooling were toned down.
- **Bibliography (compiled by the AI).** 26 entries added. Page numbers of
  `blazy2013formal` and `alias2010multi` were checked on the web; the others come from
  the model's memory. Two keys could not be resolved at first and were replaced by a
  guess; the author then supplied the original BibTeX records (2026-11-11), which
  settled them: `books/daglib/0070910` is Winskel 1993 (guess confirmed);
  `Attali90aformal` is Attali, Caromel & Russo, "A Formal Executable Semantics for
  Java", so the guessed Centaur reference (Borras et al. 1988) was removed and the
  original restored as `attali1998formal`. The record gave "Princeton University,
  1990", which cannot be right (Java postdates 1990); the AI changed it from memory to
  the OOPSLA'98 Workshop on Formal Underpinnings of Java (1998). A web search confirmed
  the work exists and dates from 1997--98 (ERCIM News 36) but **not the venue — author
  to verify**. `Havelund2000` → Havelund & Pressburger 2000 (matches the record, with
  the spelling "Pressburguer" corrected).

### Session of 2026-11-12 (same conversation, continued)

| Item | Value |
|---|---|
| Tool | Claude Code (Anthropic) |
| Model | Claude Fable 5.2 (`claude-fable-5-2`) |
| Wall-clock time | not recorded — **author to fill in** |
| Estimated compute cost | not recorded — **author to fill in** |

Prompts (verbatim; the first one consisted only of pasted BibTeX records, which the AI
used to resolve the two guessed citations, see above):

4. "Start working on the C++ plugin : plan and then implement it with tests and
   documentation, then improve the lean code with any missing or incomplete
   demonstrations. Make code examples where the plugin has practical uses, for example
   in real time codes, in real world problems."
5. "I would like you to check the pertinence and usefulness of the bibliography in the
   current paper, adding or removing sources by justifying it. Make sure to cite
   previous recent work as requested on scientific papers. Also, I would you to point
   out if the paper should be simplified, maybe removing some concepts and keeping more
   generic ones ? Give me a synthetic report of your actions that I can validate before
   doing any changes."
6. "I approve all your proposals, proceed"
7. "Please complete your task"

Summary of the AI's reasoning and of what it changed:

- **Bibliography (proposed by the AI, approved by the author in prompt 6).** Removed:
  `havelund2000jpf`, `attali1998formal` (Java tools, unrelated to cost bounds),
  `barbosa2022cvc5`, `higman1952ordering`, `kozen1997kat`, `loday2012operads` (supported
  side remarks that were cut). Added, each with bibliographic data checked by web search
  on 2026-11-12: `shaw1989reasoning`, `puschner1989calculating` (the timing schema — the
  direct prior art of the branch/loop cost rules, previously uncited),
  `maroneze2014formally`, `benamram2014ranking`, `lommen2022automatic`,
  `frohn2020calculus`, `kincaid2019closed`, `hoffmann2022two`, `kahn1987natural`,
  `leroy2009coinductive`, `gueneau2018fistful`, `haslbeck2018hoare`, `clangeffects`
  (Clang documentation). The AI checked titles, venues and page ranges, **not the
  content of the papers**: the sentences describing them come from the model's memory
  and from search-result summaries. The claim that max-plus algebra "is the standard
  algebra of worst-case timing" was replaced by an attribution to the timing schema.
- **Simplification of the paper (proposed by the AI, approved by the author).** Removed
  the `Σ^∞` completion and the intensional Kleene theorem (now a remark), the asymptotic
  dominance preorder (only the branch rule is kept), the subsequence order, the operad /
  Kleene-algebra / Higman remarks, the "loop versus tree exponentiation" remark, the
  three store-rule subsections and the two duplicated recursion subsections of the
  Application section (now prose). Title: "Imperative Program Synthesis" dropped.
- **Paper, new material written by the AI.** Proposition "Size Potential"; the relational
  variant of the Lyapunov bound; Section "Prototype Implementation" with Table 2; updated
  Related Work, Mechanization and Limitations.
- **Lean (written by the AI, checked by the Lean kernel).** New modules `Certificate`
  (`ranking_bound_floor`, `ranking_bound_of_le`, `while_ranking_floor`,
  `partial_ranking_floor`, `farkas_sound`, `farkas_sound_affine`, `while_cost_bound`) and
  `Arity` (trees of arbitrary arity, `geom_closed`, `RTree.size_le_geom`,
  `callTree_size_le_potential`, `callTree_size_le_geom`). 137 theorems, builds without
  warnings.
- **Clang plugin (designed and written entirely by the AI).** `clang-plugin/` (about
  3,200 lines of C++, 1,000 lines of tests, 102 CTest tests passing on the author's
  machine with Clang 18.1.8 and Z3 5.1.0) and `benchmarks/` (10 example programs written
  by the AI). The figures of Table 2 of the paper are the output of this tool on these
  programs. The implementation is not formally verified.

### Session of 2026-11-12, continued (companion guide)

| Item | Value |
|---|---|
| Tool | Claude Code (Anthropic) |
| Model | Claude Fable 5.2 (`claude-fable-5-2`) |
| Wall-clock time | not recorded — **author to fill in** |
| Estimated compute cost | not recorded — **author to fill in** |

Prompt (verbatim):

8. "Your next task is to write a second document about the paper with detailed
   explications for each concept (referred or introduced) and a summary for each
   bibliography source that I can use to understand without being experienced with the
   theory or state of the art. Make these hypothesis : I am an experienced software
   engineer with almost zero theoretical knowledge in this field. I understand the problem
   and the idea in the paper, since I wrote the first version, but no more. I read the
   text by Manna out of curiosity. I have graduated in robotics so I understand what real
   time is, I am good enough in C++. Add a section on the plugin code, use diagrams to
   detail it's working ( I am proficient in UML). Add detailed documentation on all the
   lean code (explain both syntax and specifics) : I never used it and I will learn it
   from there. I am fine spending time reading all this : make it easy and clear to me. In
   the end I want to be at ease talking to experts and answering questions about all this."

What the AI did:

- Wrote `docs/guide/` (8 Markdown files): background concepts, a section-by-section
  reading of the paper, one summary per bibliography entry, the plugin's architecture
  with Mermaid UML diagrams, a Lean tutorial, module-by-module Lean documentation, and
  expert questions with a glossary. Explanations of the paper, the Lean code and the
  plugin were written from the repository sources; the tool outputs quoted were produced
  by running `crosscheck-tool`; the Lean examples of the tutorial were type-checked; the
  Mermaid diagrams were parsed with Mermaid 11.4.1. **The summaries of the cited papers
  come from the model's general knowledge, not from reading the papers**; the guide says
  so and gives a confidence level per entry.
- While writing the bibliography summaries, found that `sinn2014complexity` had a wrong
  title and page range (introduced by the AI in the session of 2026-11-11). Corrected
  from the web (Springer PDF header, arXiv:1401.5842): "A Simple and Scalable Static
  Analysis for Bound Analysis and Amortized Complexity Analysis", CAV 2014, LNCS 8559,
  pp. 745–761, DOI 10.1007/978-3-319-08867-9_50. The paper was rebuilt (25 pages, no
  warnings). No other paper or Lean change.

Follow-up prompt (verbatim):

9. "I would like a PDF version so that I can load it in my ebook reader. Also clean up Lean
   comments as you suggested."

What the AI did: added `docs/guide/tools/build-pdf.mjs` (Markdown → HTML → PDF with
headless Chrome, Mermaid diagrams rendered, e-reader page size) and built
`docs/guide/crosscheck-guide-ebook.pdf` (gitignored); split or simplified the large
diagrams of Part 4 and the reference map of Part 3 so they stay legible on a small page.
In the Lean sources, changed **comments and docstrings only** (no definition, statement or
proof changed; `lake build` passes with no warnings): the root module doc now uses the
paper's current title, refers to the paper's table, and says which material (`⊑_sub`,
`⊑_graft`, `≼_O`) is kept but no longer used by the paper; docstrings in `Trace.lean`
refer to paper statements by LaTeX label instead of the old numbering ("Theorem 1",
"Definition 8", "Proposition 9/10"); "operadic" was dropped from `Tree.lean`;
`Dominance.lean`'s header and `FixedPoint.solution_soundness`'s docstring describe what
they actually contain.

### Session of 2026-11-13 (plugin CI, benchmark search)

Tool: Claude Code; model: Claude Opus 5.5 (`claude-opus-5-5`). Prompt (verbatim):

10. "Add the plugin build and at least some tests run to the github pipelines. Look for a
    known benchmark in this field that could be added to the paper results."

What the AI did: added `.github/workflows/plugin_build.yml` (Ubuntu 24.04 packages for
LLVM/Clang 18, Z3, GoogleTest; configure, build, full `ctest`, tool summary on
`benchmarks/`), checked in an `ubuntu:24.04` container (102/102 tests pass). Two changes to
`clang-plugin/CMakeLists.txt` were needed for distribution packages: a fallback when Z3
ships no CMake package file, and enabling the C language (LLVM's CMake config runs C
checks). Searched the web for benchmark suites (TACLeBench, Falk et al., WCET 2016;
Mälardalen, Gustafsson et al., WCET 2010; TPDB `Complexity_C_Integer` used by KoAT,
CoFloCo, Loopus) and ran a **pilot, not added to the paper**: the tool with `--all` on the
29 TACLeBench kernels (revision `4e4fbf7`, 2020-10-15, sources concatenated per kernel, no
annotations), comparing derived loop bounds with TACLeBench's `loopbound` pragmas. No
paper, bibliography or Lean change.

Follow-up prompt (verbatim), after the AI offered to add the comparison script and draft
the paper table:

11. "please do so"

What the AI did: added `benchmarks/tacle/run_tacle.py` and `benchmarks/tacle/README.md`
(results table and the reasons loops fail, classified by the AI by reading the
benchmark sources), a CI step running the script, and in the paper a subsection
`subsec:tacle` with Table `tab:tacle` (figures generated by the script; identical on the
author's machine and in an Ubuntu 24.04 container), plus consistent changes to the
Contributions item, the opening of Section "Prototype Implementation", the Limitations
paragraph "Evaluation", the Conclusions and the Statement on the Use of AI. Two
references added, `falk2016taclebench` and `gustafsson2010malardalen`, with bibliographic
data copied from the publisher's pages (DROPS, doi:10.4230/OASIcs.WCET.2016.2 and
doi:10.4230/OASIcs.WCET.2010.136); the AI read their abstracts, not the full papers. The
companion guide (Parts 2, 3, 7) was updated to match. One `\authortodo` was added.

Follow-up prompt (verbatim):

12. "I agree, compare with other tools if you can"

What the AI did: searched for analysers that can be installed and run. Ran, on the same
29 kernels and without annotations: LLVM 18 ScalarEvolution (constant max
backedge-taken count per loop, mapped to source lines through `!llvm.loop` debug
locations; `benchmarks/tacle/llvm_scev.py`), KoAT2 release v2.1.0 (official Docker
image, C front-end llvm2kittel, one function at a time with callees inlined, 60 s
timeouts; run in containers without network; `koat_in_container.sh`), and Infer v1.3.0
`--cost-only` (official release binary, run in a container without network). Raw answers
stored in `benchmarks/tacle/results/`; `compare_tools.py` computes the comparison. The AI
found and fixed a bug in its own LLVM mapping during the work (outer loops had been
attributed to inner loops' lines), and re-ran. It checked every function that CrossCheck
bounds and another tool does not: none is reported unbounded by KoAT2; the one Infer
misses (`bitcount_bit_shifter`) was read and CrossCheck's bound (64) is correct. In the
paper: a paragraph "Comparison with other tools" and Table `tab:tools` in subsection
`subsec:tacle`, with consistent changes to the Contributions item, Section "Prototype
Implementation", the Limitations paragraph "Evaluation", the Conclusions and the AI
statement. References added: `lattner2004llvm` (data checked on Crossref),
`falke2011termination` (checked on DROPS), `infercost` (tool documentation; its sentence
"We do not handle recursion" was read on the page). One `\authortodo` was added.
CI runs the ScalarEvolution comparison.

13. "I think that we should invest some more time in comparing other tools before we work
    on improving the precision of our plugin where it is lacking, what do you think we
    should be doing now ?"

What the AI did: answered with a plan, no changes: (1) check every bound against loop
counts observed by running the kernels, (2) a WCET loop-bound tool (oRange/OTAWA),
(3) CoFloCo on the integer programs already produced for KoAT2, (4) a second benchmark
set suited to complexity analysers (TPDB C integer programs). It also pointed out that
the data argue for context sensitivity before the precision items listed in
`CLAUDE.md`.

14. "I agree, proceed"

What the AI did: step (1). New `benchmarks/tacle/measure_loops.py`: instruments the
unoptimised LLVM IR of each kernel as text (a counter local to the function activation,
reset in the loop preheader and incremented in Clang's `for.body`/`while.body`/`do.body`
block) and runs the kernel on its built-in input, recording the largest number of body
executions per loop entry. `compare_tools.py` compares CrossCheck, ScalarEvolution and
the flow facts with these counts, and its new `--check` option (used in CI) fails if a
CrossCheck bound is below one. Result: 208 of 220 loops reached; no bound of CrossCheck
or ScalarEvolution below an observed count; flow facts equal on 198 loops and below by
one on two `while (1)`/`break` loops. Paper: three rows in Table `tab:tools`, sentences in
the paragraph "Comparison with other tools", the `\authortodo` there extended to the
instrumentation. The AI first misattributed the largest ratio (`minver`, 500/3) to an
array size; reading the source showed it comes from the test `side > 500`, and the text
was corrected before release.

15. "proceed with the next step"

What the AI did: step (2), oRange. Found its source on GitHub (`statinf-otawa/orange`,
LGPL-2.1, last change 2022-11-21); the FrontC on GitHub under the same organisation is a
different fork (BAP's) and does not build oRange, so FrontC was cloned from IRIT's
repository (`git.renater.fr/.../orange/Frontc.git`, 2023-11-17). Built with OCaml 4.14
in an Ubuntu 24.04 container, saved as a local image, and run per kernel in containers
without network (`orange_in_container.sh`). oRange reads `loopbound` pragmas, so they are
blanked (line numbers kept) before each run, and the script refuses to run if one is
left. Results stored in `benchmarks/tacle/results/orange/`; `compare_tools.py` reads
them. One oRange bound is below the observed count (`filterbank`, `while (n-- > 0)` with
n = 2: reported 1, runs 2); the AI read the source to confirm. Paper: oRange column in
Table `tab:tools`, sentences in "Comparison with other tools", reference
`demichiel2008orange` (data checked on Crossref, DOI 10.1109/RTCSA.2008.53).

16. "proceed with step 3 too"

What the AI did: step (3), CoFloCo. Its repository (`aeflores/CoFloCo`, GPL-3.0) ships a
front-end (`interfaces/C2ces`) converting llvm2kittel's integer programs into cost
equations. The AI regenerated those programs with the KoAT2 image's llvm2kittel and the
same options as for KoAT2 (`its_in_container.sh`; 202 programs, as many as KoAT2
analysed), then ran the author's Docker image `afloresmontoya/cofloco` on them without
network (`cofloco_in_container.sh`, default cost model, 60 s per step). Answers stored in
`benchmarks/tacle/results/cofloco/`. Because KoAT2 and CoFloCo count the same unit on the
same programs, `compare_tools.py` also compares their numeric bounds. The AI checked the
one function CoFloCo bounds and KoAT2 reports "Infinity" (`md5_R_RandomInit`) by reading
its integer program. Paper: CoFloCo column in Table `tab:tools`, sentences in "Comparison
with other tools", reference `floresmontoya2014cofloco` (checked on Crossref; the LNCS
volume number was not given there and is omitted). The paper is now 29 pages.

17. "proceed with step 4"

18. "ok, finish step 4 when the tools are done"

What the AI did: step (4). New `benchmarks/tpdb/`: `run_tpdb.py` fetches TPDB's
`Complexity_C_Integer` (553 programs, pinned revision) and runs CrossCheck in two modes:
unchanged, and with input ranges [-1000, 1000] added by a script to every `int`
parameter and every value assigned from an undefined (nondeterministic) function, with
unit cost for those functions. The AI chose this harness because CrossCheck has no
symbolic bounds; the bounded mode is compared with the other tools only on whether a
bound is found. `tools_in_containers.sh` runs KoAT2 and CoFloCo on all programs
(network-less containers, same scripts as TACLeBench). Results: CrossCheck 10 (as is) and
141 (ranges), KoAT2 288, CoFloCo 264. The AI read the 7 programs bounded only by
CrossCheck: 6 are bounded only because the harness also restricts values chosen inside
loops (the other tools are right to report no bound), 1 is a timeout of both tools. It
read a random sample of 10 of the 171 programs bounded by KoAT2 or CoFloCo and not by
CrossCheck, and debugged one (`speed_popl10_sequential_single`: `x >= 0` is lost after a
loop that may exit by `break`). During the work the AI found a naming bug in its own
script (reports looked missing for 170 programs) and fixed it before using any figure.
Paper: paragraph "Complexity benchmarks" in `subsec:tacle`, updated Contributions and
Limitations, reference `giesl2019termcomp` (checked on Crossref), one `\authortodo`.
`CLAUDE.md`'s precision priorities were reordered from these results.

From here on the model is Claude Fable 5.2 (`claude-fable-5-2`), same tool.

19. "What does this all says to us about CrossCheck, is it any good at anything ? Can it
    be further improved ?"

20. "Let's keep talking about this a bit more : I would like to implement all your ideas
    but I think we should split those in two parts : the ones that could, and should, be
    integrated into theory and have lean formalisation done and the rest that cannot be
    integrated in the theory in a smooth way, that might seem engineering hacks. What do
    you think ?"

What the AI did for 19 and 20: answered, no changes (an assessment from the benchmark
figures, and a split into new kinds of certificate, which need theory and Lean, and
better ways to find what existing certificates need).

21. "Proceed with the improvement of the project as suggested : paper, lean code, guide
    and plugin code"

What the AI did (first milestone only; **stopped before finishing, see below**):
- Plugin: calling contexts (a callee is re-analysed with the Z3-derived intervals of its
  integer arguments, joined over all states in which the call is evaluated; never for
  self-recursive functions; at most 8 per function); every statement now evaluates
  before costing; one exit state per `break` path plus the guard exit; interval join in
  `mergeStates`; `v = v + c` recognised as an increment for invariant candidates;
  `boundsOf` in the solver; report fields `in_context`, `contexts`, `wcet_in_context`,
  option `entry=NAME`. The AI chose interval contexts instead of the symbolic
  summaries it had proposed, because costs in the analyser are numbers; symbolic bounds
  are not done. 120 tests pass (18 new, 7 of them must-reject cases).
- Lean: `run_invariant`, `ranking_bound_floor_of_invariant`, `ranking_bound_of_context`,
  `call_bound_of_context` in `Certificate` (141 theorems, builds with no warnings).
- Paper: Proposition `prop:context-bound` with proof, paragraph "Calls", Table
  `tab:lean` row, line and theorem counts. Guide Parts 2, 4, 6; plugin README;
  `formalization.yaml`.
- Measured (scripts updated, `results/comparison.json` and `results/tpdb.json`
  refreshed): TACLeBench 126 loops bounded for every call (was 124), 137 in the contexts
  reached from `main` (128 equal to the flow fact; none below an observed count), 9
  entry functions (was 8); TPDB with ranges 165 programs (was 141), as is 10.
- After an interruption (usage limit), the same prompt was continued: the figures of
  Tables `tab:tacle` and `tab:tools`, the paragraphs of `subsec:tacle` (including the
  TPDB paragraph) and the plugin line counts in the paper were brought in line with
  the new runs, as were `benchmarks/tacle/README.md`, `benchmarks/tpdb/README.md`, the
  guide (Parts 2 and 7) and `CLAUDE.md`. Every figure now says whether it is a bound
  for every call or a bound in context. The example-program figures (`tab:plugin`)
  were re-checked and are unchanged. The paper is 31 pages. Symbolic bounds, global
  variables, new potential shapes and float loops are not done.

22. "I would like you to work on theory and lean first. Before that, I would like you to
    answer a few important questions honestly : - now that you have a comparison with
    existing tools and benchmark results, do you think that there is a concrete
    engineering advantage for the industry in crosscheck or not ? If yes, which one ? If
    not, could this be fixed, and how ? - is there a concrete scientific interest in the
    theory described in the paper, with respect to the state of the art in the field ? If
    yes, describe which one, if not, is there anything that should be done ? - is it
    possible and usefult to include concurrency and parallelism constraint
    (multithreading, multiprocessing) in the theory ? - is the paper too long and complex
    for a single article, should it be split in different publications ? If yes, how ? -
    after this part will be completed and the author todo removed, would you suggest
    publishing it on arxiv or there should be more work done ? - what would be the next
    evolution that you would suggest that would improve this work, both on theorical and
    implementation point of vues ?"

What the AI did: answered, no changes. Its assessment, in short: no decisive industrial
advantage today and little theoretical novelty (the ingredients are classical); both
could come from a language-level soundness theorem plus certificates checked by a
verified checker; concurrency only as a remark (work/span); split the paper in two
before a venue submission; arXiv is reasonable once the author has verified everything,
the claims about other tools are confirmed and the artifact is archived.

23. "Let's go for the small language route first, then treat all other suggestions you
    gave, I fill follow your lead. I aim for industrial value and scientific innovation.
    Also check the bibliography to make sure it does not only comes from your memory, if
    it is in the scope of your abilities. Feel free to commit and push now or later on.
    Thank you for your valuable advice."

What the AI did:
- Committed and pushed the state so far on branch `evaluation-and-contexts`.
- Lean: new module `Language` (425 lines, 16 theorems): commands with weighted relational
  atoms, cost semantics for terminating executions (`Exec`) and for execution prefixes
  (`Pre`), valid triples, the rules, the proof system `Derivable` and `soundness`;
  symbolic bounds (`ValidSym`, `validSym_call`, `validSym_seq`); an example with a
  derivable bound. Totals: 13 modules, 157 theorems, standard axioms only, no warnings.
  The design (prefix costs to cover divergence; symbolic bounds encoded by a budget) is
  the AI's.
- Paper: subsection `subsec:cost-logic` (definitions, Theorem `thm:cost-logic-soundness`
  with a proof, Proposition `prop:summary-call`), a Contributions item, rows of Table
  `tab:lean`, the scope list, the AI statement; an `\authortodo` on the relation to
  Nielson and to Haslbeck and Nipkow. 33 pages.
- Bibliography check, by script: every entry with a DOI was fetched from Crossref and
  compared (title, authors, year, pages); entries without DOI were searched on Crossref;
  the four Dagstuhl DOIs were fetched from DataCite; six books were looked up on Open
  Library; the three web pages return HTTP 200. DBLP refused automated queries. Result:
  all entries confirmed except `matiyasevich1970enumerable` (only a reprint is indexed).
  One error fixed (`blazy2013formal`: year 2014). 24 DOIs added. New entry
  `nielson1987hoare` (from Crossref). The content of the papers was not read.

24. "Proceed with the order as you see fit. I would like you to also read cited paper
    contents (and if possible download them somewhere in this repository) when they are
    available. I wish that this plugin would allow to check real industrial code in C /
    C++ (and later on, another plugin for rust) for architectures used in real-time
    applications (in this case, maybe even temporal checks and some basic parallelism
    could be integrated ?). I would like that standard libraries with explicit complexity
    constraint and declared time behaviour would be accepted (such as std library in
    C++), what do you think ?"

What the AI did: new folder `references/` with `fetch_papers.py`, which downloads the
open-access copies of the cited papers (21 of 50 entries) into a gitignored folder; the
PDFs are not committed because most are under publisher or author copyright. The AI
read abstracts, and for a few papers the sections the text relies on; what was read and
checked is listed per entry in `references/README.md`. Two statements of the paper were
corrected after reading: TACLeBench is no longer called "the successor of" the
Mälardalen benchmarks (the article lists several sources), and the comparison with
Haslbeck and Nipkow in `subsec:cost-logic` now states what their paper does (three
logics for deterministic IMP, sound and complete, triples assert termination). Nielson
1987 was not obtained; the `\authortodo` now names it. The AI also answered the
questions on industrial use (see the conversation); no code was changed for them.

25. "Implement the theory part of your plan (theory, paper, lean), read the papers as you
    feel a need for it. I want to swith to Opus for implementation once the foundations
    are set."

What the AI did (design choices are the AI's):
- Lean `Language`, rewritten: commands gain `call`, with procedure bodies in an
  environment `Φ` (recursion allowed); `Derivable` gains a set `Γ` of assumed triples
  (contracts), a dead-code rule, and a call rule for a ranked family of triples
  (recursion, mutual recursion); `soundness` is relative to the validity of `Γ`;
  example of a recursive procedure with a derivable bound (`down_cost`).
- Lean `Checker` (new, 477 lines): affine expressions and constraints over program and
  logical variables, Farkas certificates, annotated programs `ACmd`, an executable
  `check`, and `check_sound` / `certified_cost_le`; an example certificate accepted by
  `decide`. The use of logical variables for the loop rule, and the certificate layout,
  are the AI's design.
- Lean `Certificate`: `lex_ranking_bound`, `log_ranking_bound`.
- Totals: 14 modules, 185 theorems, about 3,300 lines, no warnings, standard axioms only.
- Paper: `subsec:cost-logic` extended (calls, rules 7 to 9, relative soundness, a
  paragraph on weights, architectures and parallel composition, not formalized); new
  `subsec:checker` (Definition `def:certificate`, Theorem `thm:checker-soundness` with
  proof); Proposition `prop:lex-log` with proof; Contributions, Table `tab:lean`, scope
  list, Conclusions, AI statement. 37 pages.
- References added, data from Crossref, content **not** read: `necula1997proof`,
  `nipkow2002hoare`, `blumofe1999scheduling` (an `\authortodo` says so).
- `docs/implementation-plan.md`: what is proved, the certificate format, and the ordered
  implementation tasks, for the implementation phase.
- No plugin code was changed in this step.

From here on the model is Claude Opus 5.5 (`claude-opus-5-5`), same tool.

26. "proceed with the next implementation phase as indicated"

27. (sent while the AI was working) "Once you have finished all the remaining tasks, I
    would like you to consider splitting the paper in two as discussed previously. Also,
    please update the guide with the latest developments; if you can, make it a bit
    shorter (without losing what is needed to learn and understand) maybe using more
    diagrams and less text ? After that, propose improvements to augment scientific
    relevance and innovative contibution as well as industrial value and engineering
    interest, maybe extending the subset of the language so that a larger part of legacy
    codebase can be handled ?"

What the AI did for 26 (tasks 1 and 2 of `docs/implementation-plan.md`):
- Lean: the checker's definitions moved to `CheckerCore.lean` (no mathlib) so that they
  can be compiled; `CheckerMain.lean` reads JSON certificates and runs `check`
  (`lake build crosscheck-check`); test certificates (one accepted, three rejected).
  The proofs (`Checker.lean`) are unchanged in substance.
- Plugin: `src/core/Cert.{hpp,cpp}` (dense constraints reproducing the checker's vector
  operations, Fourier-Motzkin elimination, Farkas multipliers by Z3, JSON); certificate
  generation in `Analyzer.cpp` (lowering, forward assertions, Houdini invariants, the
  analysis' potentials, call inlining in the calling context, restructuring of early
  returns, a relevance filter on variables); option `certificates=FILE`; report fields
  `certificate`, `certificate_bound`; 6 new tests and a ctest that runs the Lean checker
  on the examples' certificates.
- Results: TACLeBench 142 of 158 bounded functions certified, all 142 accepted by the
  checker; examples 7 of 13. The AI investigated the four certified bounds that are
  smaller than the plugin's (`__kernel_cosf`) and found an infeasible path excluded by
  the certificate's assertions, not a missing cost.
- CI: the Lean workflow builds and runs the checker; the plugin workflow emits the
  certificates and a second job checks them.
- Paper: paragraph "Certificates" and figures in the prototype section, "Trust"
  rewritten, scope list updated; `docs/certificate-format.md`; plugin and TACLeBench
  READMEs; `CLAUDE.md`; `docs/implementation-plan.md` (tasks 1 and 2 done).

What the AI did for 27:
- Tasks 3 to 8 of the implementation plan were **not** done in this session (each is
  weeks of work); the AI moved to the requested deliverables and covered the rest in its
  proposals (`docs/proposals.md`).
- Paper split (2026-11-14): `paper/theory/crosscheck-theory.tex` (Paper I: theory and
  Lean, 30 pages) and `paper/tool/crosscheck-tool.tex` (Paper II: the plugin,
  certificates and the evaluation, 11 pages), sharing `paper/crosscheck.bib`. The text of
  the sections was moved, not rewritten, except: both abstracts, Paper II's
  introduction and its "Background" section (a summary of Paper I's results with
  references to their numbers through `xr`), the conclusions of both papers, Paper I's
  contribution list and evaluation paragraph, Paper II's limitations and AI statement.
  `\authortodo` marks were kept with the text they belong to; Paper II's AI statement has
  a new one. Both compile with no warnings. The combined `paper/crosscheck.tex` was removed
  (it is in git history).
- Guide rewritten and shortened (4,660 → 1,138 lines; 12 → 19 diagrams; 7 parts, the
  Lean tutorial and module parts merged, a new part for Paper II, the bibliography as a
  map with what was read). Content updated for the cost logic, the checker, the
  certificates and the split.
- Proposals (the last request of 27): `docs/proposals.md`, with the argued order of the
  next steps; written by the AI from the measurements of this session.

28. "Proceed with the order you recommend"

What the AI did for 28 (step 1 of `docs/proposals.md` §5; design choices are the AI's):
- Lean: a checker node `whileAnd` (loop whose test is a list of linear constraints,
  postcondition the invariant alone) in `CheckerCore.lean`, its case in the proof of
  `check_sound` (`Checker.lean`), parsing and printing in `CheckerMain.lean`; one more
  accepted and two more rejected test certificates; still 185 theorems, about 3,500
  lines, no warnings. The CI step now fails if any certificate of
  `count_rejected.json` is accepted (before: only if all were).
- Paper I: Definition `def:certificate`, the description of the checker, the proof of
  `thm:checker-soundness` and the remark after it mention the conjunctive loop and how
  early exits can be expressed with it. **Author to check** that this text says what
  `check` does for `whileAnd`.
- Plugin (certificate generator only; the analysis is unchanged except for the
  reported loop bounds below): `break`, `continue`, `return` inside loops by flag
  variables and the potential `pot + c·(1 − Σ flags)`; `switch` as nondeterministic
  conditionals per group of cases; `&&` loop tests; unsigned variables with an explicit
  wrap-around test whose wrapping branch the checker must prove dead; join hints so
  that inner loops keep the outer loops' ghost constraints. A crash of the generator
  (a callee's `return` inlined inside a caller's loop) was found by the AI on the example
  programs and fixed; the ctest that runs the checker now fails when the tool crashes.
- Reported loop bounds now count executions of the body in two cases where they
  counted one less: `do … while` loops, and loops left by `break`/`return` whose
  potential is not proved ≥ 1 at the start of the leaving iteration (found on
  TACLeBench `lift`: `while (1) { …; if (i++ >= 1000) break; }`, 1001 executions, reported
  1000). Cost bounds were not affected (the cost rules already counted these bodies);
  the TACLeBench kernel figures (`tab:tacle`, `tab:tools`, observed counts) were re-run
  and are unchanged.
- Results: TACLeBench certificates 156 of 158 bounded functions (before 142), all
  accepted; examples 10 of 15 bounded functions. Tests: 128 pass.
- TACLeBench sequential and app categories (25 programs, 572 loops) run for the first
  time: 263 loops bounded for every call (252 = flow fact), 317 in context (297 =); the
  AI inspected the 5 in-context bounds below a flow fact in the sources (two `sizeof`
  flow facts that overstate, three loops in branches that cannot run); certificates
  232 of 252 bounded functions, all accepted. New paragraph in Paper II and section in
  `benchmarks/tacle/README.md`. **Author to check** that classification.
- `run_tacle.py`: `--category` (kernel, sequential, app); counts of smaller certified
  bounds and the reason for each uncertified function; `-Wno-error=implicit-function-declaration`
  (some programs call `printf` without a declaration).
- Documents updated: Paper II (certificate paragraph, figures, conclusions), plugin and
  TACLeBench READMEs, `docs/certificate-format.md`, guide parts 3, 4, 5 and 7,
  `docs/proposals.md`, `docs/implementation-plan.md`, `CLAUDE.md`.

29. "yes please make these changes as you suggest" (after the user asked: "I wonder if
    bibliography should be shared between the two papers : I suspect (your call) that most
    theory-oriented bibliography should go in Paper I and the more technical one in Paper
    II, what do you think ?", and the AI proposed keeping one `.bib` and moving the
    tool-side related work to Paper II)

What the AI did for 29: the shared `crosscheck.bib` is unchanged (each paper lists only
what it cites). Paper I: the paragraph "Compile-time real-time checks" moved to Paper II.
Paper II: new section `sec:related` (bound analyzers, WCET flow analysis, verified and
certified bounds, compile-time real-time checks), citing entries already in the
bibliography and already checked; Lean 4 cited where the checker is introduced; an
`\authortodo` lists the works whose content was not read or only from abstracts. Paper I
now 29 pages and 45 references, Paper II 13 pages and 28 references.

30. "I propose to proceed with step 2: exporting loop bounds to WCET tools (aiT, OTAWA,
    SWEET) and CI/SARIF integration"

What the AI did for 30 (design choices are the AI's; no Lean or theory change):
- Formats researched from sources, not from memory: FFX from Bonenfant et al. (RTNS 2012,
  sections 3-4 read) and from OTAWA's loader `src/prog/flowfact_FlowFactLoader.cpp` (read
  partly verbatim, partly through a fetch tool's summary); AIS from the AbsInt white paper
  of Heckmann and Ferdinand (section 4 read); AIS2 only from one example in AbsInt's a³
  15.10 release notes and the CompCert manual (section 6) — the AIS2 grammar is not
  public. SARIF from the OASIS schema. SWEET was dropped: no public input format for loop
  bounds was found, and SWEET computes flow facts itself.
- Plugin: `src/analysis/Export.{hpp,cpp}` (FFX, AIS, AIS2, SARIF), options `flowfacts`,
  `flowfacts-format`, `flowfacts-context`, `sarif`, `sarif-base`; the report gains loop
  file/column, error locations and linker names; `scripts/cost_diff.py` (cost diff,
  snapshots); `benchmarks/bounds-baseline.json`; tests `Export.*`, `exports_read_back`
  (SARIF validated against the schema), `bounds_equal_baseline`; 135 tests pass. CI
  downloads the schema, uploads the exports and writes the cost diff to the job summary.
- `benchmarks/tacle/compare_ffx.py`: CrossCheck's in-context FFX equals oRange's FFX on all
  114 loops both bound.
- Not done: the files were not loaded into OTAWA or aiT (they need compiled binaries;
  aiT is commercial). The aiT loop numbering (source order) is a stated caveat.
- Bibliography: `bonenfant2012ffx` (Crossref), `heckmann2013ait` (the PDF read; undated),
  `sarif2023` (OASIS page). Paper II: paragraph "Exports", a sentence in the kernel
  results, related work and future work updated (14 pages). READMEs, guide, proposals,
  implementation plan, `references/README.md`, `CLAUDE.md` updated.

31. "proceed with step 3: modular symbolic certificates and library contracts"

What the AI did for 31 (design choices are the AI's):
- Lean (`CheckerCore`, `Checker`): symbolic bounds `SB` (`c + Σ co_j·max(0, γ_j)`, natural
  coefficients, compared coefficient by coefficient); loop nodes with a symbolic entry
  bound and the condition `loopBoundOk` (symbolic entry with constant body, or constant
  entry with symbolic body: bounds stay affine); a `call` node (instantiation of the
  callee's logical variables by argument expressions, its precondition and the argument
  bounds by Farkas certificates, frame = facts not mentioning the callee's variables);
  program certificates `FunCert` with assumed contracts (no body), `checkProgram`.
  `check_sound` now proves the frame too and holds relative to the callees' `FunSpec`;
  `program_sound` (strong induction over the functions, contracts as hypotheses). Examples
  by `decide`: a symbolic loop, a two-function program with a call (18 accepted, 17
  rejected), and `exMain_cost` through `program_sound`, so that the hypotheses are met in
  one example. 208 theorems, standard axioms only, no warnings.
- Checker program: certificate format version 2 (programs, contracts printed `ASSUMED`, a
  `PROGRAM` verdict); version 1 still read (all earlier TACLeBench certificates accepted);
  test files `program.json` and `program_rejected.json` (bound too small, wrong argument
  facts, argument bound too small, undeclared writes), checked in CI.
- Plugin: one program certificate per translation unit; parameter ghosts; summaries by a
  test-derived potential tried before the analyser's, symbolic entry bounds by
  Fourier–Motzkin projection (`symbolicUpper`), kept only when no looser than the constant
  bound at the largest admissible parameters; call nodes for functions certified earlier;
  contracts for `CROSSCHECK_COST` and for a new contract file (`contracts=FILE`,
  `docs/contracts.md`, costs linear in the arguments, listed as assumptions); report field
  `certificate_summary`. Two regressions found by the AI on the examples and fixed before
  measuring (a looser test-derived potential in `plan_ramp`; ranges not yet in the
  precondition when the largest parameter values were computed).
- Paper I: Definition `def:program-certificate`, Theorem `thm:program-soundness` with
  proof, `def:certificate` and `thm:checker-soundness` extended, Table `tab:lean`, scope
  list; `formalization.yaml`. **Author to check** these against the Lean code. Paper II:
  certificate paragraph (summaries, call nodes, contracts) and trust paragraph.
- Not done: the analyser itself still needs numeric ranges (no symbolic bounds for
  unannotated code, so the TPDB gap "as is" remains); recursion in the checker; polynomial
  bounds.
- Results (re-run with a frozen copy of the tool): TACLeBench kernels unchanged (156 of 158
  certified, all accepted), 120 calls checked against summaries; sequential/app 232 of 252,
  169 calls; TPDB with input ranges: 125 of the 165 bounded entry functions certified, all
  accepted, 92 with a summary in their parameters (KoAT2 linear for 67 of them), 39 contract
  entries; examples 11 of 15 bounded functions, 3 with a summary. 138 tests pass.

32. "Proceed with step 4"
33. (sent while the AI was working) "try again, continue what you were doing"
34. "proceed with the next step"

What the AI did for 32-34 (step 4 of `docs/proposals.md` §5; design choices are the AI's):
- Code base: CMSIS-DSP (Arm, Apache-2.0) and CMSIS 6 Core, pinned, fetched into a
  gitignored cache, analysed for a Cortex-M4 target with generated freestanding stubs
  (`benchmarks/cmsis/run_cmsis.py`). The blockers were measured first and drove the work.
- Plugin (analysis): annotations usable in C; target intrinsics, straight-line statement
  expressions and inline assembly costed (assumptions); `input-range=LO,HI` (assumption);
  fields read through pointer parameters as entry symbols (assumption: not modified while
  the function runs); globals and static locals tracked (assumption: no interrupt, thread,
  bodiless function or inline assembly writes them), cleared after calls that may write
  them, also inside loops; constant tables; C integer tests as `!= 0`; absolute-bound
  invariant candidates for variables modified by the loop test (`while (--j)`); C++
  pre-increment lvalues. A performance regression (`cjpeg_transupp` > 30 min) was found by
  the AI on the benchmark campaign, bisected to these candidates and fixed (100 s).
- Lean: checker node `havocC` (an unknown value with constraints), proof case in
  `check_sound`, examples `shiftCert_checks` / `shiftCert_rejected`; 215 theorems.
  Plugin certificates: `havocC` for shifts, divisions, remainders, masks and table reads,
  shared variables for globals, field variables, scaled potentials for fractional
  summaries (`blockSize >> 2`). Paper I: the constrained atom in the linear instance and
  the checker description.
- Tests: 149 (must-be-rejected: callee resetting a global, escaped global, volatile limit,
  written field, `--j` from 0; a C-language test).
- Results: TACLeBench kernels 127 / 138 loops (every call / in context; were 126 / 137),
  entry functions 10 (were 9), certificates 158 of 160, no bound below an observed count,
  in-context bounds equal to oRange's on all 114 common loops; sequential/app 273 / 328
  (were 263 / 317), the 10 in-context bounds below a flow fact all checked by the AI in the
  sources (dead branches, overstated facts); TPDB 166 with ranges (was 165); CMSIS-DSP 161
  functions as is, 616 of 786 with ranges and context (357 before the step).
- Not done: pointer iterators (no measured need in these code bases); logarithmic loops.
- Documents: Paper II (implementation, results, a paragraph on CMSIS-DSP, limitations),
  READMEs (plugin, tacle, tpdb, new cmsis), certificate format, guide, proposals,
  CLAUDE.md. **Author to check** the new assumptions' wording and that the CMSIS-DSP
  harness (ranges, context, illustrative contracts) is a fair way to report coverage.

35. "try again now" (after an interruption by a usage limit)
36. "proceed with step 5"

What the AI did for 35-36 (step 5 of `docs/proposals.md` §5, "verified lowering"; the
design is the AI's): instead of writing the lowering from C in Lean (the plan of S1), the
AI chose **translation validation** (Pnueli, Siegel and Singerman 1998; Necula 2000): a
second, syntactic translation of each function into a small subset of C, mini-C, whose
meaning is defined in Lean, is compared by the checker with the program of the certificate.
Reason given: it removes the generator (the largest unverified part) from the trusted base
without re-implementing its search in Lean, and leaves a translation short enough to read.
- Lean: new modules `MiniCCore` (no mathlib: `MExp`, `MCond`, `MStmt`, `lower` (the
  meaning of mini-C), the normal form `nf`, `validate`) and `MiniC` (`CImp`/`CEquiv`,
  congruences for sequences, conditionals and loops, `seq_assoc`, `nf_equiv`,
  **`validated_sound`**; examples `countCert_validated`, `countCert_not_validated`);
  `deriving DecidableEq` on `ACmd`; 239 theorems (24 new), standard axioms only.
- Checker program: reads an optional `"source"` per function, prints `VALIDATED` / `NOT
  VALIDATED` (exit status 1), `--print` shows both normal forms on a mismatch; test files
  `test/certificates/minic.json` and `minic_rejected.json` (four wrong sources), in CI.
- Plugin: option `minic`; exporter `src/analysis/MiniC.cpp`, independent of the generator
  (inputs: the variable numbering and the cost model); dead-code nodes now contain the code
  that is not reached (with `minic`; loops there get the potential 0, since nothing inside
  a dead node is checked). The exporter refuses what it does not model exactly (calls,
  jumps inside loops, unsigned/global/static/volatile/aliased tracked variables, division,
  shift, mask and table forms). While building it, the AI found that the generator
  describes masks and remainders by facts (`havocC`) that mini-C does not have: these
  functions are refused rather than reported as mismatches. Test `minic_sources_validated`
  (`tests/c/minic.c`: `ok_*` must validate, `no_*` must not); 150 tests pass.
- Results (frozen binary): TACLeBench kernels: tables unchanged; 158 of 160 certificates,
  all accepted; 93 validated, none fails validation, 26 of them with loops (42 of the 82
  loops of the certified programs), 3 entry functions; 65 refused (calls 31, division
  forms 19, unsigned 8, global or static 6, `break` 1). Sequential/app: tables unchanged
  (231 of 263 certified, all accepted); 113 validated, none failing; refused: calls 41,
  globals/statics 24, division forms 25, unsigned 19, jumps and `switch` 9. TPDB was not
  re-run with `--minic` (the option was added to `run_tpdb.py`).
- Papers: Paper I subsection `subsec:validation` (Definition `def:minic`, Lemma
  `lem:nf-equiv`, Theorem `thm:validated` with proofs), Table `tab:lean`, contributions,
  scope list, AI statement; Paper II: introduction, paragraph "Validation against the
  source", trust paragraph, kernel results, related work, limitations, conclusions; two
  new references checked on Crossref (`pnueli1998translation`, `necula2000translation`;
  content not read). **Author to check** (see §3, item 24).
- Not done: calls in mini-C (needs a congruence of the semantics in the procedure
  environment, and the exporter would have to follow the generator's choice between a
  summary and inlining); unsigned arithmetic, division and masks in mini-C; jumps in loops.

37. "proceed with step 6"

What the AI did for 37 (step 6 of `docs/proposals.md` §5 has three parts; the AI chose the
order S6, S5, I6, and did S6 first; design choices are the AI's):
- Lean: `ResponseCore` (no mathlib: `rtaHolds`, `rtaSearch`), `Interrupts` (schedule model
  `Admissible`, `sporadic_count`, `handler_demand`, `response_time_bound`, `rtaHolds_sound`,
  examples incl. an admissible schedule, so that the hypotheses are satisfiable),
  `ForkJoin` (`Greedy`, `greedy_bound` = Graham's bound, `forkjoin_bound`, `load_lower`);
  260 theorems. Both results are classical (Joseph and Pandya 1986, Audsley et al. 1993,
  Graham 1966); the papers say so and cite Prosa (Cerqueira et al. 2016) as the general
  mechanization.
- Checker program: `"responses"` claims (task and handlers must be accepted with constant
  bounds); tests `response.json`, `response_rejected.json` (four wrong claims), in CI.
- Plugin: `CROSSCHECK_INTERRUPT(T)`, option `interrupt-overhead=N`, `response_time` in the
  report and `--summary`, deadlines checked against it, claims in certificate files with
  the certified bounds; tests `Interrupts.ResponseTime`, `Unsound.DeadlineMissedUnderInterrupts`,
  `Unsound.InterruptWithoutPeriod`, `tests/certificates/interrupts.cpp`.
- Papers: Paper I subsection `subsec:concurrency` (Definition `def:interrupt-model`, Lemma
  `lem:sporadic`, Theorem `thm:response-time`, Proposition `prop:graham`, with proofs),
  contributions, table, scope; Paper II paragraph "Interrupts". New references checked on
  Crossref: `joseph1986finding` (Crossref lists only M. Joseph; the co-author P. Pandya is
  from the AI's memory), `audsley1993applying`, `graham1966bounds`, `cerqueira2016prosa`;
  content not read. **Author to check** (§3, item 25).
- Not done in S6: the busy-period argument; fork-join in the plugin; task graphs.
- S5 (time on a predictable core), done after S6 in the same prompt: `benchmarks/cycles`
  (`m0.py`: ARMv6-M decoder, Cortex-M0 timing table from the AI's knowledge of the Arm
  Technical Reference Manual, an ELF loader and an interpreter; `wcet.py`: CFG of the
  binary, natural loops matched to source loops by debug lines, timing schema;
  `run_cycles.py`; `runtime.c`: integer division for the M0, so that CrossCheck bounds
  it; `test_m0.py` + `selftest.c`: self-test of the interpreter against C semantics). The
  AI first tried to install the `unicorn` emulator and `pyelftools` with pip into a scratch
  venv; the action was denied by the session's permission policy, and the AI wrote its own
  interpreter instead (no external package). While debugging, the AI found that TACLeBench
  `fft` converts negative floats to `unsigned long` (undefined behaviour), so it fails its
  own check on Arm; it is listed as an expected failure. Results: see Paper II and
  `benchmarks/cycles/README.md`. **Author to check** the timing table against the TRM
  (§3, item 26).
- I6 (Rust): first left out (MIR only as unstable text); done after prompt 38, see below.

38. "proceed with rust, even if the interface may evolve with time"

What the AI did for 38 (design choices are the AI's):
- Rust front-end on the textual MIR of rustc 1.100.0 (`frontends/rust/mir2c.py`): the MIR
  of each free function is translated into C, which the existing analyser bounds and
  certifies; loops rebuilt as `while` loops from the tests at their head, conditionals by
  immediate post-dominators. Semantic choices (in its README and Paper II): wrapping
  operations on unsigned C types; checked arithmetic as plain C arithmetic (bounds for the
  executions that do not panic); other assertions and panics as early returns (more
  behaviours in C, so the bounds carry over), which makes `assert!` a run-time-checked
  input range.
- Tests (`frontends/rust/tests/test_rust.py`): differential test against Rust (382 runs,
  no mismatch), must-be-unbounded functions; CI step with the toolchain pinned. Results:
  11 of 12 example functions translated, 6 bounded, 3 certified (1 validated), the 4
  `rejected_*` not bounded. The translation is not verified.
- Paper II paragraph "Rust"; docs. **Author to check** (§3, item 27).

39. "proceed with the next step"
40. "proceed with the next step" (sent again while step 7 was being measured)
41. "proceed with the next step when you are ready, do not forget to update the guide too"
42. "I would like to switch to the Fable model, can I do it now or should I wait for the background tasks to terminate ?"
43. "While we wait for the background runs to complete to finalize step 8 of the current improvements, I would like you to read once again the papers, the guide, analyze lean theorems, the clang and rust implementations with these main objectives :
- make sure that the research work is solid and complete
- plan to further improve the scientific relevance and innovative contribution
- plan to increase as much as possible the industrial value, engineering interest and widen applicability to legacy or future code
- get better results on benchmarks and with respect to existing tools comparison
Give me any advice about how to proceed : how to make this project really useful for a big company such as Safran, Dassault, Thales, Airbus or others ? What would you do now ?"

44. "Write your advices into docs/proposals.md then go on with step 9 and follow up with all your advices, one by one, without stopping to ask anymore until all you can think of has been done."
45. "I am building otawa right now and I will find some time later for reviews. There are some authortodo tasks that you should be able to complete yourself, please check them since my time is very limited and I am busy reviewing the guide and the paper. Proceed improving the paper, lean and implementations while otawa builds"

What the AI did for 45 (Claude Fable 5.2, 2026-11-16). The `\authortodo` marks of both
papers were taken one by one. A mark was removed only where its check could be done by a
script, by a comparison with a document that was obtained and read, or by a line-by-line
comparison of a definition with the Lean source; the checks are the AI's, not the
author's, and section 3 below says for each item what was done and what is left. Nothing
in the papers says that the author verified anything.
- **Paper I against Lean** (three marks). `def:certificate`, `def:program-certificate` and
  the description of the checker were compared with `ACmd`, `check`, `checkProgram`,
  `FunSpec`, `check_sound` and `program_sound`; `def:minic`, `lem:nf-equiv` and
  `thm:validated` with `MStmt`, `lower`, `nf`, `validate`, `nf_equiv`, `validated_sound`;
  `def:interrupt-model`, `thm:response-time` and `prop:graham` with `Interrupts.lean` and
  `ForkJoin.lean`. Differences found:
  - **Lean was weaker than the paper in one place**: `Handlers.rel` was a `Finset`, so an
    admissible schedule could contain only finitely many handler activations (a periodic
    interrupt that never stops was excluded, although the theorem only looks at the first
    `R` slots). `rel` is now a `Set`, `before rel t` is the finite set of activations
    released before `t`, the proofs are adapted, and `perRun_admissible` /
    `perRun_completes` give an example with a handler activated forever.
  - The paper said that `W/p` and `S` are lower bounds for every schedule; Lean proved it
    for greedy schedules only. `ForkJoin.makespan_lower` now proves it for every assignment
    of tasks to processors.
  - Paper text made precise, with no change of meaning intended: `floor(k/d)` read as 0
    for negative `k` (the checker uses `toNat`); logical variables of a callee without an
    expression are 0; the bound of an argument is proved in the form `a <= u + sum u_i
    gamma_i`; in mini-C, an operand without affine form gives an unknown value, a scratch
    variable may be named in any case and must differ from the dedicated variables,
    unsigned parameter stores in calls, the cases where the lowering is undefined, and the
    normal form of logarithmic loops.
  288 theorems; `formalization.yaml`, Table `tab:lean`, the guide and `CLAUDE.md` updated.
- **Cited papers** (parts of five marks). Open copies of 14 papers that had not been read
  were found by web search (queries contained titles and authors only) and read in part:
  `gulwani2009speed`, `carbonneaux2015compositional`, `li1995ilp`, `nipkow2002hoare`,
  `blumofe1999scheduling`, `pnueli1998translation`, `necula2000translation`,
  `audsley1993applying`, `graham1966bounds`, `cerqueira2016prosa`, `kirchner2015framac`,
  and more of `blazy2013formal`, `maroneze2014formally`, `sinn2014complexity`.
  `references/README.md` says which passages. One correction: SPEED
  (`gulwani2009speed`) uses counters and invariants and presents itself as an alternative
  to ranking functions; Paper I no longer cites it for ranking functions. Two sentences
  made more precise (the greedy-scheduling theorem of Blumofe and Leiserson; RTL and
  Clight in Paper II). Not obtained: `nielson1987hoare`, `necula1997proof`,
  `joseph1986finding`, `albert2011closed` and others listed in `references/README.md`;
  the marks were narrowed to these.
- **Cortex-M0 timing table** (one mark). Table 3-1 of the Arm Cortex-M0 Technical
  Reference Manual (r0p0, DDI 0432C, from Arm's public documentation service) was read in
  full and written into `benchmarks/cycles/test_m0.py` (87 rows, encodings checked against
  the assembler); `m0.cycles` agrees. One defect fixed: `WFE` and `WFI` were decoded as
  `NOP` (1 cycle); they now stop the decoder. New bibliography entry `armCortexM0trm`
  (a manual, not on Crossref).
- **Unbounded loops of the kernels** (one mark). `benchmarks/tacle/classify_unbounded.py`
  classifies the 87 loops by the analyser's stated cause (55 / 27 / 5); the sentence of
  Paper II and the README (which still said 94 loops) now give these counts. The split of
  the 27 into 17 and 10 is the AI's reading of the sources.
- **Tool comparison** (one mark). `benchmarks/tacle/test_measure_loops.py` tests the loop
  instrumentation on 13 loops with known counts (in CI). The `filterbank` case was
  confirmed from three sources (flow fact 2, observed 2, oRange's stored answer 1).
  Infer's documentation was fetched and confirms "We do not handle recursion"; the
  sentence "not designed as a sound upper bound" was an interpretation and was reworded.
- **TPDB** (part of one mark). The five potentials "checked by hand" are now certificates
  accepted by the Lean checker (run for these five programs); the sentence says so.
  `benchmarks/tpdb/results/tpdb.json` was stale (2026-11-13) and was regenerated.
- **Early exits in the mini-C export** (the "improve" part of the prompt). `break`,
  `continue` and `return` inside `while` and `for` loops are now exported, written with
  the certificate's flag variables in the existing mini-C (no change to Lean, `lower` or
  `validate`): the rewriting is in `MiniC.cpp` (`Exporter::block`, `loop`) and is trusted
  for validated certificates; Paper I and Paper II say so, and that the description
  evaluates the loop test once more than C after a jump. The generator now keeps one
  flag variable per name (`CertCtx::flagVar`), named by loop nesting depth. Tests:
  eight `ok_*` and three `no_*` functions in `tests/c/minic.c`; the random generator now
  puts `break` into exportable functions (40 files: 61 mini-C sources run against the
  compiled C, no mismatch, no bound below a run). Result on the kernels: 144 of 161
  validated (143), 137 with all callees (134); certificates unchanged (161 of 165). The
  earlier reason "`return` or `break` inside a loop (6)" was mostly `switch` (5).
- **`switch` in the mini-C export.** A `switch` is exported as the cost of its test
  followed by each case group under an unknown test (`Exporter::switchStmt`), which is
  how the generator already lowered it; the description has every execution of the C
  statement and more (the value is not compared with the labels). Tests `ok_switch`,
  `ok_switch_in_loop`, `ok_switch_return`, `no_switch_nested_label`. Kernels: 147 of 161
  validated, 140 with all callees, none failing. Sequential/app, re-run afterwards:
  178 of 231 validated (170 before), none failing; the TPDB certificate counts, re-run
  with the same build, are unchanged (156 with ranges, 101 without).
- **OTAWA** (the author built its Docker image during the session and said so; the AI ran
  it with `--network none`). `benchmarks/cycles/run_otawa.py`: the kernels linked for the
  Cortex-M0 with `rust-lld`, CrossCheck's bounds as FFX flow facts on the binary loop
  headers (label and offset, `maxcount` = bound + 1), `owcet` with the `trivial` script at
  one unit per instruction. 107 functions bounded by OTAWA, 11 executed calls compared,
  no violation. Finding: the source-line FFX that the plugin exports is not placed by
  OTAWA on `-O1` code. New reference `ballabriga2010otawa` (Crossref-checked, not read).
- Left in the papers: the two statements of responsibility; five reading marks for the
  papers not obtained; one mark on the descriptions of KoAT2, CoFloCo and oRange; one on
  the fairness of the TPDB harness.

What the AI did for 44 (Claude Fable 5.2): the advice of prompt 43 was written into
`docs/proposals.md` section 6, with an order of steps 9 to 18; the steps are described
below as they are done.
- **Step 9, lexicographic potentials.** The AI first ran five lexicographic loops through
  the analyser: none was bounded, and the cause was missing invariants (bounds of the
  inner counter), not a missing kind of potential, since `V1 (K2 + 1) + V2` is affine when
  `K2` is a constant. So no checker node was added. Lean: `lex_potential` (the pair
  satisfies the two premises of the loop rule), `lex_ranking_bound` now derived from it;
  280 theorems. Analyser: when no potential is found, a second set of candidate
  invariants (branch tests as they are and relaxed by one, hulls of assigned constants
  and entry bounds, pairs of variables left equal), each proved on entry and inductive as
  before; the proved invariants are handed to the certificate generator as hints that it
  proves again. Tests: `Loops.LexicographicWithBoundedInnerCounter` (three bounds checked
  exact by brute force: 5100, 5000, 150), must-be-rejected
  `Unsound.LexInnerCounterRefilledWithUnknown`, `LexOuterCounterNotAdvanced`,
  `LexRefillFromUnboundedParameter`, `Certificates.LexicographicLoop`,
  `tests/certificates/lexicographic.cpp` (five certificates accepted). Cost: the kernel
  run takes about 1.5 times longer.
- **Step 10, soundness tests.** `clang-plugin/tests/fuzz_bounds.py` (random loop programs,
  bounds against instrumented runs, the mini-C export interpreted against the compiled C)
  and `formalization/test/mutate_certificates.py` with `cert_interp.py` (an interpreter of
  certificate programs written from the Lean semantics; mutated certificates). **Defects
  found and fixed**: (a) a loop whose body can never return to the head (an inner loop
  that does not terminate) was reported with 0 executions of its body, although the body
  starts once; the function was already rejected, but the reported loop bound and the
  exported flow fact were wrong (three occurrences in the first 480 random functions;
  regression test `Unsound.OuterLoopWhoseBodyNeverCompletes`); (b) the mini-C exporter
  wrote a source for a loop with a `!=` conjunct, which the checker then did not validate
  (`no_loop_test_ne` in `tests/c/minic.c`). One mismatch reported by the test was a defect
  of the test itself (runs discarded for overflow on one side only), corrected. After the
  fixes: 960 random functions, 873 bounded loops, 1.29 million runs, no bound below an
  executed count, 238 certificates accepted; 1,898 mutants of 14 accepted programs, 1,853
  rejected, 45 accepted, none with a run above its bound.
  Final campaign, with the binary that has division and unsigned stores in mini-C: 960
  functions, 1,632 loops, 863 bounded, 1.23 million runs, no violation; 2,114 exported
  invariants and 832 variants executed without a failure; 143 mini-C exports compared with
  the compiled C, no mismatch; 2,029 mutants of 15 accepted programs, 1,983 rejected, 46
  accepted, none with a run above its bound. That campaign found three functions exported
  but not validated (the exporter was less precise than the generator on `x <<= k` for an
  unsigned `x`, and gave scratch variables to statements in source order where the
  generator's order differs): both corrected (scratch variables are now keyed by
  statement). A campaign of 40 more files after the corrections (320 functions, 283
  bounded loops, 384 thousand runs) had no failure of any kind.
  Last measurements (2026-11-16, on a machine shared with other work): sequential/app
  275 loops bounded for every call, 330 in context, 231 of 263 functions certified, 170
  validated (one more exported function was not validated at first: a constant
  expression exported as a quotient; the exporter now folds constants first); CMSIS-DSP
  unchanged (616 functions, 1,044 loops with ranges; two files over the time limit);
  TPDB with ranges 207 programs (171 before the retry with more invariants), 156
  certified. Cost of the retry: the kernel run is about 1.5 times slower, the largest
  sequential program about three times (stated in Paper II and the README).
- **Step 13.** The unbounded-loop error names a likely cause;
  `clang-plugin/scripts/crosscheck_project.py` (compilation database, `project.json`,
  `index.html`, baseline).
- **Step 15.** Reports carry `invariants`, `variant` and `requires`;
  `clang-plugin/scripts/acsl_export.py`. Frama-C is not installed on this machine: the
  export was **not** run through it; the annotations are executed as run-time checks in
  `fuzz_bounds.py` (and a falsified annotation is detected).
- **Step 11, mini-C (partly).** Statement `divStore` in `MiniCCore.lean` (quotient,
  remainder and mask by a constant; a shift is a quotient), with `divFacts`, `divOf` and
  its case of `lower`; no proof changed (the lowering produces existing programs of the
  checker). Reader in `CheckerMain.lean`; exporter (`MiniC.cpp`, own type checks; a
  scratch variable for `x = x / c`, taken from the certificate after checking that it is
  not a variable of the source); the generator now uses one scratch variable per
  statement. Tests `ok_halve`, `ok_digits`, `ok_shift`, `ok_quarter`,
  `ok_remainder_mask`, `no_unsigned_remainder`; the random-program test interprets the
  new statement. Then stores into unsigned variables (`assignU`: the value if it is in
  the variable's range, unknown otherwise; exporter function `expMod`), tests
  `ok_unsigned`, `ok_unsigned_down`, `ok_unsigned_halve`, `no_unsigned_char`. Kernels: 105
  of 161 certificates validated (were 93), none failing. Then calls (`call`: stores of the
  arguments into the callee's parameter variables, then the checker's call node; also in
  initialisers and return values), tests `ok_call`, `ok_call_in_loop`,
  `ok_call_in_return`, `no_call_in_test`: 143 of 161 kernel certificates validated, 134
  of them together with every function they call, none failing. The random-program test
  has no calls between functions, so the call statement is tested only by `tests/c/minic.c`
  and the benchmarks.
- **Step 12, bounds without ranges.** Option `symbolic`: `synthesizeRanking(...,
  unbounded)` (no constant entry bound, small coefficients preferred); a loop with such a
  potential is not an error, its numeric cost is infinite, the function is reported
  `symbolic` and not `ok`; the certificate generator then derives a bound affine in the
  parameters, with logical variables for `x`, `-x` and `x - y` (up to three parameters),
  which the unchanged checker accepts or not. Tests `Symbolic.*`,
  `Unsound.SymbolicModeStillNeedsAPotential`. TPDB runner: a third mode without ranges,
  in which a value read from the nondeterministic input function before the first loop of
  the entry function becomes a parameter (a harness, described in the README).
- **Step 14, stack.** Lean `Stack.lean` (activation trees, `highWater_le_of_bound`,
  `highWater_le_depth`; 284 theorems, 21 modules), Paper I `subsec:stack`;
  `benchmarks/cycles/stack.py` and its check in `run_cycles.py`. 143 of 267 kernel
  functions, 24 calls compared with the emulated runs, no violation, 19 exact.
- **Step 17 (OTAWA) not done**: the command that would clone and build OTAWA in a
  container was refused by the session's permission policy; nothing was fetched except
  the list of repositories and the project's README. **Step 18 not done** (recursion in
  the checker, amortised bounds): reasons in `docs/proposals.md` section 6.4.
- A reference was added, `kirchner2015framac` (Frama-C), from the model's memory; its
  bibliographic data were checked on Crossref; it was not read.
- **Step 16.** `docs/qualification/` (requirements, traceability script, requirement
  tests, README). Written from the model's general knowledge of DO-330 and ISO 26262;
  it claims no compliance. **Author to check** (section 3, item 30).

What the AI did for 41 to 43 (Claude Opus 5.5 until prompt 42, Claude Fable 5.2 from
prompt 43, after the user switched models):
- 41: the companion guide was brought up to date (all seven parts: logarithmic loops,
  interrupts, cycles, Rust, validation, current figures and line numbers); step 8 was
  measured and its figures put into Paper II, the READMEs and the guide (below).
- 42: answered that the model can be switched while background runs continue.
- 43: a review and advice given in the conversation (no file changed by it): weak points
  (validated share of certificates, informal link from mini-C to C, soundness evidence on
  one input per kernel, analyser needing numeric ranges, time on one core only, breadth
  over depth); suggested order (finish steps 8 and 9, soundness tests on random programs
  and mutated certificates, mini-C with calls and unsigned, parametric analyser, an
  end-to-end OTAWA demonstration on a recognised benchmark, stack bounds, a qualification
  kit, an ACSL export). The benchmark names it mentions (ROSACE, PapaBench, NASA cFS) are
  from the model's memory and unchecked. Written into `docs/proposals.md` section 6 after prompt 44.

What the AI did for 40 (step 8, chosen by the AI: the CMSIS-DSP figures had not moved with
step 7, and the AI found why):
- Analyser: unsigned `/`, `>>`, `%`, `&` of a value of the same type are exact (the result
  lies between 0 and the operand or mask, so it cannot wrap): before, the range check could
  not be proved (symbols get no type limits) and the facts were dropped, so no unsigned
  halving loop was bounded. Growing potentials (a counter at least 1, multiplied by a base
  64..2 on every path, at most a constant under the test). Bases include 10.
- Lean: checker node `whileGrow` (`growEntry`, `ghostLow`, `ghostGrow`), `growloop_sound`
  via the logic's loop rule with `logIters b K - ⌊log_b pot⌋`; examples `growCert_checks`,
  `growCert_rejected`, `growCert_needs_entry`, `growCert_cost`; 279 theorems.
- Generator: `whileGrow` emission; `x << k` and `x <<= k`, `x *= c` modelled exactly in
  signed types (as in the analysis), also in the mini-C exporter so that validation agrees.
  A crash (empty linear potential with a logarithmic one) found by the certificate ctest
  and fixed.
- Tests: `Loops.LogarithmicUnsignedAndGrowing`, must-be-rejected `Unsound.GrowFromZero`,
  `Unsound.UnsignedHalvedThenIncreased`, `ok_doubling` in `tests/c/minic.c`.
- Results (measured after prompt 41): TACLeBench kernels, loops bounded for every call
  127 -> 132 (equal to the flow fact 101 -> 105), in context 138 -> 141 (129 -> 131),
  entry functions 10 -> 11 (`fft_main`); 158 of 162 bounded functions certified (the two
  new `fft` functions are not: the generator's invariant does not show the logarithmic
  potential positive); no bound below an observed count, geometric mean 1.83 / 1.03;
  FFX equal to oRange's on 115 loops; sequential/app unchanged from step 7 (274 / 329
  loops); CMSIS-DSP 616 functions (unchanged), loops with ranges 1024 -> 1044, one file
  timed out in the run; TPDB with ranges 166 -> 171, 130 certified; Cortex-M0 104
  functions, 10 calls and 43 loops compared without violation, one `fft` function with a
  bound 970 times the observed cycles (product of nested bounds), stated in Paper II.

What the AI did for 39 (step 7, chosen by the AI after steps 1-6: logarithmic potentials,
the largest measured blocker on CMSIS-DSP; the user then asked for the next step, which the
AI started after committing this one):
- Lean: checker node `whileLog` (`CheckerCore`: `ilog` by structural recursion so that
  `decide` evaluates it, `logIters`, `ghostMul`, `logExit`), soundness case of `check_sound`
  via `logloop_sound`, which applies the logic's loop rule to the potential
  `⌊log_b pot⌋ + 1` (no new rule of the logic); `ilog_eq` relates `ilog` to mathlib's
  `Nat.log`; examples `logCert_checks`, `logCert_rejected`, `logCert_base1_rejected`,
  `logCert_cost`; mini-C normal form and `nf_equiv` case; 270 theorems.
- Plugin: logarithmic potentials in the analyser (a variable at least 1 at every iteration
  and divided by the largest base 64..2 on every path; kept when better than the linear
  bound), certificate generator for `whileLog` (constant entry bound, no early exits).
  **A generator bug found and fixed**: for `x >>= k` / `x /= c` the `havocC` facts mentioned
  the new `x` on both sides (the certificate's program was then not the C function; the
  checker accepted it because it checks the certificate's program); the old value is now
  copied first. Tests: `Loops.LogarithmicHalving`, must-be-rejected
  `Unsound.LogOnlyOnSomePaths`, `LogUndoneByAnotherPath`, `LogNeedsAPositivePotential`,
  `Certificates.LogarithmicLoop`, `tests/certificates/logarithmic.cpp`; 158 tests.
- Results: TACLeBench kernels: tables unchanged (`fft`'s bit-reversal loop 11 instead of
  1023, its flow fact is 10); observed counts: no bound below, geometric mean bound/observed
  1.85 (every call) and 1.03 (in context), were 1.92 and 1.06. CMSIS-DSP, sequential/app and
  TPDB: see the next commit. A stale count in the TACLeBench README (23 loops bounded only
  by CrossCheck, 24 since step 4) was corrected.
- Papers: Paper I `def:certificate`, checker description and proof of
  `thm:checker-soundness`, `prop:lex-log` status, scope, future work, Table `tab:lean`;
  Paper II limitations and the observed-count figures. **Author to check** (§3, item 28).

46. "I would like to cover properly early exits and switch on lean, start the do loops and tracked globals in mini-c, the cortex-m0 timing for OTAWA and run with minimal annotations. Could you do  the descriptions of KoAT2, CoFloCo and oRange by yourself ?"

What the AI did for 46 (Claude Opus 5.5, 2026-11-16).
- **Early exits and `switch` in Lean.** New modules `MiniCJumpCore` (no mathlib; in the
  checker program) and `MiniCJump`. `JStmt`: mini-C with `break`, `continue`, `return`,
  `switch` and `do` loops; `JExec`/`JExecD`: their meaning, a big-step semantics with
  outcomes (normal, break, continue, return, interrupted for prefixes); `tr`/`elim`: the
  elimination of the jumps with flag variables, computed by the checker, in the form the
  generator already wrote (continuation-passing: what follows a jump moves into the
  branches that do not jump); `validateJ`. Theorem `sim` (simulation, by induction on the
  derivation, generalised over the context of enclosing loops and `switch` statements and
  the continuation; a second statement about the loop command is proved in the same
  induction) and `validatedJ_sound` (every interrupted run of the source costs at most
  the bound). The rewriting the exporter did is gone from the C++ code: the exporter now
  writes the jumps as they are (key `jsource`), and the checker eliminates them. Lean:
  413 theorems, 23 modules, no `sorry`, standard axioms only.
- **A defect found while doing it.** The first statement of the theorem required every
  procedure of the program to leave the flags alone, including the validated function
  itself, which writes them: the hypothesis could not hold for a function with flags,
  and the checker's executable check failed for the same reason (no function with a
  loop jump was validated). It is now restricted to the functions numbered below the
  validated one (the checker already requires calls to go there), with the call bound
  carried by `Quiet` and `quietCmd` and checked on the source's calls (`callsBelow`).
- **Generator changes**, to match the elimination: each `switch` gets a variable of its
  own for the unknown choice of the case group (`?case<depth>`, instead of the shared
  choice variable), and a loop no longer clears the return flag twice (its prologue does
  it). A test checks that a source naming a ghost variable is not validated
  (`tests/check_minic.py`, 12 mutations).
- **`do` loops.** In Lean: `JStmt.doLoop` with rules of its own in `JExecD`; `elim`
  accepts it when its body has no `break` or `continue` of its own, as the body followed
  by the loop (`desugar_exec`: every run is a run of the desugared statement;
  `tr_desugar`). Generator: a `do` loop is certified as the body followed by the loop,
  when the body has no jump and no `switch` at all. Exporter: `do` loops exported.
- **Tracked globals in mini-C**: accepted by the exporter as ordinary variables of the
  certificate; static locals are still refused. Assumption: no other code writes them
  while the function runs (stated in both papers).
- **OTAWA with Cortex-M0 timing**: `benchmarks/cycles/otawa/m0time.cpp`, a program
  compiled against OTAWA in the author's image (no network) that sets the time of each
  basic block from the timing table of `m0.py`; `run_otawa.py --timing m0`.
- **Minimal annotations**: `benchmarks/tacle/run_annotated.py`.
- **Results** (re-measured with this build): kernels 161 of 165 certified (unchanged),
  152 validated (147 before), 146 with all callees, one not validated (`isqrt_main`: the
  generator inlined a call whose argument has no bound, the source has the call);
  sequential/app 231 certified (unchanged), 193 validated (178), none failing; TPDB 159
  certified with ranges (156) and 103 without (101: 89 in the parameters + 14), the
  increase from `do` loops; fuzz (40 files, seed 2026): 0 violations, 61 mini-C sources
  compared, 0 mismatches; OTAWA in cycles: 107 functions, no call above its bound, never
  below the timing schema; minimal annotations: `main` bounded in 23 of 29 kernels (10
  without), 84 annotations, 2 below an observed count; 174 ctest tests pass.
- **Tool descriptions** (KoAT2, CoFloCo, oRange) rewritten in Paper II from what was
  read: the CoFloCo paper (technical-report copy, read in full), the abstract of the
  KoAT paper, oRange's README; the oRange paper could not be obtained and is listed with
  the unread papers. The decision on reporting `filterbank` stays with the author.

47. "Keep improving the paper, lean code, the mini C language, benchmark numbers and results, certificates to aim for scientific relevance and industrial value"

What the AI did for 47 (Claude Opus 5.5, 2026-11-16).
- **Choice.** Of the open items of `docs/proposals.md` §6.4, the AI chose amortised bounds
  for nested loops (step 18): the measured weakness of the cost bounds is the product of
  nested loop bounds, and an amortised rule is a new result of the theory side.
- **Lean.** `Language.valid_whileSum` (with `whileSum_exec`, `whileSum_pre`): a derived
  loop rule in which the cost of an iteration is a function `W` of the integer potential
  before it; any `F` with `F X ≥ w` and `w + W v + F (X − d) ≤ F X` (for `d ≤ v ≤ X`)
  bounds the loop from `V ≤ K` by `F K`. Checker: the loop nodes `while`/`whileAnd`
  accept, besides the old bound condition (`loopBoundOk`, with `γⱼ` absent from the body
  bound), an amortised one, `triOk`: constant entry bound `k`, body bound
  `a + c·max(0, γⱼ)` and `2B ≥ triBound2 = 2((N+1)w + Na) + c(2Nk − dN(N−1))`,
  `N = ⌊k/d⌋`; proof `triloop_sound` (closed form: `triBound2_step`, `triBound2_ge`).
  The certificate format is unchanged (a body bound may now mention `γⱼ`). Example: the
  tool's certificate of a 4×4 triangular nest, `triCert_checks` (bound 70 for the loop,
  94 without amortisation), `triCert_69_rejected`, `triCert_cost`, all by `decide`.
  Lean: 424 theorems, about 9,300 lines, standard axioms only.
- **Generator.** An inner loop's entry bound is first sought in the logical variables of
  the enclosing loops (`symbolicUpper` with a lower index limit), and the potential
  suggested by the loop test is tried inside loops too; the enclosing loop builds the
  amortised node and also lowers its body again without such bounds, and keeps the
  smaller certified bound. Logarithmic loops lower their bodies without them (their body
  bound must be constant). C++ replica `cert::triBound`.
- **Tests.** Unit test `Certificates.AmortisedTriangularNest` (a `j = i..n` nest below 60%
  of the product bound; a square nest and a `j < i` nest unchanged); certificate example
  `tests/certificates/triangular.cpp` (four nests, accepted); mutation fixture
  `formalization/test/certificates/triangular.json` (150 requested, 87 mutants made, all
  rejected; unchanged certificates never exceeded by the interpreter), in ctest and CI.
- **Results.** Kernels: certificates and validation unchanged (161 certified, 152
  validated); 14 certified bounds below the analyser's (12 before): `ludcmp_main` 4,907 →
  3,674, `main` of `ludcmp` 6,076 → 4,843. Sequential/app: 231 certified, 193 validated, none failing (unchanged); `susan_median`
  1,047 → 648 (validated). 175 ctest tests pass.
- **Not covered**, stated in both papers: an inner loop from `0` to the outer counter (its
  bound grows as the outer potential falls; it would need a second logical variable or a
  new node); the analyser's own bounds and the cycle bounds still multiply.
- Papers: Paper I `prop:amortised-loop` (new), `def:certificate`, checker description and
  proof of `thm:checker-soundness`, scope paragraph, nested-loops paragraph, Table
  `tab:lean`; Paper II certificate generation and limitations. **Author to check** (§3,
  item 36).

48. "Proceed with the next step, also check yourself for prior work"

What the AI did for 48 (Claude Opus 5.5, 2026-11-16).
- **Prior work** (the `\authortodo` of prompt 47). Web search, then the texts read locally:
  Healy, Sjödin, Rustagi, Whalley, van Engelen, "Supporting Timing Analysis by Automatic
  Bounding of Loop Iterations", Real-Time Systems 18 (2000), Section 5: non-rectangular
  loop nests, the number of iterations as a summation, after Sakellariou; and Albert,
  Genaim, Masud, "More Precise Yet Widely Applicable Cost Analysis", VMCAI 2011, read
  through Section 4.2 of Masud's thesis (the paper's own copy needs a login): the costs of
  successive iterations bounded by an arithmetic (or geometric) sequence, increasing or
  decreasing, and summed. Both DOIs checked against Crossref; bibliography entries
  `healy2000supporting`, `albert2011more`; reading notes in `references/README.md`. The
  paper no longer presents the summation as new: Paper I cites both before
  `prop:amortised-loop`, Paper II in its related work. The search was a few queries, not
  a survey: earlier sources may exist.
- **Next step: inner loops from `0` to the outer counter** (`j < i`), left open by 47.
  Lean: `Language.valid_whileMono` (with `whileMono_exec`, `whileMono_pre`): the loop
  rule with a monotone bound `F` of the potential itself (`w + W v + F (v − d) ≤ F v`
  for `v ≥ d`), which allows a cost that grows as the potential falls (Paper I
  `prop:amortised-loop`(2)). Checker: new node `whileUp` (`CheckerCore`: `upLo`, `upHi`,
  `upBound2`, `upOk`): constant entry bound `k`; the body is checked with
  `γⱼ = k − pot` (two constraints) and must end with `pot + γⱼ − k + d ≤ 0`; body bound
  `a + c·max(0, γⱼ)`; `2B ≥ 2((N+1)w + Na) + c(2Nk − dN(N+1))`, `N = ⌊k/d⌋`. Proof
  `Checker.uploop_sound` (closed form by induction, `upSum`, `upSum_closed`) and the new
  case of `check_sound`; the mini-C modules (`nf`, `nf_equiv`, `quietCmd`) and the
  executable (`CheckerMain`: JSON, printing) handle the node. Example `upCertAt`: the
  tool's certificate of `for i<4: for j<i`, `upCert_checks` (54 for the loop, 94 as a
  product), `upCert_53_rejected`, `upCert_cost`, by `decide`. Lean: 436 theorems, about
  9,700 lines, standard axioms only (checked with `#print axioms` for `valid_whileMono`,
  `uploop_sound`, `check_sound`, `upCert_cost`, `program_sound`).
- **Generator.** A loop whose body contains a loop and that has a constant entry bound is
  also lowered with the body precondition `γⱼ = k − pot`; if the body bound is
  `a + c·γⱼ`, a `whileUp` node with `cert::upBound` competes with the other candidates by
  value. C++: `Node::WhileUp`, JSON, replicas `upLo`/`upHi`; interpreter
  `formalization/test/cert_interp.py` runs the node. First version tried it only when
  the first lowering had no bound in `γⱼ`; that missed the back-substitution nest of
  `ludcmp` (330 → 230 once fixed). Cost: one more lowering of every body that contains a
  loop (the example file 5 s → 12 s; the kernel run 143 s → 156 s).
- **Tests.** `Certificates.AmortisedTriangularNest`: the `j < i` nest now below 60% of
  the product; `Certificates.EmittedWithTheSameBound` now expects a lower certified bound
  for its `j < i` nest (378 against 648) and a `whileUp` node; three `j < i` examples in
  `tests/certificates/triangular.cpp` (`prefix`, `insertion`, `upto`; all accepted, about
  half the product); the mutation fixture regenerated (119 mutants, 118 rejected, the
  accepted one never exceeded). 175 ctest tests pass.
- **Results.** Kernels: 161 certified, 161 accepted, 152 validated, 146 equal and 14
  lower (unchanged counts); `ludcmp_main` 3,674 → 3,474 (two `whileUp` nests), `main` of
  `ludcmp` 4,843 → 4,643. Sequential/app: unchanged (231 certified and accepted, 193 validated, none failing; 207 equal, 14 lower; no `whileUp` node: no `j < i` nest with constant bounds there); the run took 88 min, `cjpeg_transupp` 2,833 s (2,299 s before).
- Papers: Paper I `prop:amortised-loop` (part 2, prior work), `def:certificate`, checker
  description, proof of `thm:checker-soundness`, scope paragraph, nested-loops paragraph,
  Table `tab:lean`, conclusion; Paper II generator, results, related work, limitations,
  future work. **Author to check** (§3, item 37).

49. "Continue until all open improvements have been realized. Integrate other benchmarks if you think it is useful for scientific relevance and industrial value. Work on authortodos yourself as I have little time while reviewing your work. Keep execution time under control so that the tool will behave on real world cases."

What the AI did for 49 (Claude Opus 5.5, 2026-11-16/17).
- **Execution time.** Profiled the slowest program (`cjpeg_transupp`, 2,277 s of analysis)
  by sampling stacks under gdb: nested loops re-run their bodies in every round of the
  invariant refinement of the enclosing loops, and every query built a new Z3 context.
  (1) The answers of `entails`, `isFeasible` and `boundsOf` are cached under the closed
  premises (functions of them; answers identical), with one Z3 context per thread:
  742 s, kernels 156 s → 114 s, ctest 194 s → 100 s, all results unchanged. (2) Option
  `budget` (default 500,000 units of solver work per function, counted in constraints
  sent to the solver, so machine-independent): once spent, the optional searches stop
  and the refinement of candidate invariants stops after two rounds, dropping a set that
  is not yet inductive (sound: only proved invariants are kept). The report gives
  `solver_work` and `search_budget_exhausted`. Test `Budget.ExhaustedSearchStaysSound`.
- **A soundness defect found and fixed** (by reading the code while extending mini-C):
  static locals were initialised at every call in the analysis and in the certificate's
  program, so a loop bounded by a static counter that grows from call to call got a
  bound (and an accepted certificate of the wrong program; validation against the source
  would have refused it). Now a static local's declaration does nothing at a call and its
  value on entry is unknown, as for a global. Test `Unsound.StaticLocalCounterGrowsAcrossCalls`.
- **Analyser precision.** Conditional expressions keep the facts true in both arms
  (`m <= a`, `m <= b` for `a < b ? a : b`, and the hull of the arms' intervals); a
  disequality in a loop guard is split into `a < b` and `a > b` (two paths). Tests
  `Conditional.MinOfTwoArmsDecreases`, `Disequality.GuardSplitIntoTwoPaths`, must-reject
  `Unsound.ConditionalArmMayBeZero`, `Unsound.DisequalityGuardOneSideStuck`.
- **Mini-C**: static locals exported (their declaration as nothing); `ok_static_local`,
  `no_static_escaped`.
- **Benchmarks**: TACLeBench `parallel` category (`run_tacle.py --category parallel`,
  program units with file lists and source fixes in the work copy): the five threads of
  ROSACE (flight controller; `random`/`srandom` renamed in their text) and DEBIE (ESA
  satellite instrument software; a `#pragma entrypoint` inside a function header and an
  include-guard typo fixed in the copy; host port). PapaBench does not compile as
  distributed (missing `math_papabench.h`, AVR interrupt macros) and is left out.
  ROSACE: in each thread 73 of 86 functions bounded and certified (every control task but
  `aircraft_dynamics`, which calls `sinf`/`cosf`); DEBIE: 111 of 187 bounded, 110 certified,
  30 of 76 flow-fact loops bounded (26 equal; 2 below, `sizeof` of a structure that differs
  between host and target); 480 certificates accepted, 309 validated.
- **Re-measured** (2026-11-17, all with the final binary): kernels unchanged (161
  certified, 152 validated; 1 min 53 s); sequential/app: same loop tables, 231 certified,
  194 validated (193), 5 bounds 1-3 units lower (static-local initialisers no longer
  charged), 23 min (88 min); TPDB: 215 bounded in the ranged mode (207), 107 bounded by the
  other tools and not by CrossCheck (115); without ranges 103 certified (unchanged), 139
  with potentials but no certificate (133); ranged-mode certificates 97 summaries, 62
  constant (17 summaries became constant amortised bounds after prompts 47-48, smaller at
  the largest inputs; found by building the earlier revision and comparing). 181 ctest
  tests pass.
- **Authortodos.** Copies obtained and read: `hoffmann2012multivariate` (author's copy),
  `wilhelm2008worst` (MDU page); `shaw1989reasoning` and `albert2011closed` are now cited
  as described in sources that were read (Wilhelm et al. §2.1.2; Masud's thesis); the
  reading todo of Paper II is reduced to `puschner1989calculating` and
  `demichiel2008orange`. No copy found for `necula1997proof`, `joseph1986finding`,
  `nielson1987hoare`, `puschner1989calculating`, `demichiel2008orange` (searched again).
  TPDB: a second random sample of ten programs (seed 2026) classified; it confirms the
  first (`benchmarks/tpdb/README.md`). The todos that only the author can resolve are
  kept: the responsibility statements in both papers and the decision on reporting
  `filterbank` to oRange's authors.
- **Not done** (open): polynomial bounds in the checker (products of parameters; needs a
  new form of symbolic bound through the whole checker and its proofs), recursion in the
  checker, stack bounds for recursion (no recursive function with a depth bound in the
  benchmarks to test it on).

### Earlier work

**Author to fill in:** tools, models, prompts and scope of any AI use before
2026-11-11 (the pre-existing manuscript, Lean files and `CLAUDE.md`).

## 2. Compliance audit against the AGMAI recommendations

The recommendations address AI labs; for a paper released by a human author their
Section 2.A applies (traditional norms: the author understands the argument, has
verified it personally, and takes full responsibility). The Step I items are applied
here as the release standard.

| Item | Requirement | Status |
|---|---|---|
| 2.A | Author understands every argument, has verified correctness personally, takes full responsibility | **OPEN — only the author can do this.** See checklist in §3. |
| 1(a) | Literature searched; ideas cited to the papers that introduced them | Done by the AI from memory (Related Work, Positioning). **Author must check every reference and the novelty claims.** |
| 1(b) | Traditional paper style: introduction, precise statements and proofs | Done. |
| 2 | Deposit in a scholarly repository with persistent identifier and version history | **OPEN.** arXiv for the paper. The Lean code is on GitHub only: tag the submitted revision and archive it (e.g. Zenodo or Software Heritage), then cite the identifier in the paper. |
| 3 | Publish model name, prompts, summarised reasoning, time, cost | Model, prompts, summary: this file. **Time and cost: open.** |
| 4 | Formalize as far as possible; state formalization status clearly; machine-readable link between paper and formal artifact; copyright headers; challenge file | Formalized with status stated in the paper (Section "Mechanization in Lean 4", incl. what is *not* formalized; the C++ plugin is explicitly outside the formalization). Copyright headers added. `formalization/formalization.yaml` links paper labels to Lean names, but its schema is project-defined and **not validated** against a community spec. **No challenge file for `comparator` yet.** |
| 5 | Document exactly how AI came to be used on this problem | This file, and the "Statement on the Use of AI" in the paper (contains an explicit author-to-confirm marker that must be resolved). |

## 3. What the author must verify personally before release

Machine-checked statements are safe as *Lean statements*; what needs human judgement
is whether each Lean statement says what the paper says, and everything outside Lean.

1. **Statement fidelity.** For each row of Table 1 in the paper, read the Lean
   statement and confirm it matches the paper's statement (hypotheses included).
2. **Non-mechanized mathematics** (proved on paper only):
   - general branching factor `b > 2` in the tree-order propositions and the closed form
     `I·(L^d − 1)/(L − 1) + L^d`;
   - the remark on the fixed-point reading (`t^ω` as least fixed point);
   - the Farkas / linear-template paragraph: completeness over ℚ, and the complexity
     statement attributed to Ben-Amram & Genaim;
   - the decidability remark (translation loops ↔ Presburger; polynomial loops ↔ Diophantine).
3. **Examples.** The parametric-loop system was changed
   (`i_loop = i_init + 2(n−1)`, `i_last^0 = i_loop + 2`); confirm it against the
   prototype's actual output, or adjust the sentence saying the systems are produced
   by a prototype.
4. **Bibliography.** Check every entry against the source, especially the
   venue and year of `attali1998formal` and all page numbers.
5. **Claims about tooling.** The paper says a prototype generates the example systems
   and that the Clang front-end is under development; confirm both are accurate.
6. **Title.** Changed to "Dual-Layer Semantics of Imperative Programs and WCET
   Verification via Constrained Optimization"; confirm the wording.
7. **New references.** Read each paper added on 2026-11-12 and confirm that the sentence
   citing it describes it correctly (the AI verified bibliographic data only).
8. **Prototype section and Table 2.** Re-run `ctest` and the tool on `benchmarks/`,
   confirm the figures, and read `clang-plugin/README.md` ("Soundness", "Limitations"):
   the analyser is unverified C++ written by an AI, and its soundness rests on review
   and on the regression tests. Decide whether the examples sentence in Section
   "Examples" ("systems ... produced by a prototype implementation") is still accurate.
9. **Size potential.** Check Proposition "Size Potential" and its attribution to the
   potential method.

10. **TACLeBench subsection** (`subsec:tacle`). Re-run `benchmarks/tacle/run_tacle.py`
    and confirm Table `tab:tacle`; check the classification of the 96 unbounded loops
    against the sources (it was made by the AI); confirm the two new references describe
    the collections correctly; decide whether to add a run with minimal annotations.
11. **Tool comparison** (`tab:tools`). Re-run `compare_tools.py`, inspect
    `benchmarks/tacle/results/`, and check the descriptions of ScalarEvolution, KoAT2,
    llvm2kittel and Infer against their papers and documentation. The KoAT2 and Infer
    runs used default options (for llvm2kittel, the image's own flags plus inlining of
    callees), with no tuning; decide whether that is fair to state as is.
12. **Observed loop counts** (rows "Loops reached" of `tab:tools`). Read
    `measure_loops.py`: that the counter is reset on every entry of the loop and
    incremented once per execution of the body, in particular for `do` loops and loops
    left by `break`; re-run and spot-check a few counts by hand (e.g. with a debugger).
    Check the interpretation of the two flow facts below the count (`md5` line 562,
    `quicksort` line 745).
13. **oRange** (column of `tab:tools`). Check that the comparison is fair to it: the
    build (oRange from GitHub, FrontC from IRIT), the removal of the pragmas, the use
    of the summary `max` (maximum over calling contexts), the 600 s timeout. Confirm the
    `filterbank` counterexample, ideally with the oRange authors before publishing it.
14. **CoFloCo** (column of `tab:tools`). Check that running it on llvm2kittel's
    uniform complexity tuples (the KoAT2 options) through `interfaces/C2ces` with the
    default cost model is a fair use, and that "Infinity" is read as "no bound found".
15. **TPDB** (paragraph "Complexity benchmarks"). Decide whether the bounded-mode harness
    is a fair way to run CrossCheck (it also bounds nondeterministic values, which the
    other tools do not assume); check the 7 CrossCheck-only programs and the sampled
    failure reasons in `benchmarks/tpdb/README.md`; check the entry-function heuristic.
16. **Calling contexts and `prop:context-bound`.** Read the proposition and its proof,
    and the four Lean statements. In the plugin, check the three soundness rules
    (evaluate before costing, same-type arguments, no context for self-recursive
    functions) and the `Calls/UnsoundContext` tests; check that the report's two kinds
    of bound (for every call / in context) are described correctly wherever figures are
    quoted.
17. **Cost logic** (`subsec:cost-logic`). Check that the definitions in the text
    (`\Downarrow`, `\uparrow`, valid and derivable triples) say what `Exec`, `Pre`,
    `Valid` and `Derivable` say in `Language.lean`; read the proof of
    `thm:cost-logic-soundness`; read Nielson 1987 and Haslbeck and Nipkow 2018 and
    resolve the `\authortodo` on how this system differs from theirs.
18. **Bibliography.** The data of every entry were checked by script against public
    indexes (see session notes); check `matiyasevich1970enumerable` yourself, and read
    the papers whose content the text relies on. `references/README.md` lists which
    papers the AI read, how far, and which it could not obtain (29 entries).
19. **Procedures, recursion, checker, new potentials.** Read rules 7 to 9 and the recursion
    case of the proof of `thm:cost-logic-soundness`; compare `def:certificate` and the
    description of the checker with `ACmd` and `check` in `Checker.lean`, and read the
    proof of `thm:checker-soundness`; check `prop:lex-log` and its proof; read Necula
    1997, Nipkow 2002 and Blumofe and Leiserson 1999 before keeping their citations;
    decide whether the unformalized paragraph on weights and parallel composition should
    stay.
20. **Certificate emission.** Read `docs/certificate-format.md` and the paragraph
    "Certificates" of the paper; check the claim that inlining a callee is sound (a
    callee cannot modify the caller's tracked variables) and that moving the statements
    after a returning conditional into its branches preserves the cost semantics;
    inspect a few certificates with `crosscheck-check --print`.
21. **Early exits, `switch`, unsigned in certificates.** Read the `whileAnd` case of
    `check` and of `check_sound` and the text added to Definition `def:certificate`,
    the checker description and the proof of `thm:checker-soundness` (Paper I). Check
    that the lowerings described in `docs/certificate-format.md` (flags for
    `break`/`continue`/`return`, `switch` as nondeterministic groups, the wrap-around
    test of unsigned stores, `certModular`'s congruence argument) are faithful to C
    semantics: the checker verifies the certificate's program, not this translation.
22. **Reported loop bounds.** Loop bounds in reports now count executions of the body
    for `do` loops and for loops whose leaving iteration is not covered by the
    potential; confirm this is the convention wanted in the papers' tables.
23. **Program certificates.** Read `Definition def:program-certificate`, the proof of
    `thm:program-soundness`, and the `call` case of `check`/`check_sound`; confirm that
    contracts (functions without a body) are stated as assumptions in both papers and in
    the checker's output, and that `docs/contracts.md` says what a contract may not claim.
24. **Validation against mini-C.** Read Definition `def:minic`, Lemma `lem:nf-equiv` and
    Theorem `thm:validated` against `MiniCCore.lean` (`lower`, `nf`, `validate`) and
    `MiniC.lean` (`nf_equiv`, `validated_sound`). Read `clang-plugin/src/analysis/MiniC.cpp`
    in full: it is now the trusted translation for validated certificates; confirm that
    its modelling choices (unknown values for memory and untracked variables, exact signed
    arithmetic under the no-overflow assumption, the conditions for exact `+=`/`++`,
    `return` outside loops, the refusals) are faithful to C, and that the papers state
    the hypotheses (no signed overflow, no aliasing of tracked variables, no concurrent
    writes). Read Pnueli et al. 1998 and Necula 2000 before keeping the citations.
25. **Interrupts and fork-join.** Read Definition `def:interrupt-model`, Theorem
    `thm:response-time` and Proposition `prop:graham` against `Interrupts.lean` and
    `ForkJoin.lean`; confirm that the hypotheses (no activation pending at the start, one
    cost unit = one time slot, handlers not writing the task's variables) are stated
    wherever response times are reported; check the authors of `joseph1986finding`.
26. **Cortex-M0 cycle bounds.** Check `m0.cycles` against the instruction summary of the
    Arm Cortex-M0 Technical Reference Manual (the AI wrote it from memory: 1 cycle for data
    processing, 2 for loads/stores, 1+N for LDM/STM/PUSH/POP, 4+N for POP with PC, 3 for
    taken branches, 1 not taken, 4 for BL, 3 for BX, MULS 1 or 32), and decide whether the
    loop matching by debug lines (checked on runs only) is acceptable as stated.
27. **Rust front-end.** Read `frontends/rust/README.md` and `mir2c.py`; confirm the
    semantic choices (checked arithmetic as non-overflowing C, assertions as early
    returns, `usize` as 64 bits) and that Paper II states that bounds cover the executions
    that do not panic and that the translation is unverified and tied to rustc 1.100.0.
28. **Logarithmic loops.** Read the logarithmic case of the proof of `thm:checker-soundness`
    against `logloop_sound` and `logPot_step` in `Checker.lean`, and the `whileLog` case of
    `check` in `CheckerCore.lean`; note the generator bug on `x >>= k` found during this step
    (certificates emitted before it may describe a different program for such statements).
29. **Growing logarithmic loops and exact unsigned division.** Read the growing case of
    the proof of `thm:checker-soundness` against `growloop_sound` and `log_grow` in
    `Checker.lean` and the `whileGrow` case of `check`; in `Analyzer.cpp`, check the claim
    that unsigned `/`, `>>`, `%` and `&` cannot wrap (function `shrinking` and its uses in
    `evalBinary`), which is an analyser rule without a Lean proof; check the new figures of
    Paper II (`tab:tacle`, `tab:tools`, CMSIS-DSP, TPDB, cycles) against the READMEs.
30. **Steps 9, 10, 13, 15, 16.** Read `lex_potential` and the remark after
    `prop:lex-log`; in `Analyzer.cpp` (`execLoop`), the retry with more candidates and the
    rule that counts one more body execution when an iteration may never return to the
    head; decide whether the two defects found by the random tests need a note in Paper II
    (the AI added one); have `docs/qualification/README.md` read by someone who knows
    DO-330 before showing it to an industrial partner; run `acsl_export.py` output through
    Frama-C/WP on one example before claiming that the export is usable.
31. **Steps 11, 12, 14.** Read `divFacts` and the `divStore` case of `lower` in
    `MiniCCore.lean` against the added item of Definition `def:minic`, and decide whether
    the facts stated for a mask and a remainder are what you want mini-C to mean; read the
    `assignU` case and `expMod` in `MiniC.cpp` (the claim that sums, differences and
    products computed over the integers agree modulo 2^width with C's unsigned arithmetic
    when no intermediate result is truncated to fewer bits); read the `call` case of
    `lower` and `callStmts` in `MiniC.cpp`, and decide whether "validated" should be
    reported only for functions whose callees are validated too; read
    `Stack.lean` against `prop:stack` (in particular the off-by-one of the depth
    statement); check that the TPDB harness of the symbolic mode (inputs read before the
    first loop become parameters) is a fair reading of the benchmark; check the reference
    `kirchner2015framac`.
32. **TPDB programs bounded only by CrossCheck.** Done on 2026-11-16: the five
    potentials are in certificates accepted by the Lean checker, and Paper II says so.
33. **Checks made by the AI on 2026-11-16 (prompt 45).** Each of these replaced an
    `\authortodo`; they are checks by the AI, listed so that you can sample them:
    - items 19, 23, 24, 25 (definitions of Paper I against Lean): the comparison is
      described in section 1 under prompt 45; read the three precisions added to
      `def:certificate` / `def:program-certificate` and the four added to `def:minic`, and
      the new `Handlers.rel : Set` and `makespan_lower`;
    - item 26 (Cortex-M0 timings): done against Table 3-1 of the manual; only the decision
      on loop matching by debug lines is left;
    - items 10 and 12 (classification of unbounded loops, loop instrumentation): done by
      scripts; the decision whether to add a run with minimal annotations is left to you;
    - item 13: decide whether to report the `filterbank` case to the authors of oRange
      before publication;
    - items 7, 18, 19, 24, 25 (reading): see `references/README.md` for what was read; the
      papers not obtained keep an `\authortodo`.
34. **Early exits and `switch` in mini-C, and OTAWA (prompt 45).** (The rewriting is no
    longer trusted since prompt 46: item 35.) Read `Exporter::block`,
    `Exporter::loop` and `Exporter::switchStmt` in `MiniC.cpp` (the flag rewriting and the
    description of a `switch` are now trusted for validated certificates) and decide
    whether you accept that a description may cost one loop test more than the C code
    after a jump, and that "validated" may be said of a function whose `switch` is
    described with unknown tests; read the paragraph "A WCET analyzer on the same
    binaries" of Paper II and `run_otawa.py`: the reading of OTAWA's `maxcount` (header
    executions per loop entry) is the AI's, from OTAWA's behaviour and general knowledge,
    not from its documentation; the unit is instructions, not cycles; check the reference
    `ballabriga2010otawa`.
35. **Mini-C with jumps in Lean, `do` loops, globals, OTAWA cycles, annotated run
    (prompt 46).** Read Definition `def:minic-jumps` and Theorem `thm:validated-jumps` of
    Paper I against `MiniCJump.lean` (`JExecD`, `tr`, `sim`, `validatedJ_sound`): is the
    direct semantics the meaning of C's `break`, `continue`, `return`, `switch` (entry
    group not modelled) and `do`? The hypotheses that remain: the exporter's syntactic
    translation, contracts not touching the ghost variables, and no other code writing
    tracked globals during a function. Read `m0time.cpp` (the block time is the sum of
    the table's instruction times, a conditional branch counted as taken; OTAWA's edge
    times are not used) and the paragraph on OTAWA; read `run_annotated.py` (annotation
    values taken from the benchmark's flow facts). Check the new descriptions of KoAT2,
    CoFloCo and oRange in Paper II against the sources listed in references/README.md.
36. **Amortised loop rule (prompt 47).** Read Proposition `prop:amortised-loop` of Paper I
    and its proof (the induction, the closed form and the parity argument) against
    `Language.valid_whileSum` and `Checker.triBound2_step`/`triBound2_ge`/`triloop_sound`;
    check that the third form of the loop condition in `def:certificate` and in the
    checker description is `CheckerCore.triOk`. Decide whether this rule is presented as
    new: amortised bounds for triangular nests are classical in loop-bound analysis (e.g.
    symbolic summation of nested loop counts). (Prompt 48: the AI searched briefly and
    now cites Healy et al. 2000 and Albert, Genaim, Masud 2011; see item 37.)
37. **Amortised loops with increasing cost, and prior work (prompt 48).** Read part (2) of
    `prop:amortised-loop` and its proof against `Language.valid_whileMono` and
    `Checker.upSum_closed`/`uploop_sound`; check that the description of the loop
    "amortised with increasing cost" in `def:certificate` and in the checker description
    is `CheckerCore.whileUp`/`upOk`. Check the two attributions (`healy2000supporting`
    Section 5; `albert2011more`, read only through Masud's thesis) and look for earlier
    sources (Sakellariou's summations, IPET flow facts that bound the total count of an
    inner loop, e.g. Puschner and Koza's markers): the paper must not suggest that the
    summation is new, only its form as a rule of the cost logic with a checker case.
    Remove the `\authortodo` before `prop:amortised-loop` when done.
38. **Prompt 49 (tool, benchmarks, no new theorem).** Check the static-local defect and its
    fix (`Analyzer.cpp` `execDecl`, certificate generator, `MiniC.cpp` `decl`; test
    `Unsound.StaticLocalCounterGrowsAcrossCalls`) and that the papers report it fairly;
    the search budget (`Options::budget`, `searchBudgetLeft`, refinement capped at two
    rounds with the candidates dropped if not inductive): that it can only lose
    precision; the solver cache (`Solver.cpp`: keys are the closed premises and the goal);
    the `?:` facts and the disequality split (sound case analyses); the fixes applied to
    ROSACE and DEBIE in `run_tacle.py` (`parallel_units`) and the descriptions of both
    programs; the second TPDB sample and the replacement of the TPDB `\authortodo` by a
    sentence; the trade-off of 17 TPDB summaries for constant amortised bounds.
