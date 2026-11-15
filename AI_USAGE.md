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
