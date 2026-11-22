# AI usage record

This file documents how AI was used in the CrossCheck paper and Lean development,
following AGMAI's *Responsible Release of AI-Generated Mathematics*
(<https://agmai.org/general-sep29/>, version of 29 September 2026).
It must be kept up to date whenever an AI tool changes the paper, the bibliography
or the Lean code, and it must be complete before any arXiv submission.

Section 1 is a chronological log. The checks it leaves to the author, and its references
to the numbered items of an earlier Section 3, describe the state at the time; on
2026-11-22 (prompt 107) those items were closed, or removed where only the author's own
review could close them: Section 3 now records what was checked, and the author's review
is the subject of the statement in each paper.

Prompts are verbatim, except that names of local files that are not part of the repository
are replaced by a description in square brackets.

## 1. Sessions

### Session of 2026-11-11

| Item | Value |
|---|---|
| Tool | Claude Code (Anthropic) |
| Models | Claude Opus 5.5 (`claude-opus-5-5`), then Claude Fable 5.2 (`claude-fable-5-2`); Claude Haiku 5.5 (`claude-haiku-5-5`) inside the subagent that reads web pages (27 responses over all sessions, found in the transcripts on 2026-11-21) |
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

What the AI did: obtained open-access copies of the cited papers (21 of 50 entries), kept
outside the repository because most are under publisher or author copyright. The AI read
abstracts, and for a few papers the sections the text relies on, and kept reading notes. Two statements of the paper were
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
  implementation plan, the reading notes, `CLAUDE.md` updated.

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
  the reading notes says which passages. One correction: SPEED
  (`gulwani2009speed`) uses counters and invariants and presents itself as an alternative
  to ranking functions; Paper I no longer cites it for ranking functions. Two sentences
  made more precise (the greedy-scheduling theorem of Blumofe and Leiserson; RTL and
  Clight in Paper II). Not obtained: `nielson1987hoare`, `necula1997proof`,
  `joseph1986finding`, `albert2011closed` and others listed in the reading notes;
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
  `healy2000supporting`, `albert2011more`; reading notes in the reading notes. The
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

50. "Proceed with the open tasks"

What the AI did for 50 (Claude Opus 5.5, 2026-11-17).
- **Quadratic bounds in the checker** (proposals step 12, open part). Lean: `SB` gains
  quadratic terms `q` (`a·max(0,γᵢ)·max(0,γⱼ)`), `dotQ`; `SB.le` compares them as a
  subsequence (`qsub`, sound since terms are non-negative); `SB.mul` (product of two
  linear bounds, `crossQ`), `SB.qcomb` (a callee's quadratic terms instantiated with
  products of the linear argument bounds); a third form of `loopBoundOk` (symbolic entry
  bound, linear body bound, decrease 1: `B ≥ (w + Wb)·max(0,K) + w`); the existing forms
  require the body's quadratic part to be empty or free of `γⱼ` (`qfree`). Proofs:
  `dotQ_crossQ`, `SB.eval_mul`, `qsub_le`, `dotQ_update`, `SB.qcomb_ge`, the third case of
  `loopBoundOk_sound`, the call case of `check_sound`. Example `prodCert_checks` (the
  tool's certificate of `rect(n, m)`: `5 + 7·max(0,n) + 6·max(0,m)·max(0,n)`),
  `prodCert_5_rejected`, `prodCert_cost`. 451 theorems, about 10,300 lines, standard
  axioms only. The JSON format gains an optional field `q`; old certificates are still
  accepted (all kernel certificates and the fixtures re-checked).
- **Generator**: the product where it used to give up ("symbolic entry bound with a
  symbolic body bound"); calls instantiate quadratic callee bounds; C++ replicas
  `QT`, `sbMul` (trims the coefficient lists as the JSON does, keeps `kl` as written).
  Interpreter `cert_interp.py` evaluates `q`. Tests: `Symbolic.ProductOfParameters`, the
  expectation of `Symbolic.BoundInTheParametersWithoutRanges` changed (the nest is now
  certified), fixture `products.json` in the mutation test (113 mutants, all rejected).
- **Results**: TPDB without ranges 147 certified for all inputs (103), 133 with a bound in
  the parameters, for 34 of which KoAT2 also reports `O(n²)`; all accepted. TACLeBench and
  the ranged TPDB mode unchanged. Times on an idle machine: kernels 2 min 19 s (1 min 53 s:
  `ludcmp_test` now goes further before its certificate fails), sequential/app 23 min,
  TPDB 20 min.
- **Not done**: recursion in the checker (design recorded in `docs/proposals.md`, step
  18: rank variable, `callRec` node, `check_sound` generalised by a predicate on the
  valuation; low industrial priority); stack bounds for recursion (nothing to test on).

51. "I really think that code macros for cost guards to be checked should be expressed in time and not in operation counts to be useful in industrial terms. Maybe integrating something like OTAWA inside the plugin would help ? Any better idea or intuition about this ? Do not change anything about this for the moment, I only want to discuss about it with you"

What the AI did for 51: discussion only, no change. Answer: time is a property of the
binary on a processor, so a time budget is checked after linking (flow facts exported by
the plugin, OTAWA, aiT or the Cortex-M0 model, clock frequency from a target profile),
while the compile-time check stays in units; a calibrated time estimate at compile time
would be an early warning, not a proof; sound timing is credible on predictable cores;
research direction: a certificate of the binary's cycles checked by the same checker,
relative to a trusted timing table.

52. "I agree with you, I would like to work  on the linker in the cases you described, keep the current course, thank you for explaining all this"

What the AI did for 52 (Claude Opus 5.5, 2026-11-17).
- Finished the round of prompt 50 (benchmarks re-run on an idle machine, documents).
- **Time budgets checked after compilation**: macros `CROSSCHECK_DEADLINE_CYCLES(n)` and
  `CROSSCHECK_DEADLINE_US(n)` (real-time profile; the budget is recorded in the report,
  `deadline_cycles`/`deadline_us`, not checked by the plugin); `scripts/crosscheck_link.py`
  computes the cycle bound of each such function on the compiled Cortex-M0 code from the
  plugin's loop bounds (debug-line matching and timing table of `benchmarks/cycles`),
  converts with `--clock-mhz`, prints what is trusted, and exits 1 if a budget is
  exceeded or a bound is missing (a post-build step). Test
  `time_budgets_after_compilation` (`tests/c/time_budget.c`: two functions within budget,
  one over). Not yet: other processors, OTAWA/aiT back ends, whole linked images across
  files, a certificate of the binary's cycles.

53. "Proceed with the next steps"

What the AI did for 53 (Claude Opus 5.5, 2026-11-17): the linker work of prompt 52.
- **Whole linked programs**: `crosscheck_link.py` takes one `--report`/`--source` pair per
  translation unit and a binary that may be a linked executable (`m0.load` reads ET_EXEC
  for static analysis: the code region rebased; `wcet.line_table` keys lines by file).
  ctest `time_budgets_after_compilation` also checks a program of two files linked at the
  addresses of a microcontroller (bound 2,686 cycles; an emulated run of the same code,
  merged with `ld -r`, takes 2,367).
- **Other processors through OTAWA**: `benchmarks/cycles/otawa_flow.py` matches the loops
  of OTAWA's own graphs (`mkff`, `dumpcfg --cfg-raw -S`) with the source loops by debug
  lines and writes flow facts; a call graph from the disassembly refuses recursion,
  indirect calls/jumps, jump tables, branches into other functions and calls of undefined
  symbols; `test_otawa_flow.py` (CI) tests these rules. `crosscheck_link.py --processor
  stm32f4|stm32h7` uses OTAWA's `stm32` script (Cortex-M4, Cortex-M7) in a container
  without network. Defects found and fixed during the work: OTAWA loads `<binary>.ffx` by
  itself (a stale file hid loop headers; now removed first, and such output is refused);
  the `-S` output of OTAWA's tuned graph drops edges into IT-block copies (the raw graph is
  used); linker padding decoded as a branch (instructions past the symbol size ignored);
  `blo` taken for a call.
- **Measured**: `run_otawa.py --matching otawa --check`: identical OTAWA bounds to the
  `wcet.py` matching for all 107 Cortex-M0 functions, no bound below a run.
  `run_stm32.py` (new): TACLeBench compiled for a Cortex-M4 with FPU; OTAWA bounds 168 of
  267 functions (STM32F427) and 162 (STM32H753, 6 timeouts), 106 of the 107 bounded on the
  Cortex-M0, 62 more (57 of them use single-precision floating point); not checked against
  executions; OTAWA's M4 latencies are not from the datasheet (its own comment). Paper II
  paragraphs "Time budgets" and "Other processors", the READMEs, guide 03/07, proposals
  step 17, CLAUDE.md.
- **Not done**: aiT (not available here); a certified cycle bound of the binary.

54. "Proceed with this next step"

What the AI did for 54 (Claude Opus 5.5, 2026-11-17): the certified cycle bound of the
binary (the research step of prompts 51-53).
- **Prior work searched and read** (Sections
  2.2 and 3.4): Maroneze, Blazy, Pichardie and Puaut validate in Coq the solution of the
  IPET program of their WCET estimation with a Farkas certificate, and prove the ILP
  generation against CompCert's assembly semantics, with one cycle per instruction. The
  new certificate is the same idea (weak LP duality, Schrijver; IPET, Li and Malik), in
  the form of node potentials and row multipliers, with costs on edges and calls bounded
  by the callees' claims; the generation of the graph is *not* proved here (trusted).
  Paper I cites them before the statement.
- **Lean** (new modules `CyclesCore`, no mathlib, and `Cycles`): graphs with weighted edges
  and callees, rows on edge counts, certificates (scale, potentials, multipliers, bound),
  executable `checkFn`/`checkProgram`; runs indexed by call depth (`Run`), `walk_bound`
  (telescoping potentials), `sum_dot`, `cycles_sound`, `program_sound` (by induction on
  the depth of calls: circular claims of recursive functions are sound for completed
  runs); example with `decide` (`exLoop_checks`, `exLoop_tight`: a bound one below the
  worst case is rejected) and a run satisfying the hypotheses (`exLoop_run`). Axioms: the
  three standard ones. 463 theorems.
- **Checker program**: format `crosscheck-cycles` (`docs/certificate-format.md`), calls by
  name; the JSON conversion is trusted as before.
- **Producer** `benchmarks/cycles/ipet.py`: the CFG of `wcet.py` (refactored into `cfg` and
  `loop_structure`, bounds unchanged: 107/107 identical) with edge costs (branch taken 3,
  not taken 1), one row per matched loop, the dual multipliers from scipy's HiGHS, made
  integer, potentials by Bellman-Ford longest paths. `run_cycles.py --certify DIR --checker`,
  `crosscheck_link.py --certify` (Cortex-M0).
- **Measured**: all 107 functions with a schema bound certified and accepted; certified
  bound below the schema for 60, equal for 47, never above (median ratio 0.998, smallest
  0.72); no violation on the 11 calls compared; entry functions 1.06-1.94 times the
  observed cycles (schema: 1.24-2.49); 2.6 min for all kernels.
- **Tests**: `test_ipet.py` (14: exact bound of a function with a known worst case, call
  composition, no certificate without a loop bound; altered bound, callee bound,
  potentials, multiplier, removed row, raised edge weight, zero scale, unknown callee must
  be rejected), in CI with the Lean job checking every kernel's certificate; ctest
  `time_budgets_after_compilation` also runs `--certify` and requires a lowered bound to
  be rejected.
- **Documents**: Paper I subsection `subsec:cycles` (Definition `def:cycle-certificate`,
  Proposition `prop:cycles` with proof, Table 1 row, scope list), Paper II paragraph
  "Certified cycle bounds", READMEs, `formalization.yaml`, CLAUDE.md, guide, proposals.
- **Not done**: certificates for the OTAWA processors (their timing is OTAWA's, not a
  table); proving the graph extraction (a verified decoder of the binary and timing table
  in Lean).

55. "Proceed with Proving that the graph matches the binary, which needs a decoder and timing table in Lean, as Maroneze et al. did for CompCert."

What the AI did for 55 (Claude Opus 5.5, 2026-11-17).
- **Prior work searched and read** (contributions,
  Sections 2.4 and 4.1; `fox2010trustworthy.pdf`, abstract and introduction): Sewell, Kam
  and Heiser obtain the seL4 binary's CFG from a decompiler proved (HOL4) against the
  Cambridge ARM model of Fox and Myreen (validated on hardware), and leave as future work
  the proof that the CFG given to Chronos captures the binary's control paths. Both DOIs
  checked on Crossref; bibliography entries `sewell2017high`, `fox2010trustworthy`.
- **Lean** `ThumbCore` (no mathlib): `decode` (ARMv6-M Thumb, effect on the PC, Cortex-M0
  cycles, the same table as `m0.py`), `trans`, `closed`, `medges`, `buildFn`,
  `checkBinary`. `Thumb`: the PC-level semantics `Step`/`MRun` (data abstracted; an
  address without code or an unmodelled instruction allows any step), `chain_walk`,
  `translate` (every machine run is a run of the built graph, same cost and row values),
  `binary_sound`; example with `decide` (68-cycle loop accepted, 67 rejected) and a run
  satisfying the hypotheses. Three standard axioms; 476 theorems.
- **Checker program**: format `crosscheck-binary-cycles` (code, instruction addresses, rows
  on address pairs, certificate) and `--decode` (for differential tests).
- **Producer** `ipet.py` now emits that format (instruction-level graph, same LP).
- **Measured**: same 107 bounds as the graph-level certificates, all accepted (223
  functions with the run-time routines, 8,333 instructions, checked in 0.15 s); run 2.8 min.
  `test_thumb.py`: Lean decoder = `m0.py` on all 131,072 cases (every halfword followed by
  two second halfwords), = llvm-objdump on 24,285 kernel instructions (kind, size,
  target); a wrong MULS setting is detected.
- **Tests**: `test_ipet.py` (17, incl. altered code: a slower instruction, an indirect
  branch; an instruction missing from the list; a missing callee), `test_thumb.py`, both
  in CI (the Lean job downloads the certificates and the objects); TOR-11.
- **Documents**: Paper I `def:machine-run`, `thm:machine-cycles` (proof, Table 1 row,
  scope list), Paper II "Certified cycle bounds", READMEs, certificate format, guide,
  CLAUDE.md, proposals, plan.
- **Not done**: a decoder validated on hardware or derived from Arm's machine-readable
  specification; the copy of the code into the certificate is not checked against the ELF
  file by the checker; the OTAWA processors.

56. "How could we further improve the scientific relevance and industrial value, what is the next logical thing to do ? Also, look into author todos to see if some can be treated by you."

What the AI did for 56 (Claude Opus 5.5, 2026-11-17): a recommendation (discussion, in the
conversation) and the author todos it could treat. Of the 9 `\authortodo`, 3 are the
author's by nature (responsibility statements in both papers; whether to report the
`filterbank` case to oRange's authors) and 1 (attributions to Healy et al. and Albert et
al.) asks the author to confirm what was read. For the 5 papers not obtained, a new search
found an open copy of Nielson's 1984 Edinburgh thesis, from which `nielson1987hoare`
derives: read (abstract, contents), added to the bibliography as `nielson1984hoare` (no
DOI; handle checked on the archive) and cited with the journal paper; the `\authortodo`
reduced to confirming the attribution. No open copy of `necula1997proof`,
`demichiel2008orange`, `albert2011more`, `joseph1986finding`, `puschner1989calculating`.

57. "I do not feel like reporting the filterbank discrepancy to the oRange authors, maybe after the paper has been accepted and reviewed. I added nielson1987hoare.pdf to the references, check if you can read it."

What the AI did for 57 (Claude Opus 5.5, 2026-11-17).
- **Author decision recorded**: the `filterbank` discrepancy is not reported to oRange's
  authors before acceptance; the corresponding `\authortodo` of Paper II is removed (the
  text describing the case is unchanged).
- **`nielson1987hoare` read** (the PDF provided by the author, not committed): abstract,
  Section 1, Section 3 (system R, rules R-1 to R-6). Paper I now says that Nielson's logic
  proves total correctness with a time bound in the initial values and that its loop rule
  bounds the unfoldings by a natural-number variable (R-3, R-4), and, after
  `prop:summary-call`, that its second statement is Nielson's composition rule R-3. The
  `\authortodo` now asks to confirm these two attributions.

58. "I added puschner1989calculating.pdf joseph1986finding.pdf healy2000supporting.pdf necula1997proof.pdf demichiel2008orange.pdf"

What the AI did for 58 (Claude Opus 5.5, 2026-11-17): read the five files (not committed);
reading notes in the reading notes.
- `puschner1989calculating`: read entirely. Confirms the timing-schema attribution of
  Paper I; one sentence added to Paper I's related work ("WCET analysis"): Puschner and Koza's
  markers, scopes and loop sequences bound execution counts, constraints of the kind IPET
  expresses linearly (`li1995ilp`). Removed from Paper II's reading `\authortodo`.
- `necula1997proof`: a scan; text obtained by OCR (tesseract) and Sections 1, 2, 6, 7 read.
  Confirms the citation for the principle; Paper I's sentence now says what the principle
  is (the producer supplies a proof, the consumer validates it by a simple algorithm); its
  `\authortodo` removed.
- `healy2000supporting`: the journal version; Section 5 agrees with the preprint read
  before. Paper I's `\authortodo` now says the journal version was read.
- `demichiel2008orange.pdf` is not the cited RTCSA paper but a six-page summary of it by
  Bonenfant, de Michiel and Sainrat (September 2008); read entirely, consistent with Paper
  II's description of oRange. Not cited (venue unknown); Paper II's `\authortodo` now says
  the paper itself is still unread and the summary was read.
- `joseph1986finding.pdf` is another paper (O'Rourke et al., minimal enclosing triangles,
  J. Algorithms 1986); the `\authortodo` of Paper I is unchanged and the author is told.

59. "look at joseph1986finding_bis.pdf conf-vmcai-AlbertGM11.pdf demichiel2008orange_bis.pdf"

What the AI did for 59 (Claude Opus 5.5, 2026-11-17): read the three files (not committed);
notes in the reading notes.
- `joseph1986finding` (a scan, OCR with tesseract): read entirely. The `\authortodo` of
  Paper I is removed; after `thm:response-time` Paper I now says that the iteration is
  Joseph and Pandya's function Response, and that their analysis starts at the critical
  instant whereas the theorem bounds every schedule with no activation pending at slot 0.
- `albert2011more`: Sections 1-4 read; the attribution of Paper I agrees. The Healy/Albert
  `\authortodo` now only asks the author to check the two attributions.
- `demichiel2008orange` (the RTCSA paper): read entirely. Paper II's description of oRange
  now takes the context tree with expanded calls (no recursion) from the paper and marks
  "multiple returns" as from the documentation; the oRange part of Paper II's
  `\authortodo` is removed (Shaw and Albert 2011 TOPLAS remain cited through other sources).

60. "Start on the binary loop-bound certificates"

61. (sent while 60 was in progress) "I added shaw1989reasoning.pdf and albert2011closed.pdf and replaced most of remaining authortodo, fix the remaining ones"

What the AI did for 61 (Claude Opus 5.5, 2026-11-17): read both files (not committed);
notes in the reading notes. `shaw1989reasoning`: Sections I-III; confirms the
timing-schema citations; Paper I's `subsec:cost-logic` now also says that Shaw extended
Hoare logic with a real-time variable. `albert2011closed`: abstract, Section 1 and the
passages on ranking functions and maximization; confirms the citations. The author
replaced the two responsibility `\authortodo` with statements of their own (not changed
by the AI). On the author's instruction the three remaining `\authortodo` were removed:
Paper I, confirmation of the attributions to Nielson (R-3, R-4) and to Healy et al. and
Albert et al. (the AI read the cited passages, see the reading notes); Paper II, the
note that Shaw and Albert 2011 (JAR) were cited through other sources (now read). No
`\authortodo` remains in either paper. The work for 60 is recorded separately when done.

What the AI did for 60 (Claude Opus 5.5, 2026-11-17/18): loop bounds certified on the
Cortex-M0 machine code, so that the loop rows of the cycle certificates need not be
trusted.
- Prior work searched and read (not kept): Sewell, Kam and Heiser
  (RTAS 2016, `sewell2016complete`), Crary and Weirich (POPL 2000, `crary2000resource`),
  Cullmann and Martin (WCET 2007, `cullmann2007data`); Blackham and Heiser's Sequoll (RTAS
  2013) and Aspinall et al. (TCS 2007) were found but not obtained or not read, and are
  not cited. DOIs checked on Crossref/DataCite.
- Lean: `ThumbDataCore` (no mathlib: the effects of the instructions on r0-r7 and the
  flags, `Thumb.effect`, flags of AddWithCarry, conditions, the conditions as linear facts,
  certificates `DFun`/`LoopCert`, `obligations`, `loopRow`, `checkData`) and `ThumbData`
  (data runs `DRun`; `condFacts_sound`, `postE_eval`, `step_ok`, `chain_ok`, `chain_rows`,
  `drun_mrun`, `data_sound`; example `exData_checks`/`exData_tight`/`exData_sound` by
  `decide`). 68 theorems, no axiom beyond the standard three. `MRow` derives `DecidableEq`.
  No data run of the example is constructed in Lean (stated in Paper III).
- Checker program: format `crosscheck-binary-cycles` version 2 (fields `loops`, `kinds`,
  `inv`, `proofs`, `abi`; the rows of certified loops are generated by `loopRow`); option
  `--effect` for differential tests.
- Producer `benchmarks/cycles/binloops.py` (untrusted): zone analysis, potentials,
  Farkas proofs (shortest paths, negative cycles, linear program with a safety margin
  after a tolerance failure was found), weakening of what cannot be proved; wired into
  `ipet.certify(loops=True)` and `run_cycles.py --certify-loops [--abi]`.
- Tests: `test_effect.py` (Lean effects/flags/conditions vs `m0.py` on every encoding, 3
  states each, with and without `abi`: 297,244 executions, 0 differences; an earlier
  version of the test corrupted its own code region through stores and was fixed by
  moving the code above the data), `test_binloops.py` (14 tests, must-reject mutations);
  CI updated; qualification TOR-12.
- Results (TACLeBench kernels, Cortex-M0): 72 of the 403 loops of the kernels' own code
  certified (94 with `--abi`), none of the 116 loops of the division routines; all
  certificates accepted; no back-edge count of the emulated runs above a certified bound;
  115 functions with a certified cycle bound (107 before).

62. (sent while 60 was in progress) "As you suggested, put the work on binaries on a third paper"

What the AI did for 62 (Claude Opus 5.5, 2026-11-18): Paper III
(`paper/binary/crosscheck-binary.tex`, 13 pages): Paper I's `subsec:cycles` (cycle
certificates, machine code: definitions, proposition, theorem and proofs moved verbatim,
the last paragraph adapted) and Paper II's paragraphs on the Cortex-M0 binaries (cycles,
certified cycle bounds, OTAWA, other processors, stack, time budgets) moved; new
introduction, related work, Section "Loop Bounds on the Machine Code" (`def:data-run`,
`def:loop-certificate`, `lem:cond-facts`, `thm:machine-loops` with proofs), evaluation of
the loop certificates, mechanization table `tab:lean3`, limitations, conclusions, and a
statement on the use of AI with an `\authortodo` (responsibility; the three new
attributions). Papers I and II: the moved material replaced by pointers to
`crosscheckBinary` (bibliography entry added); Paper I's Table 1 row and not-mechanized
item for cycles removed; in the AI statements of Papers I and II (the author's own
sentences are unchanged) the lists of what the assistant wrote no longer name the moved
work. Paper I: 41 pages, Paper II: 23, Paper III: 13; all three build with no warning.
`formalization.yaml` gains a `paper:` field; `CLAUDE.md` describes the three papers.

63. "Model stack slots"

What the AI did for 63 (Claude Opus 5.5, 2026-11-18): the data semantics of Paper III
extended with the stack pointer and memory, so that loop counters kept in the frame can be
certified.
- Lean `ThumbDataCore`: `stackEffect` (the effect of each instruction on SP, memory and
  SP-relative loads: SUB/ADD SP, PUSH, POP, STR/LDR through SP, other stores and calls;
  whether it puts an address of the frame in a register), `MState` gains `sp` and `mem`;
  certificates gain per-instruction SP offsets (`spOff`), tracked words of the frame
  (`slots`, variables `20 + j`) and a per-function assumption `frame`; `postS` (values
  after an instruction, tracked words included), `spOk`, `slotsOk`, `stackWf`; the checker
  refuses `frame` for a function that takes an address of its frame. `abi` now also covers
  SP. `ThumbData`: `StackOk`, `DChain` with the entry SP, `postS_eval` (address arithmetic
  modulo 2^32 by `omega`), `step_ok`, `chain_ok`, `chain_rows`, `drun_mrun`, `data_sound`
  redone; 77 theorems in the module, 553 in all; three standard axioms. The example
  (`exData_*`) unchanged in substance.
- Checker program: fields `sp`, `slots`, `frame`; `--effect` also prints the stack effect.
- `test_effect.py`: the stack effects compared with `m0.py` (SP, the memory window around
  SP, SP-relative loads) on every encoding: 297,244 executions, no difference.
- Producer `binloops.py` rewritten around post-expressions (registers, ghosts, tracked
  words): SP offsets by data flow, tracked words accessed through SP in loops, zones over
  registers and words, potentials over words too; prover restricted to the variables in use.
  `ipet.certify(frame=...)`, `run_cycles.py --frame`.
- `test_binloops.py`: 18 tests (counter in a stack slot certified with no assumption; with a
  call in the loop only under `abi` and `frame`; must-reject: another slot, a wrong SP
  offset, an entry offset other than 0, a store to another word, `frame` removed, an
  address of the frame taken).
- Results (TACLeBench, Cortex-M0): kernels' loops certified on the code 73 (72 before), 105
  with `abi` (94 before), 107 with `abi` and `frame`; functions with a certified cycle
  bound 115, 117 with `frame`; all certificates accepted; no run above a certified bound.
  The gain is limited because `frame` is refused in 192 of 267 functions (191 frame-pointer
  prologues `add r7, sp, #i`); reported in Paper III and the README, with two options for
  the author: compile without frame pointers, or refine the escape analysis.
- Paper III: Definitions `def:data-run` and `def:loop-certificate`, the proof of
  `thm:machine-loops`, the producer description, the evaluation and the counts updated;
  Paper I: the development counts (10,300 lines and 451 theorems for Paper I; 2,900 and 102
  for Paper III's modules).

64. (sent while 63 was running) "While you wait for results, I need you to redo the guide : I cannot follow it, the previous version was better. Too many details are missing, paragraphs make almost no sense to a prophan. Many thongs are not explained. Some parts could have graphic examples such as potential dominance using math functions ? What are the underlying bricks, Farkas checks, z3 intervals, Fourier etc ? Make a better, even if lengthier, work here please"

What the AI did for 64 (Claude Opus 5.5, 2026-11-18): the companion guide rewritten for a
non-specialist (about 1,650 → 3,300 lines, 9 parts).
- New Part 1 (the big picture, the FIR example followed from source to checker output, run
  for the purpose: 331 units, potential `16 − k`, `3 + 339·n`; the trust table) and Part 2
  (the toolbox: one section per building block with intuition, worked numbers, where it is
  in the code and pitfalls: potentials, invariants and Houdini, linear constraints,
  Farkas' Lemma and the checker's `entails1`, LP duality and IPET with its dual, Z3's three
  uses read from `Solver.cpp` (entailment, intervals re-proved by entailment, potential
  synthesis through Farkas), intervals and calling contexts, Fourier–Motzkin, zones and
  shortest paths, abstract interpretation and widening, the timing schema and envelopes,
  recursion, certificates and Lean, the Cortex-M0).
- Papers I, II and III each explained in their own part (Part 5 new: the 68-cycle example
  checked edge by edge, the loop certificate of the same code checked by hand); plugin,
  Lean, bibliography and expert parts renamed and updated (Lean modules `ThumbDataCore`,
  `ThumbData`; the bibliography's "Read" column regenerated from the reading notes;
  machine-code questions; stale numbers fixed).
- Nine figures drawn by `docs/guide/tools/figures.py` (plain SVG: potentials along runs, a
  data-dependent step, cost envelopes of a triangular nest, a logarithmic loop, Farkas in
  the plane, calling contexts, widening, the potentials of a cycle certificate, execution
  times and bounds); the PDF builder rewrites image paths.
- Found while checking the code: the certificate generator does use Fourier–Motzkin
  (`eliminate` in `Cert.cpp`, capped at 64 constraints) — the previous guide said "FM" in a
  diagram without explanation; the new Part 2 says where and why. Paper II's abstract still
  said 103 of 553 TPDB programs certified where its text says 147 (the count before
  quadratic bounds): corrected.

65. "Your choice about what to do now, what I want is to keep improving scientific relevance, better benchmark results, more cases covered, apply well known techniques, augment industrial values by checking on known cases, make the papers sound and solid"

What the AI did for 65 (Claude Opus 5.5, 2026-11-18), first part: Paper III said that no
data run of its example was built in Lean, so the hypotheses of `data_sound` were only shown
satisfiable informally. Added to `ThumbData.lean` a concrete simulator (boolean checks
`effOkB`, `chainB`, `dOkB` on concrete registers and flags, with soundness lemmas
`effOkB_sound`, `stackKeep_sound`, `chainB_sound`, `dOkB_sound`) and `exData_run`: the
counting loop has a data run of exactly 68 cycles, so the hypotheses are satisfiable and
the certified bound is attained (8 theorems; 561 in all). Paper III, Table `tab:lean3`,
`formalization.yaml`, CLAUDE.md and the guide updated. `run_cycles.py` gained `--cflag`
and `--tag` to measure another build (here `-fomit-frame-pointer`) without replacing the
published one.

Second part (same prompt, 2026-11-18): **congruences modulo powers of two** in the loop
certificates of machine code. Of the loops the producer could not bound on the code, 177 of
210 left their loop on equality (`bne`): a counter stepped by 4 that exits at 80 is not
bounded by zones, since `x ≤ 80 ∧ x ≠ 80` gives `x ≤ 79`, not `x ≤ 76`. The well-known remedy
is Granger's congruence analysis (Int. J. Computer Mathematics 30, 1989; metadata checked on
Crossref, text not obtained: attribution flagged in Paper III's `\authortodo`).
- Lean (`ThumbDataCore`, `ThumbData`): certificates carry congruences `x ≡ r (mod 2^e)`,
  `e ≤ 32` (so that wrapping modulo 2^32 keeps them), checked along every transition and wrap
  case by divisibility on the post-expressions, without Farkas certificates (`congOk`,
  `congPE_sound`); none at the entry; at a branch, the facts on the difference of the ghost
  operands are rounded to multiples of `2^e` (`gExp_dvd`, `tightenL_holds`,
  `condFactsM_sound`); `Inv` carries the congruences, `step_ok` and the entry updated,
  `data_sound` unchanged in its statement. Example `exStep_*`: `movs r0,#0; L: adds r0,#4;
  cmp r0,#40; bne L` certified at 52 cycles (the worst case), the same certificate without
  congruences rejected, by `decide`. 581 theorems; only the three standard axioms.
- Checker program: field `"cong"` parsed and reported.
- Producer (`binloops.py`): congruences computed on the checker's own post-expressions (so
  that the checker accepts what is derived), used to round branch facts in the zone analysis
  and in the obligations. Tests (`test_binloops.py`, class `Congruence`): the loop is
  certified only with congruences; six mutations rejected (no congruence, wrong residue, one
  at the entry, exponent 33, a variable of a transition, the step changed from 4 to 3 in the
  code, which makes the loop endless).
- Found while testing: `ipet.py` rounded the LP's multipliers up first and kept them if
  feasible, which is loose for rows of scale above 1 (79 instead of 52 cycles on the
  example); it now keeps the smallest feasible bound among the rounded and the exact
  fractional multipliers (sound either way: the checker decides). On the kernels it lowers
  10 certified bounds (up to 8 %) and raises none.
- Measured: `-fomit-frame-pointer` build (separate objects, `--tag .nofp`), before
  congruences: loops certified on the code 77 / 109 / 129 (none / abi / abi+frame) instead
  of 73 / 105 / 107, functions with a certified cycle bound 118 instead of 117.
- Results with congruences (default build): kernel loops certified on the code 116 / 167 /
  169 of 403 (none / abi / abi+frame; before: 73 / 105 / 107); every certificate accepted;
  no emulated run above a certified bound; remaining failures with abi+frame 151 / 42 / 21
  / 12 / 8 (counter without potential / compared value not tracked / SP offset unknown /
  unmodelled flags / mixed). Paper III (definition, rounding after `lem:cond-facts`,
  producer, evaluation, `tab:lean3`, related work), `benchmarks/cycles/README.md`,
  `docs/certificate-format.md`, the guide (Part 2: a section on congruences with a figure;
  Parts 5 and 9) and the reading notes updated.
- Without frame pointers, with congruences: `frame` refused in 25 of 265 functions (190 in the
  default build); loops certified 120 / 173 / 202; 118 functions with a certified cycle
  bound; all accepted, no violation. Reported in Paper III and the README as a separate
  build; the default build's figures are unchanged (OTAWA runs not redone).

66. "Proceed with the next step as you are proposing"

67. "Those tests are taking hours on multiple processors, I feels that something is wrong, what do you think?"

68. "I added cullmann2007data.pdf crary2000resource.pdf sewell2016complete.pdf granger1989static.pdf and fixed the authortodo, read them and adapt the corresponding lines"

What the AI did for 66 and 67 (Claude Opus 5.5, 2026-11-18): **potentials per instruction by
linear programming** in the producer of loop certificates on machine code
(`binloops.synth_lp`): when the potential search with one linear part for the whole loop fails
(the counter moves between a register and a word of the frame inside the loop, e.g. the outer
loop of `matrix1_main` at `-O1`), one linear program over the checker's own obligations, with
the potentials and the Farkas multipliers as unknowns, minimizes the bound (Colon and Sipma
2001; per control point, Alias, Darte, Feautrier and Gonnord 2010: Sections 1 to 3.1 read).
The rational solution is rounded and proved again with exact arithmetic; the checker and the
Lean proofs are unchanged (the certificate format already allowed a potential per
instruction). Test `PotentialsPerInstruction` (`test_binloops.py`): a loop certified only with
the linear program (9 back edges, 114 cycles, instead of the trusted source row, 125), and four
altered certificates rejected (bound 8, the header's potential everywhere, a constant too
small, the loop's store removed: endless loop). Prompt 67: the first measurement runs hung for
about six hours, because HiGHS did not terminate on a badly scaled linear program of
`jfdctint` (constants up to 2^32) and no time limit had been set; the runs were stopped, the
cause found by dumping the stack, and each solve is now limited to 5 s (a loop whose program
times out stays uncertified; soundness is unaffected, the checker decides). The runs were
restarted. Results (all certificates accepted, no emulated run above a certified bound, no
loop lost, no certified bound higher): kernel loops certified on the code 121 / 173 / 175 of
403 (none / abi / abi+frame; before 116 / 167 / 169), and 123 / 176 / 216 in the build
without frame pointers (before 120 / 173 / 202); remaining failures with abi+frame 145 / 42 /
21 / 12 / 8. Runs now take 11 to 70 minutes (5 to 32 before; `pm` alone up to 55). Paper III
(abstract, which still quoted the counts from before congruences, 73 / 105 / 107; producer;
evaluation), `benchmarks/cycles/README.md`, the guide (Parts 5 and 9), CLAUDE.md updated.
The new loops of `isqrt_usqrt` keep their counter in a register: why the single-linear-part
search fails there was not analysed, and the paper does not claim a reason for them.

What the AI did for 68 (Claude Opus 5.5, 2026-11-18): read the four papers in full (copies
supplied by the author, not committed) and adapted Paper III: `cullmann2007data` (counters in
memory, also modified through pointers, through the value analysis; intervals of iteration
counts; after the pattern-based analysis), `sewell2016complete` (their binary example is a
register stepped by 4 leaving on inequality with 256, bounded with the divisibility of its
initial value; 47 of 67 seL4 loops bounded from the binary alone, failures for lack of a memory
aliasing analysis and of invariants maintained by the loop's environment), `crary2000resource`
(time counted in function calls in the calculus but in backward jumps in TALres; virtual
clock attributed by them to Necula and Lee; soundness by type safety, on paper),
`granger1989static` (the rounding of the branch facts is the reduction of his product of
congruences and intervals, Proposition 6.1, applied to a difference; it replaces the earlier
comparison with cutting planes). The author had replaced the `\authortodo` of the statement
on the use of AI with their own statement; its last clause (the former instruction to confirm
the attributions) was replaced by "The AI assistant checked the attributions to [the four
papers] against the full texts of these papers, which the author supplied." Note for the
author: text added to Paper III after that statement (the related-work changes above and the
evaluation of prompt 66 when it is written) is not covered by it until the author reads it.
the reading notes (four rows), the guide (Part 2 rounding paragraph, Part 8 map)
updated. Papers I, II and III build without warnings (Paper III: 16 pages).

69. "proceed with the next logical step"

What the AI did for 69 (Claude Opus 5.5, 2026-11-19): diagnosed the 145 loops "counter
tracked, no potential" of the default build: 139 are in functions where `frame` is refused,
almost always only because of the frame-pointer prologue `add r7, sp, #i`; r7 is otherwise
read in 14 instructions of all kernels' code (loads of stack arguments `ldr rX, [r7, #i]`,
and `subs r6, r7, #i`). An experiment on those 68 functions, treating that instruction as not
escaping, certified 16 more loops (`fir2dim`, `ludcmp`, `minver`). Lean change (checker
only): `ThumbDataCore.frameUseOk` replaces the condition "no instruction escapes" by "no
instruction escapes except `ADD r7, SP, #i`, and, in a function with that instruction, no
instruction may read r7 (`regsRead`, an over-approximation by encoding) except as the base
address of a load or a `PUSH` at the entry". This condition only restricts where the trusted
assumption `frame` may be stated; the soundness proof (`data_sound`) never used the escape
condition, and the meaning of `frame` (`StackOk`) is unchanged; `lake build` clean, no new
axioms. The producer mirrors it (`binloops.frame_use_ok`, `regs_read`). Test `FramePointer`
(`test_binloops.py`): a counter in the frame across a call behind the prologue is certified
(9 back edges); the checker accepts the certificate with the placeholder replaced by
instructions of the same cycles that do not read r7 or read it as a load base, and rejects it
when r7 is read otherwise (`mov r8, r7`, `add r8, r7`, `str r1, [r7]`, `str r7, [r7]`,
`stm r7!, {r0}`) or when `frame` is removed. The Python and Lean versions of `regsRead` are
not compared on every encoding (they are not part of the soundness argument). Results
(full runs with `--abi --frame`, checker rebuilt): kernel loops certified on the code 175 ->
215 of 403 in the default build (12 kernels; `minver` 10 -> 22, `countnegative` 6 -> 12, `pm`
29 -> 34), 216 unchanged in the build without frame pointers; no loop lost, no certified bound
higher, every certificate accepted, no emulated run above a bound; 117 functions with a
certified cycle bound (unchanged). `frame` refused in 26 of the 265 functions the producer
analyses (190 before). Remaining failures 106 / 42 / 21 / 12 / 7; of the 106, 89 are in
functions where `frame` is allowed, and their causes were not analysed. The run takes 58
minutes (32 before). Paper III (the rule in Section `sec:loops`, abstract, evaluation,
limitations, conclusion: the earlier remark that omitting the frame pointer is worth a
compilation option was removed, the two builds now differ by one loop), the cycles README,
the guide (Parts 5 and 9), CLAUDE.md updated. This text of Paper III is new since the
author's statement on the use of AI.

70. "Proceed by classifying the remaining cases to identify the next steps"

What the AI did for 70 (Claude Opus 5.5, 2026-11-19): wrote `benchmarks/cycles/classify_loops.py`
(heuristic diagnosis, untrusted, proves nothing): for each exit of an uncertified loop, the
instruction that set the flags and the definitions reaching its operands along paths inside
the loop, through registers and tracked words of the frame; for counters, the definitions of
the initial value. A first version that merged all definitions of a register in the loop was
discarded as too coarse (registers are reused). On the run with `--abi --frame` (default
build), the 188 kernel loops fall into: 69 counter against a constant or bounded limit (initial
value from a frame word 12, built by LSL 10, LSR of an argument 9, argument 6, MVN 5, literal
pool 4, through STM 4, ...), 27 counter against an unbounded limit (a parameter), 22 exit on a
call's result (mostly soft-float comparisons), 17 exit on loaded data, 12 exit on the flags of
a shift, 11 shifted counters (logarithmic), 11 other, 10 untracked frame words, 9 values through
approximated instructions (STM, ADCS, ANDS). An experiment in the producer only (no checker
change, nothing committed in `binloops.py`) with exact effects for STM/LDM write-back, MVN,
NEGS and literal-pool loads found potentials for 15 more loops and lost 3, not analysed. A
first version of the experiment was flawed: it gave every loop a placeholder source bound of 5,
so that the producer discarded larger certified bounds; it was rerun without that filter.
The cycles README records the table; Paper III is unchanged.

71. "I agree start with step 1"

What the AI did for 71 (Claude Opus 5.5, 2026-11-19): step 1 of the plan proposed after prompt
70, exact effects for `NEGS`, `MVNS`, the write-back of `STM`/`LDM` and literal-pool loads, in
the checker's specification and in the producer. First, the 3 losses of the experiment of 70
were analysed: in all three, HiGHS stopped with a numerical failure (status 4) on linear
programs whose zone invariants contained literal constants (addresses close to 2^32, `jpeg`
constants). Lean change (`ThumbDataCore.effect`, trusted specification): `NEGS` = `0 - rn` with
the flags of that subtraction; `MVNS` = `(2^32 - 1) - rn`, flags any; `STM` advances its base by
4 per listed register and writes no register of its list; `LDM` does the same when the base is
not in its list (its list any), otherwise its list any; an empty list makes the base any;
`LDR rt, [pc, #i]` gives the word `l + 65536 u` of the certificate's code at the aligned address
when both halfwords exist and are below 2^16, otherwise any. New trusted assumption, stated in
`ThumbData`, Paper III, `docs/certificate-format.md`: the code is not written during a run. The
proof `data_sound` needed no change (it is generic in the effect); `lake build` and the checker
build clean, no new axioms. Producer (`binloops.py`, `ipet.code_top`): mirror of the effects
(the literal region limited to the checker's code); its own analysis (`aeff`) ignores constants
above `BIG` = 2^20 in zones, handles `imm - reg` with a constant register, tries coarse linear
programs (large constants as variables) after exact ones, and retries a function with literal
loads as any value when a loop is left without a potential, keeping the result that certifies
more loops. A first coarse fallback alone did not recover the losses; the retry did. Tests:
`test_effect.py` 297,244 executions, 0 differences (Lean vs `m0.py`, including literal loads);
`test_binloops.py` class `ExactEffects`: five small loops certified only through the new
effects, and 10 mutations (literal word changed two ways, literal outside the code, `STM`
replaced by `LDM` loading the base or the counter, `NEGS`/`MVNS` operands changed; one `LDM`
variant that must be accepted). Results (all certificates accepted, no emulated run above a
bound, no loop lost, no certified bound changed): kernel loops certified 121 / 173 / 215 ->
131 / 183 / 229 (none / abi / abi+frame; `bitonic`, `fft`, `fir2dim`, `quicksort`, `matrix1`;
6 of the 14 with both assumptions have no source bound), without frame pointers 123 / 176 /
216 -> 135 / 188 / 233; functions with a certified cycle bound unchanged (115 / 115 / 117, 118
without frame pointers). Remaining failures with both assumptions 98 / 36 / 21 / 12 / 7 (before
106 / 42 / 21 / 12 / 7). Runs took 32 to 156 minutes, two at a time on the same machine.
Paper III (effects paragraph, trusted list, abstract, evaluation), the cycles README, the guide
(Parts 5 and 9), `docs/certificate-format.md`, CLAUDE.md updated. This text of Paper III is new
since the author's statement on the use of AI.

72. "Proceed"

What the AI did for 72 (Claude Opus 5.5, 2026-11-19 to 2026-11-20): the next step after the
classification of the uncertified loops (group A, counters against a constant or a bounded
limit). Diagnosis of its "constant initial value" loops: in 7 loops (`fft` x2, `fir2dim` x3,
`bsort` x2) Clang counts from `mvns r1, #7` (2^32 - 8) up by 4 to zero (wrap-to-zero); the
current certificate format cannot express it (the invariant at the exit would need a
disjunction or a relational congruence, Granger 1991); not done, noted as a future option.
Then the counters and limits built by `LSL`: Lean change (`ThumbDataCore`, trusted
specification): new value kind `Val.shl a k` (`a * 2^k mod 2^32`); `LSLS rd, rm, #s` gives
`shl` for `s > 0` and the move `rm + 0` for `s = 0` (flags any, as before); its linear form
(`valE`) is `2^k * a` without overflow and the register's new value (a fresh variable)
with it; `wrapPrem` gives the premise of each case (`0 <= 2^k a <= 2^32 - 1`, or
`2^k a >= 2^32`). Proof (`ThumbData`): `mOf`, `mSel_mem`, `valE_eval` (now split on overflow,
with the old proof as `valE_eval_ar`), `wrapPrem_holds`, `postE_eval`; `lake build` clean, no
`sorry`, `data_sound` still depends only on `propext`, `Classical.choice`, `Quot.sound`. No
new trusted assumption beyond the specification itself. Producer (`binloops.py`): mirror of
the effect, post-expressions of a shifted constant, and two changes to its Farkas search: the
LP fallback now also lists the ranges of the goal's variables as premises, and when the LP's
multipliers are too small to round, the multipliers are solved exactly (Gaussian elimination
over the rationals on the premises with nonzero LP multipliers; first with the constant row
tight, then with the free multipliers at 0); `classify_loops.py` handles the new value kind.
Tests: `test_binloops.py` 26 pass, with a new loop `SHLLOOP` certified only through the exact
shift and five mutations that must be (and are) refused: shift amount 2 instead of 1,
operand 6 instead of 5, overflowing shift by 31, `LSRS` instead of `LSLS`, `LSLS #0` (a move
of an odd value, which breaks the congruence the certificate uses); two of the AI's first
expectations were wrong (it expected the `LSLS #0` variant to be accepted; an `ADDS r1, r0, r0`
variant was dropped because the stored Farkas proofs do not fit its premises); `test_ipet.py`
17 pass; `test_effect.py` 297,244 executions, 0 differences. Results: a first set of six runs
lost one loop (`jfdctint` 0x172: HiGHS failed on its linear program once the frame word holding
`1 << 14` became exact); the producer's second analysis (`lit_any`) was then changed to give
shifts any value as well, which recovered it, and the six runs were made again. Kernel loops
certified 131 / 183 / 229 -> 136 / 193 / 246 (none / abi / abi+frame; `fft`, `filterbank`,
`st`, and `bitcount` with both assumptions; 3 of the 17 gained have no source bound), without
frame pointers 135 / 188 / 233 -> 140 / 198 / 251; no loop lost, no certified bound higher,
four `bitcount` bounds lower (2^31 - 2 -> 255), every certificate accepted, no emulated run
above a bound; functions with a certified cycle bound with both assumptions 117 -> 120 (118 ->
120 without frame pointers); below the source bound 78 (110 with abi), no source bound 58 (83).
Remaining failures with both assumptions 92 / 25 / 21 / 12 / 7 (before 98 / 36 / 21 / 12 / 7);
`classify_loops.py`: 157 loops, group A 62 -> 51, B 26 -> 20.
Runs took 17 to 103 minutes, three at a time. Paper III (data-run definition, effects
paragraph, congruence and case-split sentences, abstract, evaluation, Lean size), the cycles
README, the guide (Parts 5 and 9), `docs/certificate-format.md`, CLAUDE.md updated. This text
of Paper III is new since the author's statement on the use of AI.

73. "Go on improving benchmark scores but first make a complete profiling analysis of crosscheck : I am worried about its performances. Also the development cycle seems pretty slow now, maybe you should run a subset of samples  first then run the full suite afterwards. What would you suggest for a scientic relevance and industrial value improvement now ?"

What the AI did for 73 (Claude Opus 5.5, 2026-11-20): a profile of every part, then changes
to the untrusted producer that leave the certificates identical. Measurements: the Lean
checker takes at most 1.1 s per certificate (6 s for the 29); the Clang analyser 100 s for the
29 kernels (callgrind on `md5`: 92 % of the instructions in Z3 implication checks, much of it
in building and configuring a solver per query; not changed); compilation, emulation and
cycle bounds about 3 minutes per configuration; the loop certification on the binaries 17 to
103 minutes per configuration, `pm` alone 77 of the 103 (`pm_kernel`: 902 instructions, 31
loops, zones of 44 variables; one zone analysis 316 s, 41,376 transfers, 3,019 widenings,
loop headers visited up to 151 times). In the slow functions (cProfile, then a stack sampler,
since `perf` is not permitted on this machine), the Floyd-Warshall closure of the zones took
46-57 %, HiGHS 20-54 % (dual simplex: numerical failures and the 5 s limit; interior point:
infeasible, sometimes contradicting an optimal dual simplex). Changes (exact, checked with
`BINLOOPS_CHECK_CLOSE=1` and by comparing certificate files): joins of closed zones are not
closed again (Mine, PADO 2001: the pointwise maximum of closed difference-bound matrices is
closed), incremental closure in O(n^2) after adding a constraint, the image of a closed zone
completed only on its variables with any value, the analysis before the congruences (its
result was discarded) removed, the empty results of the division routines reused (same
code in every kernel, keyed by bytes, alignment and options). `run_cycles.py --jobs N`;
`compare_runs.py OLD NEW --check`. Results: certificates identical old vs new on 7 kernels
function by function (2.0-2.7x faster), and in whole runs: the run with both assumptions 103
-> 18 minutes (3 processes), its 29 certificate files byte-identical; four other
configurations identical (3, 9, 7, 9 minutes with 4 processes); the sixth (no frame pointers,
both assumptions) ran while the next change (prompt 74) was being written into the
producer and is not a clean comparison (same 251 loops, 4 files with other invariants).
Answered the question on the development cycle (tests, a subset of kernels, one full
configuration, all six only before figures change; written in the cycles README) and gave
suggestions: bit-width potentials for the division routines, which turned out to be wrong
(see 74), parametric bounds on the binary, relational congruences, a NumPy or native port of
the zones, a timing check on hardware, Thumb-2.

74. "Proceed with your plan. Maybe, in the future, rewriting critical parts using a more performant language such as rust or c++ would help ?"

What the AI did for 74 (Claude Opus 5.5, 2026-11-20): answered the question on Rust or C++
(a native module for the zone operations only, not a rewrite: the producer is untrusted and
mirrors the Lean specification by hand, which Python keeps easy to compare; HiGHS is already
C++; the Clang plugin's cost is its use of Z3, not the language). Then the plan of 73, with
one correction: the division routines are not logarithmic loops but `for (i = 31; i >= 0;
i--)`, compiled as `subs r3, r3, #1; adds r4, r3, #1; bhs exit`, whose exit is taken once r3
has wrapped around to 2^32 - 1; a scan found the same exit in all 116 loops of the division
routines and 2 kernel loops. Between the subtraction and the branch the invariant is
`r3 <= 30 or r3 = 2^32 - 1`, which the checker's conjunctive invariants cannot express.
Lean change (checker): `DFun` gains `alt` (further disjuncts per instruction) and `pick`
(the target disjunct of each case `(transition, wrap case, fact, source disjunct)`, default
0); `invsAt`, `tgtIdx`, `tgtInv`; `obsOf` iterates over the source disjuncts and proves the
target disjunct; with `alt` and `pick` empty the obligations are those of before. Proof:
`Inv` says that some disjunct holds; `checkDFun_alt`, `invsAt_wf`, `tgtInv_mem`; `obs_mem`
and `step_ok` with the indices of the fact and of the source disjunct; the entry uses the
first disjunct. `lake build` clean, no `sorry`, `data_sound` depends only on `propext`,
`Classical.choice`, `Quot.sound`; new example `exWrap_checks`/`exWrap_needs_alt`/
`exWrap_sound` (the loop `for (i = 9; i >= 0; i--)`, 63 cycles, by `decide`, generated from
the producer's certificate). `CheckerMain` parses `alt` and `pick`. Producer
(`binloops.py`): windows from an addition or subtraction of a constant that may wrap to the
next conditional branch (straight line, one predecessor each, no loop header); the zone
split into the cases without and with wrap-around, carried separately and joined after the
branch (trace partitioning with merging, Mauborgne & Rival, ESOP 2005, read); the
certificate's `alt`/`pick` by tags. The linear programs failed: HiGHS declared feasible
programs infeasible (shown by fixing a hand-made potential: then solved at once). Added: an
exact contradiction test (a premise violated on the box of the one-variable bounds) in the
Farkas search and to leave impossible cases out of the linear program; retries without
presolve, then with each constant split as q 2^31 + r and the two parts required
separately; then linear parts fixed to a variable that follows a bounded header variable
through the body (exact test on the checker's post-expressions in every disjunct and wrap
case), only the constants unknown. One crash in a full run (an index outside the zone for
the new values of tracked words) was fixed and the run made again. Tests: `test_binloops.py`
28 pass, new class `Disjunctions` (one more iteration, a step of 2, the opposite exit, `alt`
or `pick` removed, a disjunct or a target changed: all refused); `test_ipet.py` 17 pass.
Results (six runs, `--jobs 4`, 6 to 16 minutes each): the 116 loops of the division
routines certified in all six (none before; bound 31, source bound 32); kernel loops 136 /
193 / 246 -> 136 / 193 / 250 (`fft`, `matrix1`, `pm`), without frame pointers 140 / 198 / 251
-> 140 / 198 / 252; 366 of the 519 loops of the binaries with both assumptions; trusted loop
rows in the certified cycle bounds 159 / 153 / 137 -> 43 / 37 / 19 (157 / 152 / 134 -> 41 / 36 /
18 without frame pointers); no loop lost, no bound higher, every certificate accepted, no
emulated run above a bound; remaining failures 88 / 25 / 21 / 12 / 7. Literature checked
for the paper: Mauborgne & Rival 2005 and Gange et al. 2015 (TOPLAS; wrapped intervals; it
names Navas et al. APLAS 2012 as its preliminary version, which could not be downloaded),
DOIs on Crossref, read passages recorded in the reading notes. Paper III (definition
of loop certificates, proof of the theorem, producer paragraph, abstract, evaluation, table
`tab:lean3`, Lean size), Paper I (size of the Paper III modules), cycles README, guide (Parts
5 and 9), `docs/certificate-format.md`, `formalization.yaml`, CLAUDE.md updated. This text of
Paper III is new since the author's statement on the use of AI.

75. "What would you suggest now ?"

What the AI did for 75 (Claude Opus 5.5, 2026-11-20): proposed, in order: the wrap-to-zero
loops and exact `ADCS`/`ANDS` (11 loops), a rewrite of Paper III's evaluation into tables,
then logarithmic potentials on the machine code; later options (bounds in the parameters,
a native zone kernel, hardware validation, Thumb-2); the author's open items 44-47.

76. "Proceed with the order you propose"

What the AI did for 76 (Claude Opus 5.5, 2026-11-20), step 1 of the order proposed (step 2
below; step 3, logarithmic potentials on the machine code, not started):
- Wrap to zero: Clang counts some byte offsets from 2^32 - 16 up by 4 to zero (`adds; bne`).
  The checker now rounds facts on sums with the congruences (`ThumbDataCore.gExpS`,
  `tightenS`; `condFactsM` applies it after `tightenL`), proved in `ThumbData`
  (`gExpS_dvd`, `tightenS_holds`, `condFactsM_sound` with the extra divisibility hypothesis);
  example `exZero_checks`/`exZero_needs_cong`/`exZero_sound` (3 iterations; rejected without
  the congruences). No new assumption; `lake build` clean. Producer (`binloops.py`, untrusted):
  mirror `tighten_s`/`g_exp_s`; `adds #0` no longer a wrap point; widening thresholds at the
  wrap-around values of additions; virtual premises (sum + bound of one term) in the Farkas
  shortest paths; `synth_transport` (longest-path constants of transported potentials before
  the LP); candidates sorted by bound and search continued above the source bound.
  Must-reject tests `WrapToZero` (start 14, step 3, congruences removed). Exact `ADCS`/`ANDS`
  were examined and not done: the `ADCS` loops of `bsort` stop on a data-dependent flag and the
  `ANDS` loops include `x &= x - 1` (no linear potential); the prediction made in answer 75 that
  they would add loops was wrong, recorded in the cycles README.
- Six runs (default and no-frame-pointer builds, three assumptions): +6 loops in every run
  (`bsort`, `fft`, `fir2dim`), none lost, no bound higher, no certificate rejected, no emulated
  run above a bound; kernels 142 / 199 / 256 (146 / 204 / 258), 372 of 519 loops with both
  assumptions; trusted loop rows 41 / 35 / 17; 121 functions with a certified cycle bound.
- Step 2: Paper III's evaluation of loop bounds on the code rewritten as three tables (results
  per assumption, `tab:loops`; counts after each extension in the order made, stated as not
  an ablation, `tab:steps`; causes of the 147 loops left, `tab:fail`) and a shorter text; the
  history moved to the cycles README. Producer paragraph extended (thresholds, virtual
  premises, longest-path constants); abstract figures; Lean size (4,100 lines, 145 theorems)
  in Papers I and III; guide parts 5 and 9, certificate-format.md, formalization.yaml,
  CLAUDE.md (596 theorems). This text of Paper III is new since the author's statement on
  the use of AI.

77. "This project is a plugin for a compiler so I would like to understand if the final product can be integrated inside a GCC, llvm, clang and work on existing code (libraries) in its current state and, if not, what should be done to get a real industrial value"

What the AI did for 77 (Claude Opus 5.5, 2026-11-20): an answer only, no change. In its
current state the plugin runs on unmodified C/C++ code compiled by Clang 18 (TACLeBench,
CMSIS-DSP, `compile_commands.json` projects; flow facts, SARIF, CI diffs, time budgets);
not in GCC (the analysis reads Clang's AST), other LLVM front ends only through the Rust
translation, other Clang versions not tested; machine-code certification only for the
Cortex-M0 and only tried on Clang binaries. Proposed order: validation of the timing table
on a board, GCC binaries for the Cortex-M0, then packaging and qualification evidence.

78. "Proceed as you say"

What the AI did for 78 (Claude Opus 5.5, 2026-11-20/21):
- `benchmarks/hardware/` (new): `hw.py` (build: each kernel object linked unchanged with
  `stm32f0/startup.c`, TIM2 timing of `main`, result on USART2; measure: flash and read the
  serial port; report: board cycles against the certified bound and the emulator with
  `MUL_CYCLES = 1`), `Dockerfile` (arm-none-eabi-gcc from Ubuntu's packages), README.
  Built for the NUCLEO-F091RC (26 of 29 kernels link); **not run on a board**: the register
  addresses and clock set-up are taken from ST's reference manual RM0091 by the AI and are
  untried; that the STM32F0 has the single-cycle multiplier is also from the AI's reading of
  ST's documentation (PM0215) and to be confirmed.
- `run_cycles.py --gcc IMAGE --tag=.gcc`: the kernels compiled by arm-none-eabi-gcc 13.2.1
  (Docker, no network, `GCC_FLAGS`). The GCC runs revealed three defects, fixed:
  (1) the source was analysed with the host's data model (64-bit `long`): a bound of
  `sha_byte_reverse` below an emulated run (213 vs 367 cycles); now `SOURCE_TARGET`
  (`--target=thumbv6m-none-eabi`); (2) a GCC-rotated loop of `fft_bit_reduct` matched with
  its inner loop (bound 11, 1023 iterations observed); (3) the producer did not terminate on
  GCC's `bitcount` (zone widening then closure kept raising a bound; 7 hours): after
  `HARD_VISITS` = 200 visits of a head, growing entries are forgotten (`forget_growing`).
  DWARF line-0 rows and discriminators are now read (`wcet.zero_ranges`, `LINE`).

79. "The task has been running for hours can you check it if it needs more time or if is better to reconsider ?"

What the AI did for 79 (Claude Opus 5.5, 2026-11-21): found the GCC `bitcount` run stuck
in the producer's fixpoint (defect (3) above) and the GCC runs never started (an option
split by the shell script); fixed both, then defects (1)-(2) appeared in the runs. A first
fix of (2), the largest bound among the loop's own lines, made `matrix1` 80 times looser
and left `bsort` unbounded; two options were offered to the author.

80. "Proceed with the first recommended option : Have the plugin report also give each loop's last source line."

What the AI did for 80 (Claude Opus 5.5, 2026-11-21):
- Plugin: `LoopReport::endLine`, `"end_line"` in the JSON report (`Report.hpp/.cpp`,
  `Analyzer.cpp`); ctest 183/183.
- `wcet.Analysis.match`: a binary loop is matched with the innermost source loop whose
  line range holds the lines of its own instructions that lie in some source loop; lines
  outside every loop are ignored; else the largest bound of the loops whose line occurs.
  Callers: `run_cycles.py`, `run_otawa.py`, `crosscheck_link.py`; `run_stm32.py` analyses the
  source for its target. Tests `test_match_by_line_ranges`, `test_loop_ends_shifted` (a bug of
  the first version: the run-time routines' end lines were not shifted, which left the
  division loops unmatched; found by the full runs, 107 -> 92 bounded functions, fixed).
- Runs (Clang default and without frame pointer, three assumptions; GCC, three
  assumptions): no violation, no certificate rejected, no loop lost against the runs
  before; Clang: 107 functions bounded, `bsort` `main` 369,779 -> 366,147, one more `minver`
  loop certified (143 / 200 / 257 of 403); GCC: 107 functions bounded, 73 calls and 65 loops
  compared, 112 certified functions, 74 / 65 / 40 of 215 kernel loops certified.
- `otawa_flow.flow_facts` uses the same rule (`wcet.Analysis.match`, with the ranges): with
  its earlier rule and the line-0 fix it had lost `bsort_BubbleSort` (104 of 107 functions in
  `run_otawa.py --matching otawa`); now 107, the same bounds as `wcet.py`'s matching. Reruns:
  certified cycle bounds without loop certificates (entry functions 1.06-1.92 times the
  runs), OTAWA in instructions and cycles (geometric means 2.32 and 2.69), the STM32 models
  (169 / 163 functions, all 107 of the Cortex-M0 bounded on the Cortex-M4), the
  classification `tab:fail` (146 loops). Test `test_innermost_line_range`.
- A loop of `minver` is now certified (0x104): its function has a `while (1)` loop without
  source bound that the earlier rule matched with a bounded loop (a wrong trusted bound,
  harmless there: the function calls soft-float code and is never compared with a run).
- Paper III: the matching sentence, `tab:loops`, `tab:steps`, `tab:fail`, abstract
  figures, OTAWA and STM32 figures, new paragraph "Another compiler"; cycles README
  (method, "GCC binaries", OTAWA, STM32), guide parts 5, 6 and 9, plugin README,
  CLAUDE.md. This text of Paper III is new since the author's statement on the use of AI.

81. "Once done make sure to update the guide too"

What the AI did for 81 (Claude Opus 5.5, 2026-11-21): guide part 5 (matching by line ranges
with the `fft` example, a note on the GCC binaries, the board harness, figures), part 6
(matching), part 9 (figures; GCC and the harness in the answers on the processor model and
on the compiler).

82. "Would it be a good idea to upload paper I and II on arxiv as they are now ?"

What the AI did for 82 (Claude Opus 5.5, 2026-11-21): an answer, no change: not yet; the
papers build and have no `\authortodo`, but item 2.A of section 2 was still open, the
code was not archived (and `main` was behind the working branch), time and cost were
blank; it listed what it could do itself.

83. "I am pretty busy rereading the guide and papers right now, could you work on all the open points yourself ? I think that many, if not all, can be done by you without my intervention"

What the AI did for 83 (Claude Opus 5.5, 2026-11-21); summary in `docs/release-checklist.md`:
- Statement fidelity (item 1 of section 3, as a pre-check, not in place of the author):
  each Paper I statement of `formalization.yaml` read next to its Lean statement. Gaps
  closed by a new module `Norms` (157 lines, 9 theorems, no new axiom): `CostNorm`
  (subadditive cost norms; instruction count and weighted cost as instances) with
  `flatten_le`, `runTrace_le`, `condTrace_le`, `blocks_le` (k sequential conditional
  blocks), `wcet_bound`; `order_nil`, `order_wf`, `minimal_iteration_least`,
  `runTrace_prefix`. Table 1 (now on two pages, same number), `formalization.yaml`,
  Lean size in Paper I (10,400 lines, 460 theorems), CLAUDE.md and the guide updated.
- Reproduction of Paper II's figures on this machine (section E of the checklist).
- Bibliography: the 69 entries cited by Papers I and II checked against Crossref and
  DataCite (no data error); `clangeffects` and `infercost` read .
- Wording scan of Papers I and II (no marketing words found).
- AI statements of the three papers: Haiku 5.5 added (found in the transcripts, inside the
  subagent that reads web pages). Time and tokens measured from the transcripts (section 2).
- `paper/make_arxiv.py`: self-contained arXiv bundles (`.bbl`, cross-paper references
  resolved to numbers), each compiled alone without warnings, text identical to the
  normal builds. `CITATION.cff`, `.zenodo.json`, top-level `README.md` rewritten.
- Found and fixed: the two certificate-checking steps of `plugin_build.yml` piped the
  checker into `tee`, losing its exit status, so a rejected certificate would not have failed
  CI (now tested on the output; checked locally with a mutated certificate); DEBIE's
  `Switch_SU_State` exported and not validated, which Paper II did not say (now stated);
  CMSIS-DSP gives 1,069 loops with ranges when no file times out (Paper II said 1,044).
- Not done, the author's: making the repository public (it is private), merging into
  `main` and tagging, archiving (Zenodo or Software Heritage), the arXiv account and
  upload, the cost, and the reading of section 3.

84. "I put the original OOP java version in a "old" directory, please read it and tell me if we should commit or not"

What the AI did for 84 (Claude Opus 5.5, 2026-11-21): read the 143 files (the module Revenge
of METACad, 2008-2017): authorship (only the author), no license, no third-party source or
personal data; compared its tests with the examples of Paper I (infinite loop and linear
recursion among them; no test of the parametric loop, disabled, nor of the binary
recursion). Recommended committing it, with a README, without the IDE files, under MIT,
and rewording Paper I's sentence on the prototype.

85. "I agree with all these points, I confirm I am the only author. This code is ten years old, you can still find it online : https://sourceforge.net/p/metacad/code/291/tree/revenge/"

What the AI did for 85 (Claude Opus 5.5, 2026-11-21): checked that the SourceForge tree
(revision 291, July 2017) holds `revenge/`; moved the code to `history/revenge/` (Eclipse
files and METACad's parent POM removed), wrote its README (provenance, method, relation to
Paper I's examples, status), and reworded Paper I's sentence in Section "Examples": "The
method is that of an earlier prototype implementation ... whose tests include the infinite
loop and the linear recursion below" (before: "The systems are those produced by a
prototype implementation").

86. "Now I would like you to check this whole project once again : we are almost ready to publish the article on arxiv and open the code, I would like to clean up so that this project is spotless. What would you suggest ?"

87. "I think that you should merge with main and push it"

88. "Treat all your suggestions autonomously"

What the AI did for 86-88 (Claude Opus 5.5, 2026-11-21):
- Audit: git history (no binaries, no blob above 500 KB, one author, no vendored benchmark),
  personal data (no home paths outside CLAUDE.md, no email address in tracked files; the
  commits carry the author's address), links and paths in the documentation (none broken),
  Lean (0 warnings), Python (ruff: 10 findings), C++ (`-Wall -Wextra`: 6 warnings), CI (no
  run since 2026-11-12: both workflows trigger on `main` only).
- 87: `main` fast-forwarded to `evaluation-and-contexts` and pushed; both CI workflows ran
  on GitHub for the first time on this work and passed (Lean; plugin build, tests and
  certificate check).
- 88: copyright headers on 16 files; the lint findings and C++ warnings fixed (no change
  of behaviour: ctest 183/183, cycles tests, Rust test, `classify_loops.py`); `.vscode/`
  removed; `paper/.gitignore` reduced to the outputs of the papers; the plugin workflow
  also triggered by every `*Core.lean` module of the checker and by `frontends/`;
  `docs/proposals.md` and `docs/implementation-plan.md` marked historical (not moved:
  this file cites them); CLAUDE.md (no home path, page counts, current focus); the cycles,
  TACLeBench and TPDB READMEs rewritten to their current figures with the history moved
  to a final section (a stale TPDB classification corrected); local build leftovers
  deleted. Not done: the commit email (the author's choice).

89. "I would like to add a short presentation (if not already present, I do not remember) using sli.dev tools to convert markdow into slides about this project, showing a real case workflow with examples of artifacts : initial code, untrusted facts, certificate, lean demonstration, assembly verifications and so on, identifying the compiler and linker parts, time and complexity assertions (these are just hints, you are free to integrate or change anything). Maybe even a bit of theory similar to the initial part in the guide but for slides. Include also benchmarks and tool comparisons"

What the AI did for 89 (Claude Opus 5.5, 2026-11-21): no presentation existed. `docs/slides/`:
a Slidev deck of 22 slides (Slidev 53.1.0 pinned), and a running example `demo/fir.c` (an
8-tap FIR filter, a parameter range, a 500 µs budget) whose artifacts are all produced by
`demo/run_demo.py` and quoted in the slides: the plugin's remarks and report (untrusted),
the source certificate with a bound symbolic in the parameter, accepted and validated by
the checker, the Lean statements (`check_sound`, `binary_sound`), the Cortex-M0
disassembly, the matching of loops by line ranges, the cycle certificate, a loop bound
proved on the instructions (`dot`: potential (28 − r2)/4, 7 back edges) and one left
trusted (`fir_peak`, bounded by its parameter), an emulated run (20,806 cycles ≤ 21,177),
the time budget after linking (491 µs ≤ 500 µs; 400 µs fails), a tampered certificate
rejected, and the time of each step. Theory slides adapted from guide part 1; benchmark and
tool-comparison slides with the figures reproduced on 2026-11-21. Every slide was rendered
to an image and checked for overflow. The budget was first 400 µs, which the example misses
(the time-budget step certifies without the loop certificates): set to 500 µs, the failing
case is stated on the slide.

90. "Push this into main too"

What the AI did for 90 (Claude Opus 5.5, 2026-11-21): fast-forwarded `main` to the slides
commit and pushed it; the CI runs passed.

91. "I have tagged the release, please give me instructions about the DOI and arXiv"

What the AI did for 91 (Claude Opus 5.5, 2026-11-21): instructions only (Zenodo's GitHub
integration archives a published GitHub release of a public repository; version and concept
DOIs; Software Heritage; arXiv endorsement, categories, upload order of Papers I and II).

92. "Here is the DOI : 10.5281/zenodo.24425070 markdown : [![DOI](https://zenodo.org/badge/1423112486.svg)](https://doi.org/10.5281/zenodo.24425069) This is the only DOI I found on zenodo. The SWHID swh:1:rel:70c77563037e6db2a55b48b3ad4963c86a67773f;origin=https://github.com/ldallolio/crosscheck;visit=swh:1:snp:84c735986d2163ea55f8ab246c5b7a18cc5ccc5a and permalink : https://archive.softwareheritage.org/swh:1:rel:70c77563037e6db2a55b48b3ad4963c86a67773f;origin=https://github.com/ldallolio/crosscheck;visit=swh:1:snp:84c735986d2163ea55f8ab246c5b7a18cc5ccc5a"

What the AI did for 92 (Claude Opus 5.5, 2026-11-21): read both records from Zenodo's public
API: `10.5281/zenodo.24425070` is the version DOI of v1.0 and `10.5281/zenodo.24425069` (the badge's) the concept DOI; the SWHID's
release object is the tag `v1.0`. Paper I's paragraph "Artifact" and a new section
"Artifact" in Papers II and III give the repository, the version DOI and the SWHID;
`CITATION.cff` (version, date, both DOIs, SWHID), README badge and citation line, release
checklist. Fixed a hyperref warning (duplicate anchor of the two parts of Table 1). Papers
rebuilt without warnings (42, 23, 20 pages), arXiv bundles regenerated.

93. "You are on main branch, I pushed the commit, should we remove the evaluation-and-contexts branch if it is merged on main ? Also, I am registering on arXiv Group(s) you would like to submit to:

 cs econ eess math physics q-bio q-fin stat"

94. "which license should I choose ? [followed by arXiv's list of licences: CC BY, CC BY-SA, CC BY-NC-SA, CC BY-NC-ND, arXiv.org perpetual non-exclusive license, CC Zero]"

95. "how to build the slides pdf ?"

96. "Can you explain the usage of dot ?"

97. "I have an hard time finding the arxiv endorsement, are there other ways to ask for one ?"

98. "Can (should) I upload the papers into HAL and Zenodo first then in arxiv when I will get the endorsement ?"

99. "I would like to understand better some points from section C so that I can decide : tell me more about Novelty and attributions (items 7, 9, 18, 36, 37): the papers must not present classical ideas as new. [the reading notes] says, per entry, what the AI read; 18 of the 69 cited works have no reading note (books, classical papers such as Floyd 1967, Wegbreit 1975, Podelski and Rybalchenko 2004) and 30 were read in the abstract only."

100. "I agree with "We use the prefix order ..." and citation, also for citing Tarjan. I added courcelle1983trees.pdf tarjan1985complexity.pdf floyd1967assigning.pdf wegbreit1975mechanical.pdf podelski2004complete.pdf bardin2008fast.pdf kincaid2019closed.pdf schrijver1986theory.pdf cormen2009introduction.pdf baccelli1992synchronization.pdf cousot1977abstract.pdf nielson1987hoare.pdf start reading these then tell me again what is still missing"

101. "I also added blumofe1999scheduling.pdf healy2000supporting.pdf albert2011more.pdf atkey2010amortised.pdf"

What the AI did for 93-98 (Claude Opus 5.5, 2026-11-21/22): advice only (the branch is
merged; arXiv group `cs`, cs.LO and cs.PL; licence CC BY 4.0 or arXiv's non-exclusive
licence; endorsement; Zenodo preprints with reserved DOIs before arXiv, HAL optional),
the slides exported to PDF (22 pages, checked), and an explanation of `dot` in the slides'
example.

What the AI did for 99-101 (Claude Opus 5.5, 2026-11-22): explained items 7, 9, 18, 36 and
37 from the papers' text. Then read the cited passages of the 16 works the author
provided (two scanned copies through OCR) and recorded each in the reading notes.
Changes approved by the author: the contribution list of Paper I says the prefix order is
used, not defined, and cites Courcelle 1983 (Section 2.4) for the tree order, also after
`def:tree-order`; a sentence after `def:order-by-composition` calls it the usual prefix
order; `prop:size-potential` cites Tarjan 1985 for the potential method. Both entries
checked on Crossref. Found and reported, not changed: Nielson 1987's while rule [R-4]
and its bubble-sort recurrence are an earlier form of `prop:amortised-loop` (1); Atkey
2010 (Coq-verified VC generator, LP-inferred annotations) is not cited; Kincaid 2019 is
not a cost analysis; the affine Farkas lemma needs a satisfiable premise for the
equivalence Paper I states; Floyd 1967 already proposes the W-function as a bound on the
number of steps, and lexicographic tuples.

102. "Proceed with the changes"

What the AI did for 102 (Claude Opus 5.5, 2026-11-22): in Paper I, Nielson 1987 (rule [R-4],
the bubble-sort recurrence of its Section 5) cited before `prop:amortised-loop`, whose claim
is now "a derived rule of the cost logic, with a case of the checker and a Lean proof";
Atkey 2010 cited in the related work on mechanized logics (entry checked on Crossref, LMCS
7(2:17), 2011); Kincaid 2019 moved from the cost analyses to the paragraph on loop
acceleration; the affine Farkas lemma stated with its satisfiability premise (Schrijver,
Corollary 7.1h), the soundness direction needing none; Floyd cited for lexicographic tuples
before `prop:lex-log`. Guide part 9 and the release checklist updated. Paper I: 43 pages;
the three papers build without warnings.

103. "Adapt the guide and slides if needed, then commit and push on main"

What the AI did for 103 (Claude Opus 5.5, 2026-11-22): guide parts 1, 2, 3, 8 and 9 adapted
(Courcelle's tree order, Tarjan for the size potential, Nielson 1987 and Atkey 2010 as prior
work for the amortised rule and the logic, reading status of the bibliography, a node for
loop acceleration and closed forms); the slides needed no change (no novelty claim; the
trace order is called the prefix order there). Committed and pushed to `main`.

104. "I am perplex about the A part on missing lean proofs, do you have any opinion about this ?"

105. "Yes, please do so"

What the AI did for 104-105 (Claude Opus 5.5, 2026-11-22): sorted Paper I's list of
non-mechanized points into modelling hypotheses, cited classical results and the author's
own mathematics, and proposed to close the last group. Then: new Lean module `Branching`
(trees with `b` children, `KTree b`: the tree order, grafting, full trees, powers with the
closed form, in natural numbers and over the rationals, and the execution tree of a `b`-ary
recursion as the least feasible tree, with big-step agreement; example: a ternary
recursion); new module `Divergence` (infinite executions as the greatest fixed point of the
coinductive big-step rules; with positive loop-test and call weights an infinite execution
has prefixes of every cost, so a valid or derivable bound excludes it; example `while true
skip`). Paper I: the remark became `prop:no-divergence` with its proof; the paragraph on
parallel composition became a remark marked as not formalized; the scope list no longer
lists the tree statements, the Lyapunov theorem (stated as Lean states it) or the
interrupt theorem (stated, as in Lean, for schedules without pending activations; the
busy-period extension is only discussed); the equation-generating rules described as a
method. Table 1 (two rows), `formalization.yaml`, the module counts (32 modules, 644
theorems; Paper I about 11,000 lines and 499 theorems), CLAUDE.md, README, guide parts 3,
7 and 9, slides updated. `lake build`: 0 errors, 0 warnings; `#print axioms` of the new
theorems: at most `propext`, `Classical.choice`, `Quot.sound`. The three papers build
without warnings (Paper I: 43 pages).

106. "Yes commit and push"

What the AI did for 106 (Claude Opus 5.5, 2026-11-22): committed the work of 104-105 and pushed it to `main`.

107. "I do not think that leaving open points such as in docs/release-checklist.md or AI_USAGE.md on submission : please close them all, or remove the remarks, do the same for other files. If we can handle that, let's do it, otherwise let's clean up"

108. "Remove any record of the "references" folder and its content : this is for local use only. You can keep the gitignore line but nothing else about it"

What the AI did for 107-108 (Claude Opus 5.5, 2026-11-22): asked the author the two facts
only the author knows (AI use before 2026-11-11: not recorded; monetary cost: not recorded,
usage in time and tokens). Closed what could be closed: `matiyasevich1970enumerable`
corrected to the English translation whose title it gives (checked on Math-Net.ru and the
JSL review); obsolete items (old title, `attali1998formal`, removed `\authortodo` marks)
dropped; the unused `\authortodo` macro removed from the three papers; two "not yet"
sentences of Paper I reworded. Removed what only the author's review could close: Section 3
of this file is now a review record of the AI's checks, Section 2 says how each AGMAI item
is met, and a note above Section 1 says that the log's references to open items describe
the state at the time. `docs/release-checklist.md` replaced by `docs/release-record.md`
(checks, archive identifiers, reproduction); the historical `docs/proposals.md` and
`docs/implementation-plan.md` deleted (in git history); "not yet" phrasings in the guide,
READMEs, slides and the hardware start-up file reworded; CLAUDE.md updated (no to-do lists,
no `\authortodo`). The folder of cited works and reading notes is no longer tracked
(`.gitignore` covers it) and no file of the repository mentions it any more; the papers'
statements on the use of AI no longer point to it. Papers rebuilt without warnings.

109. "commit and push to main"

What the AI did for 109 (Claude Opus 5.5, 2026-11-22): committed the work of 107-108 and pushed it to `main`.

### Earlier work

AI use before 2026-11-11 (on the manuscript, the Lean files and `CLAUDE.md` that existed
then) is not recorded in this file.

The Java prototype that preceded CrossCheck (module Revenge of METACad, 2008-2017,
<https://sourceforge.net/p/metacad/code/291/tree/revenge/>) is in `history/revenge/`; the
author confirmed on 2026-11-21 being its only author. It predates any AI assistance.

## 2. Compliance with the AGMAI recommendations

The recommendations address AI labs; for a paper released by a human author their
Section 2.A applies (traditional norms: the author understands the argument, has
verified it personally, and takes full responsibility). The Step I items are applied
here as the release standard.

| Item | Requirement | How it is met |
|---|---|---|
| 2.A | Author understands every argument, has verified correctness personally, takes full responsibility | The author's statement in each paper ("I have read and verified the text and take full responsibility for the content"). This file records the AI's part, not the author's review. |
| 1(a) | Literature searched; ideas cited to the papers that introduced them | Related work and "Positioning" of Paper I; the attributions were checked against the cited works that could be read, and changed where the reading required it (Section 1, prompts 99-103). |
| 1(b) | Traditional paper style: introduction, precise statements and proofs | Done. |
| 2 | Deposit in a scholarly repository with persistent identifier and version history | Code: release `v1.0`, Zenodo `doi:10.5281/zenodo.24425070` (all versions `doi:10.5281/zenodo.24425069`), Software Heritage `swh:1:rel:70c77563037e6db2a55b48b3ad4963c86a67773f`; cited in the three papers, `CITATION.cff` and `README.md`. Papers: arXiv. |
| 3 | Publish model name, prompts, summarised reasoning, time, cost | Models, prompts and summaries: this file. Measured by the AI on 2026-11-21 from the local Claude Code transcripts of this project (11 files: the main session and its subagents), 2026-11-11 to 2026-11-21: about 76 hours of active session time (gaps above 30 minutes not counted); 5,117 model responses (`claude-opus-5-5` 4,273, `claude-fable-5-2` 801, `claude-haiku-5-5` 27, the last inside the web-page reader); 5.8 million output tokens, 20.4 million tokens written to and 1,790 million read from the prompt cache. Work done in other tools (e.g. claude.ai chats) is not in these transcripts. The monetary cost is not recorded; usage is given in time and tokens. |
| 4 | Formalize as far as possible; state formalization status clearly; machine-readable link between paper and formal artifact; copyright headers | Paper I, Section "Mechanization in Lean 4", lists what is not mechanized (modelling hypotheses, cited classical results, two remarks marked as not formalized; the C++ plugin is outside the formalization). `formalization/formalization.yaml` links paper labels to Lean names (project-defined schema). Copyright headers on every file. No challenge file for `comparator` is provided. |
| 5 | Document exactly how AI came to be used on this problem | This file, and the "Statement on the Use of AI" in each paper. |

## 3. Review record

What the AI checked, and where the result is recorded. Machine-checked statements are
safe as Lean statements; the checks below concern the correspondence between the papers
and Lean, the figures, the bibliography and the trusted parts.

- **Paper statements against Lean.** Every row of Table 1 of Paper I read next to its Lean
  statement, hypotheses included (2026-11-16, prompt 45, for
  the definitions of the cost logic, the checker, mini-C, interrupts and fork-join;
  2026-11-21, prompt 83, for all rows). The gaps found were closed by Lean proofs: module
  `Norms` (2026-11-21), modules `Branching` and `Divergence` (2026-11-22); `formalization.yaml`
  checked against the labels of the papers and the names of the Lean sources (2026-11-22).
- **Lean.** `lake build` without errors or warnings; no `sorry`, `admit` or new `axiom`;
  `#print axioms` of the theorems added since 2026-11-21: at most `propext`,
  `Classical.choice`, `Quot.sound`; the Lean CI passes on GitHub.
- **Figures.** Every figure of Paper II reproduced on 2026-11-21 (`docs/release-record.md`);
  the figures of Paper III follow `benchmarks/cycles/README.md` and the runs it describes;
  `ctest` 183 of 183.
- **Bibliography.** Every entry checked against Crossref, DataCite or Open Library
  (2026-11-13, 2026-11-21, 2026-11-22); the cited passages of the works that could be
  obtained were read and compared with the sentences that cite them (Section 1).
- **Cortex-M0 timings.** `m0.py` and `ThumbCore.decode` against Table 3-1 of the Cortex-M0
  Technical Reference Manual (2026-11-16); the effects against `m0.py` on every encoding
  (`test_effect.py`, `test_thumb.py`, CI).
- **Trusted parts, stated in the papers.** The analyser and the certificate generator
  (unverified C++); the exporter to mini-C for validated certificates, with its hypotheses
  (no signed overflow, no aliasing of tracked variables, no concurrent writes of tracked
  globals); the Lean specification of the Cortex-M0, compared with an interpreter written
  for the purpose and not with hardware (the board harness of `benchmarks/hardware` has
  not been run); the matching of binary loops with source loops by debug lines, checked on
  emulated runs; OTAWA's processor models, used and not checked; the hypothesis that one
  unit of cost takes one unit of time.
