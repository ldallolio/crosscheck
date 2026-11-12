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
