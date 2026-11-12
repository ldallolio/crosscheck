# CrossCheck — Companion Guide

This guide explains everything that the paper (`paper/crosscheck.tex`), the Lean
development (`formalization/`) and the Clang plugin (`clang-plugin/`) use or introduce.
It assumes the reader is a software engineer who:

- knows C++ well and knows what real-time means (deadlines, WCET, interrupt handlers);
- understands the *idea* of CrossCheck (loops and recursion as minimisation problems);
- has little background in programming-language theory, logic or proof assistants
  (beyond having read Manna's *Mathematical Theory of Computation* out of curiosity).

The goal is that after reading it you can explain every sentence of the paper,
read every line of the Lean code, change the plugin, and answer questions from
experts in semantics, static analysis, WCET analysis and formal proof.

> **Status of this document.** It was written by an AI assistant (Claude, model
> Fable 5.2, November 2026) from the repository sources. The explanations of the
> repository's own code and of the paper are checked against those sources. The
> summaries of the *cited papers* (Part 3) come from the model's general knowledge,
> not from reading the papers in this session: treat them as a map, and read the
> originals before relying on a detail in front of an expert. See `AI_USAGE.md`.

## Reading order

| Part | File | What you get | Time |
|---|---|---|---|
| 1 | [01-background.md](01-background.md) | The background concepts the paper *refers to*, from zero: semantics, orders, fixed points, monoids, decidability, WCET, ranking functions, LP/Farkas, SMT, proof assistants. | 3–4 h |
| 2 | [02-paper.md](02-paper.md) | A section-by-section reading of the paper: every definition, proposition and theorem in plain words, why it is true, where it is in Lean, and the worked examples recomputed by hand. | 3 h |
| 3 | [03-bibliography.md](03-bibliography.md) | One summary per reference: what the work is, why it is cited, how CrossCheck relates to it. Grouped by theme, with a timeline. | 1–2 h |
| 4 | [04-plugin.md](04-plugin.md) | The Clang plugin: architecture, UML class/sequence/activity diagrams, the algorithms (symbolic state, invariants, Farkas encoding, cost algebra) traced on real examples. | 2–3 h |
| 5 | [05-lean-tutorial.md](05-lean-tutorial.md) | Lean 4 from scratch, using only examples from this repository: syntax, types vs propositions, every tactic used here, how to run and explore. | 3–4 h |
| 6 | [06-lean-modules.md](06-lean-modules.md) | Module-by-module documentation of the 12 Lean files: every definition and theorem, with line-by-line commentary of the key proofs. | 3–4 h |
| 7 | [07-expert-questions.md](07-expert-questions.md) | Questions experts are likely to ask, with answers; the honest weak points; how to phrase claims; a glossary. | 1 h |

If you are short on time: read Part 2, then Part 7, then come back to Parts 1 and 5
when a term is unclear.

## Conventions

- Math is written in plain Unicode (`≤`, `⊑`, `Σ*`, `⌈x⌉`) so the files read well
  in any editor.
- Paper statements are referred to by their LaTeX label (e.g. `thm:lyapunov-bound`),
  as in `CLAUDE.md`, because numbers change when the paper changes.
- Lean names are written in code font (`ranking_bound`); they can be searched with
  `grep -rn ranking_bound formalization/`.
- "Expert phrasing" boxes give the vocabulary a specialist would use for an idea.

## PDF version

`crosscheck-guide-ebook.pdf` (in this folder, not committed) is the whole guide as one PDF
with a 100 × 133 mm page for e-readers: clickable contents and bookmarks, and large
diagrams on their own page (rotated to landscape when that makes them bigger). To rebuild
it after editing the guide (needs Node.js and Google Chrome or Chromium):

```bash
cd docs/guide/tools
npm install                        # once
node build-pdf.mjs                 # e-reader page; add --format=a4 for printing
```

## Keeping this guide in sync

This guide quotes Lean names, plugin classes and paper labels. When one of them is
renamed or removed, update the guide in the same change (the same rule as for
Table 1 of the paper and `formalization/formalization.yaml`).
