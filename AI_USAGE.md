# AI usage record

This file documents how AI was used in CrossCheck: the three papers, the Lean development and
the tools. It follows AGMAI's *Responsible Release of AI-Generated Mathematics*
(<https://agmai.org/general-sep29/>, version of 29 September 2026); Section 3 says how each of
its recommendations is met.

It records what is needed to understand, assess and reproduce the work: which tools and
models were used, what the assistant produced in each part of the project, and how each part
is checked. Like a laboratory notebook that is summarised for publication, it does not
reproduce the working conversations (discussions, drafts, abandoned attempts), which carry no
information beyond the results recorded here and in the git history.

## 1. Tools, models and usage

| Item | Value |
|---|---|
| Tool | Claude Code (Anthropic), command-line coding assistant |
| Models | Claude Opus 5.5 (`claude-opus-5-5`); Claude Fable 5.2 (`claude-fable-5-2`), part of the work of 2026-11-11 to 2026-11-16; Claude Haiku 5.5 (`claude-haiku-5-5`) inside the component that reads web pages |
| Period | 2026-11-11 to 2026-11-27 |
| Usage | Measured from the local Claude Code transcripts of the project (15 files: the main session and its subagents), 2026-11-11 to 2026-11-27: about 134 hours of active session time (gaps above 30 minutes not counted); 8,408 model responses (`claude-opus-5-5` 7,571, `claude-fable-5-2` 801, `claude-haiku-5-5` 36); 8.4 million output tokens, 27.0 million tokens written to and 2,836 million read from the prompt cache. Work done in other tools is not included. The monetary cost is not recorded (author's decision). |

How the work was organised: the author set the goals, the priorities and the constraints
(soundness rules, the AGMAI recommendations, no claim that the author verified anything, no
trusted step added without a Lean proof), decided between the options the assistant proposed,
and supplied copies of cited works. The assistant wrote code, proofs and text, ran the
measurements and the checks listed in Section 4, and reported what it could not establish.

## 2. What the assistant produced

### Paper I (theory) and its Lean development

- **Manuscript.** The framework, the examples and the original manuscript are the author's.
  The assistant reviewed the manuscript critically (2026-11-11), corrected statements whose
  proofs or Lean counterparts did not match (among them a Lean theorem with unsatisfiable
  hypotheses, an "iff" proved in one direction, `treePow` off by one, a tree order different
  from the paper's), restructured and rewrote substantial parts of the text (positioning,
  related work, mechanization, limitations), and proposed a simplification that the author
  approved (2026-11-12: the `Sigma^infinity` completion became a remark; the asymptotic
  preorder, the subsequence order and several side remarks were removed).
- **Lean (written by the assistant, checked by the Lean kernel).** `WhileLoop`, `Ranking`,
  `Recursion`, `Certificate`, `Arity`, `Language` (cost logic with procedures and recursion,
  soundness), `Checker` and `CheckerCore` (the certificate checker, symbolic and quadratic
  bounds, calls, contracts, amortised and logarithmic loops, size facts of loops, assumptions), `MiniC`, `MiniCCore`,
  `MiniCJump`, `MiniCJumpCore` (validation against the source), `ResponseCore`,
  `Interrupts`, `ForkJoin`, `Stack`, `Norms`, `Branching`, `Divergence`, and extensions of
  the author's modules `Trace`, `Tree`, `Dominance`, `FixedPoint`, `OperationalSemantics`,
  `Examples`. The correspondence with the paper is Table 1 of Paper I and
  `formalization/formalization.yaml`. On 2026-11-27 the assistant ported the whole development
  from Lean and mathlib `v4.16.0` (the toolchain of the archived `v1.0`) to `v4.36.0`: renamed
  library lemmas, removed `simp` arguments and tactics that the new linters report as unused,
  and repaired the proofs that broke; no statement changed.
- **Split into papers.** The single paper was split into Papers I and II on 2026-11-14 and
  the work on binaries became Paper III on 2026-11-18 (the earlier versions are in git).

### Paper II (the Clang plugin and its evaluation)

The assistant wrote the Clang plugin and its tests, the certificate generator, the exporter
to mini-C, the checker program (`CheckerMain.lean`), the export of flow facts (FFX, AIS),
SARIF and the cost diff, the Rust front-end, the generator of random test programs, the
interpreter of certificates and the mutation test, the ACSL export, the qualification-kit
skeleton (`docs/qualification/`, written from general knowledge of DO-330 and ISO 26262; it
claims no compliance), and the benchmark scripts (TACLeBench, TPDB, CMSIS-DSP). It ran the
measurements and the comparisons with LLVM ScalarEvolution, KoAT2, CoFloCo, Infer and oRange
(the other tools run in containers without network, their answers stored in
`benchmarks/*/results/`), and drafted the text.

### Paper III (machine code)

The assistant wrote the Lean modules of Table `tab:lean3` (`CyclesCore`, `Cycles`,
`ThumbCore`, `Thumb`, `ThumbDataCore`, `ThumbData`, `ThumbConv`, `ThumbSearch`, `ThumbHigh`) and
the ELF reader of the checker (`ElfCore`, which compares a certificate's code with the binary):
the decoder and timing table of the Cortex-M0, cycle certificates checked on the machine
code, loop certificates on the machine code (invariants, potentials, congruences, disjunctive
invariants, jumps through tables, preconditions, logarithmic potentials, amortised rows, the
calling convention checked on the code, the high registers); and the tools in
`benchmarks/cycles/` (the ARMv6-M interpreter `m0.py` and its C core, the cycle, loop and stack
analyses, the producers of certificates, the comparison with QEMU, the OTAWA experiments, the
GCC builds, the time budgets of `crosscheck_link.py`) and the board harness of
`benchmarks/hardware/` with its timing micro-benchmarks (not run on a board). It ran the measurements and drafted the text.

### Bibliography and literature

The assistant compiled the related-work bibliography and searched for prior work at several
stages, the last on 2026-11-27. Bibliographic data of every
entry were checked against Crossref, DataCite or Open Library (2026-11-13, 2026-11-21,
2026-11-22). The sentences that cite a work were compared with the cited passages of the copies
that could be obtained (open access, or supplied by the author), and changed where the reading
required it; what was read is recorded in the author's reading notes, which are not part of
the repository.

### Documentation

The companion guide (`docs/guide/`, rewritten for a non-specialist on 2026-11-18), the
slides (`docs/slides/`), the certificate format (`docs/certificate-format.md`), the
contracts (`docs/contracts.md`), the release record (`docs/release-record.md`), the READMEs
and `CLAUDE.md`.

### Earlier work

AI use before 2026-11-11 (on the manuscript, the Lean files and `CLAUDE.md` that existed then)
is not recorded in this file. The Java prototype that preceded CrossCheck (module Revenge of
METACad, 2008-2017, <https://sourceforge.net/p/metacad/code/291/tree/revenge/>, in
`history/revenge/`) is the author's alone and predates any AI assistance.

## 3. Compliance with the AGMAI recommendations

The recommendations address AI labs; for a paper released by a human author their Section 2.A
applies (traditional norms: the author understands the argument, has verified it personally,
and takes full responsibility). The Step I items are applied here as the release standard.

| Item | Requirement | How it is met |
|---|---|---|
| 2.A | Author understands every argument, has verified correctness personally, takes full responsibility | The author's statement in each paper. This file records the assistant's part, not the author's review. |
| 1(a) | Literature searched; ideas cited to the papers that introduced them | Related work and "Positioning" of Paper I, related work of Papers II and III; attributions checked against the cited works that could be read (Section 2). |
| 1(b) | Traditional paper style: introduction, precise statements and proofs | Done. |
| 2 | Deposit in a scholarly repository with persistent identifier and version history | Code: release `v1.0`, Zenodo `doi:10.5281/zenodo.24425070` (all versions `doi:10.5281/zenodo.24425069`), Software Heritage `swh:1:rel:70c77563037e6db2a55b48b3ad4963c86a67773f`; cited in the papers, `CITATION.cff` and `README.md`. Papers: arXiv. |
| 3 | Publish model name, prompts, summarised reasoning, time, cost | Models, time and usage: Section 1. The tasks given to the assistant and what it produced: Section 2, with the git history. The working conversations are not published (item 3 addresses AI labs releasing results; here a human author is responsible, Section 2.A). The monetary cost is not recorded; usage is given in time and tokens. |
| 4 | Formalize as far as possible; state formalization status clearly; machine-readable link between paper and formal artifact; copyright headers | Paper I, Section "Mechanization in Lean 4", and Paper III, Table `tab:lean3`, list what is mechanized and what is not (modelling hypotheses, cited classical results, the C++ plugin). `formalization/formalization.yaml` links paper labels to Lean names (project-defined schema). Copyright headers on every file. No challenge file for `comparator` is provided. |
| 5 | Document exactly how AI came to be used on this problem | This file, and the "Statement on the Use of AI" in each paper. |

## 4. Review record

What the assistant checked, and where the result is recorded. Machine-checked statements are
safe as Lean statements; the checks below concern the correspondence between the papers and
Lean, the figures, the bibliography and the trusted parts.

- **Paper statements against Lean.** Every row of Table 1 of Paper I read next to its Lean
  statement, hypotheses included (2026-11-16 for the cost logic, the checker, mini-C,
  interrupts and fork-join; 2026-11-21 for all rows). The gaps found were closed by Lean proofs
  (`Norms`, 2026-11-21; `Branching` and `Divergence`, 2026-11-22); `formalization.yaml` checked
  against the labels of the papers and the names of the Lean sources (2026-11-22).
- **Lean.** `lake build` without errors or warnings; no `sorry`, `admit` or new `axiom`;
  `#print axioms`: at most `propext`, `Classical.choice`, `Quot.sound`; the Lean CI passes on
  GitHub. After the port to `v4.36.0` (2026-11-27): the axioms of all 4,277 declarations of the
  project collected by a program, none beyond the three; the checker program built with each
  toolchain gives identical output on 68 certificate files (the kernels, GCC and Clang, and the
  test certificates, accepted and rejected); the checker's test suites pass.
- **Figures.** Every figure of Paper II reproduced on 2026-11-21 (`docs/release-record.md`);
  the figures of Paper III follow `benchmarks/cycles/README.md` and the runs it describes;
  `ctest` 183 of 183.
- **Bibliography.** Every entry checked against Crossref, DataCite or Open Library; the cited
  passages of the works that could be obtained read and compared with the sentences that cite
  them.
- **Cortex-M0 timings.** `m0.py` and `ThumbCore.decode` against Table 3-1 of the Cortex-M0
  Technical Reference Manual (2026-11-16) and against the cycle counts of Fox's L3 model of the
  Cortex-M0 in HOL4 (`examples/l3-machine-code/m0`, 2017; 2026-11-27): the same on every
  instruction both model (L3's multiplier is the single-cycle one, our `MUL_CYCLES` option);
  the instructions L3 times and we do not model (`MRS`, `MSR`, barriers, `WFE`/`WFI`, `CPS`)
  end a bound. The effects against `m0.py` on every encoding (`test_effect.py`,
  `test_thumb.py`, CI).
- **Trusted parts, stated in the papers.** The analyser and the certificate generator
  (unverified C++); the exporter to mini-C for validated certificates, with its hypotheses
  (no signed overflow, no aliasing of tracked variables, no concurrent writes of tracked
  globals); the Lean specification of the Cortex-M0, compared with an interpreter written for
  the purpose (whose semantics agree with QEMU's on the instructions that 50 programs execute)
  and with the L3 timings, not with hardware; that the binary is loaded as the checker reads
  its ELF file (`crosscheck-check --elf` compares the certificate's code and function entries
  with the file; for a relocatable object, that the final link preserves the bound) (the board harness of
  `benchmarks/hardware` has not been run); the matching of binary loops with source loops by
  debug lines, checked on emulated runs; OTAWA's processor models, used and not checked; the
  hypothesis that one unit of cost takes one unit of time.
