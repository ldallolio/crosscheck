# Cited papers: local copies and reading notes

`fetch_papers.py` downloads the open-access copy of every paper cited in
`paper/crosscheck.bib` for which one exists, into `references/pdf/`. That folder is
**gitignored**: most of these files are not ours to redistribute (publisher or author
copyright), so the repository keeps only the script, the record of where each copy came
from (`sources.json`) and the notes below. Run the script to obtain the files:

```bash
python3 references/fetch_papers.py
```

It asks the Semantic Scholar index for an open-access location by DOI, and tries the
publisher's own open-access link and a few known project or institutional pages. Only the
DOI is sent.

## Status (2026-11-13)

21 of 50 entries were downloaded. For the others no open-access copy was found by
the script (paywalled, or only on pages that refuse automated downloads); books and web
pages are listed as such. A missing copy does not mean the paper is unavailable to you
through a library.

The notes say what was read **by the AI assistant** and what was checked against the
paper's text. "Abstract read" means only that. Nothing here replaces the author's own
reading (`AI_USAGE.md`, section 3).

| Key | Status | Source of the copy | What was read and checked |
|---|---|---|---|
| `agmai2026responsible` | book or web page |  |  |
| `albert2011more` | read 2026-11-16 (not kept), in the author's thesis | A. N. Masud, PhD thesis, Universidad Politécnica de Madrid (COSTA project page); the thesis states that its chapters on upper bounds were published as this paper and in a TOCL article | Section 4.2 ("Cost Relations with Non-Constant Cost", 4.2.1 "Linear Progression Behavior") and the overview in Section 2.2 read; the conference paper itself was not obtained (the publisher's copy redirects to a login). The cost contributed by successive applications of a recursive equation (a loop) is bounded by an arithmetic sequence, increasing or decreasing by the least progression, and summed, instead of multiplied by the number of iterations. Cited for the summation in `prop:amortised-loop` (Paper I) and in Paper II's related work. **Author: check against the paper.** |
| `albert2011closed` | not obtained; described in A. N. Masud's thesis (read 2026-11-16) |  | The thesis (its reference [5]) describes this paper as the approach in which specific upper-bound solvers for cost relations reason on the worst-case cost and obtain sound closed-form bounds; that is all Paper II claims (cost relations solved into closed forms). The paper itself not read. |
| `alias2010multi` | downloaded | open access (Semantic Scholar) | Title page read. Multi-dimensional rankings and complexity bounds of flowchart programs. |
| `baccelli1992synchronization` | book or web page |  |  |
| `bardin2008fast` | no open-access copy found |  |  |
| `benamram2014ranking` | downloaded | arXiv | Abstract read. Confirms: existence of a linear ranking function is PTIME over the rationals and coNP-complete over the integers. |
| `bonenfant2012ffx` | downloaded (2026-11-14) | TU Wien (author copy) | Sections 3 and 4 read. FFX grammar: root and context elements, location attributes (source file + line, address, label), `<loop>` with `maxcount` = maximal number of iterations per loop entry and `totalcount`; tools ignore unknown tags. Data checked on Crossref (DOI 10.1145/2392987.2392999). Used for the FFX exporter. |
| `blazy2013formal` | downloaded | HAL (Inria) | Abstract and the passages on contributions and architecture read (2026-11-16). Confirms: loop bound estimation verified in Coq, integrated into CompCert; the analyses operate on CompCert's RTL intermediate language (program slicing, value analysis, bound calculation). |
| `brockschmidt2016analyzing` | downloaded | open access (Semantic Scholar) | Abstract read. Alternating runtime and size bounds for integer programs; tool KoAT. |
| `carbonneaux2015compositional` | read 2026-11-16 (not kept) | Yale FLINT group (authors' copy) | Abstract, the start of the introduction and the passages on Clight and Coq read. Potential method of amortized analysis for C programs (tool C4B), rules for a subset of Clight (CompCert's first intermediate language), proof certificates from the derivation rules, soundness proved in Coq with respect to a cost semantics. Confirms 'certified resource bounds for C programs' and 'potential-based amortized analysis'. |
| `clangeffects` | book or web page |  |  |
| `colon2001synthesis` | downloaded | open access (Semantic Scholar) | Abstract read. Synthesis of linear ranking functions (deductive, linear constraints). |
| `cormen2009introduction` | book or web page |  |  |
| `cousot1977abstract` | no open-access copy found |  |  |
| `demichiel2008orange` | no open-access copy found (2026-11-16: Unpaywall lists none for this paper or for the ISoLA 2010 paper on oRange) |  | Not read. Paper II cites it for oRange; the description there (structured rewriting with Calipso, whole-program or partial analysis) comes from the README of oRange's source repository, and "flow analysis and abstract interpretation" from this paper's title. |
| `demoura2008z3` | downloaded | open access (Semantic Scholar) | Skimmed. |
| `demoura2021lean4` | downloaded | open access (Semantic Scholar) | Skimmed. |
| `diekert1995traces` | book or web page |  |  |
| `falk2016taclebench` | downloaded | open access (Semantic Scholar) | Sections 1 and 3.1 read. Confirms: all benchmarks are annotated with flow facts as pragmas (loop bounds with a lower and an upper bound). Correction made: the paper called TACLeBench 'the successor of' the Mälardalen benchmarks; the article says its programs are gathered from several sources, Mälardalen (MRTC) among them. |
| `falke2011termination` | downloaded | DROPS (Dagstuhl, open access) | Abstract and the description of the translation read. Confirms: instructions returning an integer such as `load` are abstracted to an unspecified value, floating-point results are arbitrary; modelling memory is listed as future work. Supports the paper's statement that values in memory become unknown inputs. |
| `floresmontoya2014cofloco` | technical-report version downloaded (2026-11-16, TU Darmstadt server, `APLAS14techReport.pdf`, 6 pages; not compared with the LNCS version) | authors' institution | Read in full: cost equations (Def. 2), SCCs with linear recursion, chains of phases and their refinement (Sec. 3, Theorem 1), forward and backward invariants (3.2). Supports Paper II's description of CoFloCo. |
| `floyd1967assigning` | no open-access copy found |  |  |
| `fox2010trustworthy` | downloaded | author's copy (Cambridge) | Abstract and introduction read (2026-11-17): a HOL4 formalization of the ARMv7 ISA, validated by testing against ARM development boards. Cited in Paper I `subsec:cycles` as the kind of validated ISA model our hand-written decoder is not. |
| `frohn2020calculus` | downloaded | arXiv | Abstract read. A calculus combining loop acceleration techniques modularly. |
| `giesl2019termcomp` | downloaded | open access (Semantic Scholar) | Skimmed. Confirms the competition has categories for C programs and C programs restricted to integers. |
| `gueneau2018fistful` | downloaded | open access (Semantic Scholar) | Abstract and contributions read. Confirms: Coq, separation logic with time credits, asymptotic (O) bounds. |
| `gulwani2009speed` | read 2026-11-16 (not kept) | Microsoft Research (authors' copy) | Abstract and the passages on counters and on ranking functions read. Symbolic bounds from counter instrumentation and linear invariant generation; the paper presents this as an alternative to synthesizing ranking functions. **Correction made:** Paper I cited it among works that derive bounds from ranking functions; it is now cited for counters and invariants only. |
| `healy2000supporting` | read 2026-11-16 (not kept) | Mälardalen University publication page (preprint, 23/09/1999) | Introduction and Section 5 ("Bounding Iterations for Non-Rectangular Loop Nests") read: the number of iterations of an inner loop whose bounds depend on an outer counter is formulated as a summation (after Sakellariou's work on load balancing) and solved, for tighter timing predictions; the timing analyser uses the average number of inner iterations. Cited for the summation in `prop:amortised-loop` (Paper I) and in Paper II's related work. |
| `gustafsson2010malardalen` | downloaded | DROPS (Dagstuhl, open access) | Skimmed. Describes the Mälardalen WCET benchmark suite. |
| `haslbeck2018hoare` | downloaded | publisher (Springer, open access) | Sections 1-3.1 and 5 read. Three logics (Nielson style, potentials after Carbonneaux et al., separation logic with time credits) for the deterministic language IMP, in Isabelle/HOL; sound and complete; verified VCGs; a valid triple asserts termination within the bound. The comparison in subsec:cost-logic was rewritten from this reading. |
| `heckmann2013ait` | downloaded (2026-11-14) | AbsInt web site | Section 4 read (user annotations): `loop "R" + n loops [begin\|end] max j;` (n-th loop of routine R, counted from 1, in the executable), source annotations `/* ai: loop here max j; */`. Undated; PDF metadata 2013. Used for the AIS exporter. |
| `hoffmann2012multivariate` | read 2026-11-16 (not kept) | author's copy (Yale) | Abstract and introduction read: the type system relies on the potential method of amortized analysis (after Hofmann and Jost, Tarjan). Supports both citations (amortized analysis; potential method). |
| `hoffmann2022two` | downloaded | open access (Semantic Scholar) | Abstract read. Survey of automatic amortized resource analysis. |
| `infercost` | book or web page |  |  |
| `kahn1987natural` | no open-access copy found |  |  |
| `kincaid2019closed` | no open-access copy found |  |  |
| `lattner2004llvm` | downloaded | LLVM project page | Skimmed. Describes the LLVM framework; it does not describe ScalarEvolution, which the paper uses as a tool and cites LLVM for. |
| `leroy2009coinductive` | downloaded | arXiv | Abstract read. Coinductive big-step semantics describing diverging evaluations. |
| `li1995ilp` | read 2026-11-16 (not kept) | UCI archive of DAC papers | Abstract and the start of the introduction read. Bounds on running time by considering all paths implicitly with integer linear programming (tool cinderella, Intel i960). Confirms the citations for IPET. |
| `lommen2022automatic` | downloaded | publisher (Springer, open access) | Abstract read. Runtime bounds for triangular weakly non-linear loops, in KoAT. |
| `manna1974mathematical` | book or web page |  |  |
| `maroneze2014formally` | downloaded | open access (Semantic Scholar) | Abstract and the passages on RTL, assembly and IPET read (2026-11-16). Confirms: formally verified WCET estimation integrated into CompCert, loop bound estimation on RTL transported to assembly, IPET at assembly level. 2026-11-17: Sections 2.2 and 3.4 read for Paper I `subsec:cycles`: cost model with one cycle per instruction; loop bounds as ILP constraints on header counts; ILP generation proved, the external solver's result validated in Coq by substitution and a Farkas certificate of the infeasibility of a larger objective. |
| `mathlib2020` | downloaded | arXiv | Abstract read. |
| `matiyasevich1970enumerable` | no open-access copy found |  |  |
| `nielson1987hoare` | no open-access copy found |  |  |
| `podelski2004complete` | no open-access copy found |  |  |
| `podelski2004transition` | no open-access copy found |  |  |
| `puschner1989calculating` | no open-access copy found |  |  |
| `sarif2023` | web page (2026-11-14) | OASIS | Title and editors read; the JSON schema (`sarif-2.1/schema/sarif-schema-2.1.0.json` of the OASIS repository) is used by the tests. |
| `schrijver1986theory` | book or web page |  |  |
| `sewell2017high` | downloaded | course copy (UNSW) | Contributions list, Sections 2.1, 2.4 and 4.1 read (2026-11-17): WCET of the seL4 binary with Chronos and an ILP solver; the binary CFG is obtained by a decompiler that proves (HOL4) its output against the Cambridge ARM model; the final conversion into Chronos's CFG is not proved ("we could formalise the meaning of the CFG and prove it captured the control paths of the binary ... we leave this to future work"). Cited in Paper I `subsec:cycles`. |
| `shaw1989reasoning` | no open-access copy found (2026-11-16) Wilhelm et al. 2008, Section 2.1.2, credit Shaw 1989 with the structure-based approach (the bound of `A; B` is the sum of the bounds), which supports the citation for the timing schema. |
| `sinn2014complexity` | downloaded | arXiv | Abstract and the start of the introduction read (2026-11-16). Bound analysis with amortisation via lexicographic ranking functions on vector addition systems; the tool is called Loopus in the paper. |
| `wegbreit1975mechanical` | no open-access copy found |  |  |
| `wilhelm2008worst` | read 2026-11-16 (not kept) | Mälardalen University publication page | Sections 1-3 and the tool descriptions read: users supply loop bounds and flow facts as annotations (aiT, Bound-T); IPET for bound calculation; context-dependent instruction times on processors with caches and pipelines; the structure-based approach is credited to Shaw 1989 (sum for sequences). Supports every citation. |
| `winskel1993formal` | book or web page |  |  |
| `armCortexM0trm` | read 2026-11-16 (not kept) | Arm documentation service (public) | Section 3.3, Table 3-1 (instruction summary with cycle counts) read in full and encoded as a test (`benchmarks/cycles/test_m0.py`). Not on Crossref (a manual). |
| `audsley1993applying` | read 2026-11-16 (not kept) | course copy (Univ. of Padua) | Abstract, the start of the introduction, the passages that mention Joseph and Pandya and the reference list read. Exact schedulability analysis for static-priority pre-emptive dispatching, with blocking and release jitter; it attributes the response-time equation, in a different form, to Joseph and Pandya (its reference 6: M. Joseph and P. Pandya, Computer Journal 29(5), 1986, pp. 390-395, which confirms both authors of `joseph1986finding`). |
| `blumofe1999scheduling` | read 2026-11-16 (not kept) | course copy (UT Austin) | Abstract and the passage stating Theorem 1 read. Theorem 1 (greedy-scheduling theorem): any greedy P-processor schedule of a computation with work T1 and critical-path length T-infinity takes at most T1/P + T-infinity; the paper presents it as an adaptation of theorems of Brent (1974) and Graham (1966, 1969). Paper I now says so. |
| `cerqueira2016prosa` | read 2026-11-16 (not kept) | MPI-SWS (authors' copy) | Abstract and the passages on goals and the case study read. Prosa: a Coq foundation for mechanized schedulability analyses, with a case study on multiprocessor response-time analysis. Confirms 'a mechanized theory of response-time analysis, far more general'. |
| `graham1966bounds` | read 2026-11-16 (not kept) | Internet Archive scan of the Bell System Technical Journal | Abstract and the description of the system read (OCR of a scan). Identical processors, tasks with a partial order, a priority list scanned by a free processor; bounds on the ratio of finishing times. Paper I states its proposition 'after Graham', for independent tasks. |
| `joseph1986finding` | not obtained |  | Not read. Its authors and its role (the response-time equation of fixed-priority scheduling) are confirmed by `audsley1993applying`, which was read. |
| `kirchner2015framac` | read 2026-11-16 (not kept) | HAL (CEA) | Abstract and the passage on ACSL loop invariants read. Confirms the citation for Frama-C and ACSL in Paper II. |
| `necula1997proof` | not obtained |  | Not read (the author's page no longer serves it). Cited for the principle of proof-carrying code only. |
| `necula2000translation` | read 2026-11-16 (not kept) | UC Berkeley (author's copy) | Abstract and the start of the introduction read. A translation validation infrastructure for GCC that compares the intermediate form before and after each pass. Confirms the citation. |
| `nipkow2002hoare` | read 2026-11-16 (not kept) | TU Munich (author's copy) | Abstract, the start of the introduction and the rules for total correctness read. Sound and complete Hoare logics for recursive procedures with unbounded nondeterminism, in Isabelle/HOL; the rule for total correctness of a recursive call uses a well-founded relation and an assumption on the calls. Confirms 'the usual rule for recursive procedures' for rule (9). |
| `pnueli1998translation` | read 2026-11-16 (not kept) | publisher (Springer, free to read) | Abstract and the start of the introduction read. Introduces translation validation: each run of the translator is followed by a validation of its output against its input. Confirms the citation. |

`ballabriga2010otawa` (added 2026-11-16, cited in Paper II for the OTAWA tool, which was
run): not read; title, authors, series, pages and year checked on Crossref
(DOI 10.1007/978-3-642-16256-5_6). `armCortexM0trm` is a manual without a DOI.

## Not read

Updated 2026-11-16, after a second attempt to obtain the papers on which the text relies
(the files of that attempt were read and not kept).

`nielson1987hoare` (the origin of Hoare logics for running time) could not be obtained;
what Paper I says about it rests on its description in `haslbeck2018hoare`, and the paper
carries an `\authortodo` for it. Also not obtained and not read, each with an
`\authortodo` in the paper that relies on it: `necula1997proof`, `joseph1986finding`
(Paper I), `puschner1989calculating`, `demichiel2008orange` (Paper II); `shaw1989reasoning`
and `albert2011closed` were not obtained either but are cited as described in sources that
were read (2026-11-16: `wilhelm2008worst` and A. N. Masud's thesis);
`hoffmann2012multivariate` and `wilhelm2008worst` were read on 2026-11-16. The other entries without a copy were not read
either and are cited for well-known results: `cousot1977abstract`,
`podelski2004transition`, `podelski2004complete`, `wegbreit1975mechanical`,
`floyd1967assigning`, `bardin2008fast`, `kincaid2019closed`, `kahn1987natural`,
`matiyasevich1970enumerable`, and the books.

A reading by the AI assistant does not replace the author's: the notes say which
passages were read (mostly abstracts and the passages found by searching the text for the
claim to check, not whole papers), and the sentences that cite each paper are short enough to compare.
