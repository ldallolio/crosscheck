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
| `albert2011more` | read 2026-11-16 in the author's thesis; the paper read 2026-11-17 | A. N. Masud, PhD thesis (COSTA project page); `references/pdf/conf-vmcai-AlbertGM11.pdf` (provided by the author, not committed: a 15-page LaTeX copy with the paper's title and authors) | Thesis: Section 4.2 and the overview of Section 2.2. Paper: Sections 1 to 4 read. Instead of the worst-case cost for every iteration times the number of iterations, the costs of the successive iterations are bounded by an arithmetic sequence (starting from the worst-case cost and decreasing by an under-approximation of the differences) whose sum is the bound, through a worst-case recurrence relation solved by a computer algebra system; the same for geometric progressions (Section 4.2, e.g. merge sort, with an improved complexity order); also lower bounds. Confirms the citation in `prop:amortised-loop` (Paper I) and in Paper II's related work. |
| `crary2000resource` | read 2026-11-18 (not kept) | Cornell TALC project page (`res.pdf`, the POPL 2000 version, revised Oct. 1999) | Abstract, Sections 1 and 2 read: a decidable type system (LXres, implemented as TALres in Typed Assembly Language) certifying bounds on resource consumption, with a virtual clock in function types that winds down (stepped at function calls); running times may depend on arguments (dependent types simulated by sum and inductive kinds); a certifying compiler from an annotated source language; bounds are certified, not inferred. Crossref spells the second author "Stephnie"; the entry uses "Stephanie", as on the paper. Cited in Paper III's related work. |
| `cullmann2007data` | read 2026-11-18 (not kept) | Dagstuhl DROPS (open access) | Sections 1, 2 and 5 read: aiT's loop-bound analysis on executables, a data-flow analysis of loop counters ("invariants": the change of a counter per iteration, in the expression language IVALA) using intervals from aiT's value analysis, start values, evaluation of the loop tests, overflows of size-limited types handled; compared with aiT's pattern-based analysis. DOI checked on DataCite. Cited in Paper III's related work. |
| `albert2011closed` | read 2026-11-17 | `references/pdf/albert2011closed.pdf` (provided by the author, not committed; J. Autom. Reasoning 46:161-203) | Abstract, Section 1 and the passages on ranking functions and maximization (Sections 5-6) read: cost relations produced by a cost analysis are solved into closed-form upper bounds, by bounding the number of iterations with ranking functions, the cost of each with invariants and maximization, and partial evaluation. Confirms the citations ("cost relations solved into closed forms") in both papers. |
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
| `demichiel2008orange` | read 2026-11-17 | `references/pdf/demichiel2008orange_bis.pdf` (the RTCSA 2008 paper, provided by the author, not committed); also `demichiel2008orange.pdf`, a six-page summary of it by A. Bonenfant, M. de Michiel and P. Sainrat (September 2008) | Read entirely. Loop bounds of C programs by flow analysis and abstract interpretation (an extension of Ammarguellat and Harrison's recognition of recurrence relations): loops normalised, then an annotated context tree in which every call is expanded (no recursion), `total` and `max` expressions per loop built and evaluated per calling context; Calipso removes `goto`, `break`, `continue` and irregular `switch` beforehand; a comparison with Ermedahl et al. on the Malardalen benchmarks (84% of loops bounded). Confirms Paper II's description; "multiple returns" and the two modes (whole program or functions in isolation) come from the tool's README, as Paper II says. |
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
| `healy2000supporting` | read 2026-11-16 (preprint, not kept); journal version provided by the author on 2026-11-17 | Mälardalen University publication page (preprint, 23/09/1999); `references/pdf/healy2000supporting.pdf` (journal version, Real-Time Systems 18, 129-156, not committed) | Introduction and Section 5 ("Bounding Iterations for Non-Rectangular Loop Nests") read, in the preprint and again in the journal version: the number of iterations of an inner loop whose bounds depend on an outer counter is formulated as a summation (the framework is based on Sakellariou's work) and solved, for tight timing predictions of non-rectangular nests; the timing analyser uses the average number of inner iterations. Cited for the summation in `prop:amortised-loop` (Paper I) and in Paper II's related work. |
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
| `nielson1984hoare` | downloaded | Edinburgh Research Archive (handle 1842/15527, open) | Abstract and acknowledgements read (2026-11-17): Hoare logics extended to run-time properties, three proof systems for iterative programs (sound and complete), one extended to nested recursive procedures with call-by-value parameters, a restricted "time T" system; no clock variables inserted; supervised by G. Plotkin. Supports the attribution in Paper I `subsec:cost-logic`. |
| `nielson1987hoare` | provided by the author (2026-11-17), not committed | Science of Computer Programming 9 (1987) 107-136 | Abstract, Section 1 and the proof system R of Section 3 (rules R-1 to R-6 and their explanation) read (2026-11-17): a Hoare-like system for while programs proving total correctness and properties of the computation time, no clock variable; validity: termination in a final state satisfying Q and a time satisfying R; composition [R-3] relates the time of c2 to the initial values through c1's relational postcondition; while rule [R-4] bounds the unfoldings by a natural-number variable z; arithmetically sound and complete; bubble sort example. Supports Paper I `subsec:cost-logic` and the remark after `prop:summary-call`. |
| `podelski2004complete` | no open-access copy found |  |  |
| `podelski2004transition` | no open-access copy found |  |  |
| `puschner1989calculating` | read 2026-11-17 | `references/pdf/puschner1989calculating.pdf` (provided by the author, not committed) | Read entirely (Sections 1-5 and Table 1). Rules for the maximum execution time (MAXT) of structured programs: sum for sequences, condition plus the maximum of the branches for alternatives, iteration bound times (body + condition) plus initialisation and one more test for loops, organisation plus body for subroutines (Table 1); programs without recursion, function pointers or `goto`, with bounded loops (`MAX_COUNT`, `MAX_TIME`). Markers and scopes bound how many times a point is passed within a loop; loop sequences bound the total iterations of several loops. Confirms Paper I's "timing schema" attribution (with Shaw) and the added sentence on markers (Paper I, related work, paragraph "WCET analysis"). |
| `sarif2023` | web page (2026-11-14) | OASIS | Title and editors read; the JSON schema (`sarif-2.1/schema/sarif-schema-2.1.0.json` of the OASIS repository) is used by the tests. |
| `schrijver1986theory` | book or web page |  |  |
| `sewell2017high` | downloaded | course copy (UNSW) | Contributions list, Sections 2.1, 2.4 and 4.1 read (2026-11-17): WCET of the seL4 binary with Chronos and an ILP solver; the binary CFG is obtained by a decompiler that proves (HOL4) its output against the Cambridge ARM model; the final conversion into Chronos's CFG is not proved ("we could formalise the meaning of the CFG and prove it captured the control paths of the binary ... we leave this to future work"). Cited in Paper I `subsec:cycles`. |
| `sewell2016complete` | read 2026-11-18 (not kept) | Trustworthy Systems publication page (RTAS 2016 PDF) | Sections I to III read: loop bounds and infeasible paths of the seL4 binary determined with the translation-validation toolchain (SMT models of the binary's loops, explicit unrolling up to about 128 iterations or induction over a symbolic n-th iteration with guessed linear invariants, refined by binary search; C-level facts through the C-binary correspondence; call-stack information); the binary CFG from a decompiler proved against the Cambridge ARM model, except a final simplification (future work); also Mälardalen benchmarks in their C subset. Cited in Paper III's related work. |
| `shaw1989reasoning` | read 2026-11-17 | `references/pdf/shaw1989reasoning.pdf` (provided by the author, not committed) | Abstract, Sections I-III read. Upper and lower bounds `T(S) = [tmin, tmax]` on execution times derived from those of primitive entities by schemas: a sum for sequential composition, the minimum and maximum over the branches (plus the test and the transfers) for conditionals, for `while` loops a timing invariant with a counter `n` of iterations (`n` times the body plus the test); and an extension of Hoare logic with a real-time variable advanced by `T(S)` at each statement. Confirms the timing-schema citations of both papers and the clause added to Paper I's `subsec:cost-logic` (Shaw's Hoare logic with real time). |
| `sinn2014complexity` | downloaded | arXiv | Abstract and the start of the introduction read (2026-11-16). Bound analysis with amortisation via lexicographic ranking functions on vector addition systems; the tool is called Loopus in the paper. |
| `wegbreit1975mechanical` | no open-access copy found |  |  |
| `wilhelm2008worst` | read 2026-11-16 (not kept) | Mälardalen University publication page | Sections 1-3 and the tool descriptions read: users supply loop bounds and flow facts as annotations (aiT, Bound-T); IPET for bound calculation; context-dependent instruction times on processors with caches and pipelines; the structure-based approach is credited to Shaw 1989 (sum for sequences). Supports every citation. |
| `winskel1993formal` | book or web page |  |  |
| `armCortexM0trm` | read 2026-11-16 (not kept) | Arm documentation service (public) | Section 3.3, Table 3-1 (instruction summary with cycle counts) read in full and encoded as a test (`benchmarks/cycles/test_m0.py`). Not on Crossref (a manual). |
| `audsley1993applying` | read 2026-11-16 (not kept) | course copy (Univ. of Padua) | Abstract, the start of the introduction, the passages that mention Joseph and Pandya and the reference list read. Exact schedulability analysis for static-priority pre-emptive dispatching, with blocking and release jitter; it attributes the response-time equation, in a different form, to Joseph and Pandya (its reference 6: M. Joseph and P. Pandya, Computer Journal 29(5), 1986, pp. 390-395, which confirms both authors of `joseph1986finding`). |
| `blumofe1999scheduling` | read 2026-11-16 (not kept) | course copy (UT Austin) | Abstract and the passage stating Theorem 1 read. Theorem 1 (greedy-scheduling theorem): any greedy P-processor schedule of a computation with work T1 and critical-path length T-infinity takes at most T1/P + T-infinity; the paper presents it as an adaptation of theorems of Brent (1974) and Graham (1966, 1969). Paper I now says so. |
| `cerqueira2016prosa` | read 2026-11-16 (not kept) | MPI-SWS (authors' copy) | Abstract and the passages on goals and the case study read. Prosa: a Coq foundation for mechanized schedulability analyses, with a case study on multiprocessor response-time analysis. Confirms 'a mechanized theory of response-time analysis, far more general'. |
| `graham1966bounds` | read 2026-11-16 (not kept) | Internet Archive scan of the Bell System Technical Journal | Abstract and the description of the system read (OCR of a scan). Identical processors, tasks with a partial order, a priority list scanned by a free processor; bounds on the ratio of finishing times. Paper I states its proposition 'after Graham', for independent tasks. |
| `joseph1986finding` | read 2026-11-17 | `references/pdf/joseph1986finding_bis.pdf` (scan provided by the author, not committed; text by OCR with tesseract); the earlier `joseph1986finding.pdf` was an unrelated paper (O'Rourke et al., J. Algorithms 1986) | Read entirely (6 pages). Authors M. Joseph and P. Pandya (as our entry; Crossref lists only the first). Exact worst-case response times of devices at fixed priority levels: equation (1), `RT_i = sum_{j<i} ceil(RT_i/T_j) C_j + C_i`, computed by the recursive function `Response` started at `C_i` (equation 6), proved correct by computational induction, terminating under the load condition (4); the analysis assumes the critical instant (all inputs together, after Liu and Layland); also buffers and multiprocessors. Confirms Paper I's citation and the added sentences after `thm:response-time`. |
| `kirchner2015framac` | read 2026-11-16 (not kept) | HAL (CEA) | Abstract and the passage on ACSL loop invariants read. Confirms the citation for Frama-C and ACSL in Paper II. |
| `necula1997proof` | read 2026-11-17 | `references/pdf/necula1997proof.pdf` (scanned copy provided by the author, not committed; text obtained by OCR with tesseract) | Abstract, Sections 1, 2, 6 and 7 read: the code producer supplies with the native code a proof of its adherence to a safety policy; the consumer validates the proof by a simple, fast algorithm and trusts only that algorithm and the safety policy; the staging of verification into certification and proof validation is stated as the main contribution. The safety properties are partial-correctness invariants (no resource bounds). Confirms the citation for the principle in Paper I (`subsec:checker`) and Paper II (related work). |
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
on 2026-11-17 the thesis it derives from, `nielson1984hoare` (open, Edinburgh), was read and
is cited with it; the same day the author provided the paper, which was read (see its row). A
third attempt (2026-11-17) found no open copy of `necula1997proof` (the author's page no
longer serves it), `demichiel2008orange`, `albert2011more` (publisher preview only),
`joseph1986finding`, `puschner1989calculating`. On 2026-11-17 the author provided copies of
`puschner1989calculating`, `necula1997proof` and the journal version of `healy2000supporting`
(read, see their rows), a summary of `demichiel2008orange` by its authors (read; the paper
itself is still not read) and, under the name `joseph1986finding.pdf`, an unrelated paper.
Later the same day the author provided `joseph1986finding`, `demichiel2008orange` and
`albert2011more`, all read (see their rows). Then `shaw1989reasoning` and `albert2011closed`, both read (see their rows). Formerly not obtained: `shaw1989reasoning`
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
