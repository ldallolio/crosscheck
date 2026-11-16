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
| `albert2011closed` | no open-access copy found |  |  |
| `alias2010multi` | downloaded | open access (Semantic Scholar) | Title page read. Multi-dimensional rankings and complexity bounds of flowchart programs. |
| `baccelli1992synchronization` | book or web page |  |  |
| `bardin2008fast` | no open-access copy found |  |  |
| `benamram2014ranking` | downloaded | arXiv | Abstract read. Confirms: existence of a linear ranking function is PTIME over the rationals and coNP-complete over the integers. |
| `bonenfant2012ffx` | downloaded (2026-11-14) | TU Wien (author copy) | Sections 3 and 4 read. FFX grammar: root and context elements, location attributes (source file + line, address, label), `<loop>` with `maxcount` = maximal number of iterations per loop entry and `totalcount`; tools ignore unknown tags. Data checked on Crossref (DOI 10.1145/2392987.2392999). Used for the FFX exporter. |
| `blazy2013formal` | downloaded | HAL (Inria) | Abstract read. Confirms: loop bound estimation verified in Coq, integrated into CompCert. |
| `brockschmidt2016analyzing` | downloaded | open access (Semantic Scholar) | Abstract read. Alternating runtime and size bounds for integer programs; tool KoAT. |
| `carbonneaux2015compositional` | no open-access copy found |  |  |
| `clangeffects` | book or web page |  |  |
| `colon2001synthesis` | downloaded | open access (Semantic Scholar) | Abstract read. Synthesis of linear ranking functions (deductive, linear constraints). |
| `cormen2009introduction` | book or web page |  |  |
| `cousot1977abstract` | no open-access copy found |  |  |
| `demichiel2008orange` | no open-access copy found |  |  |
| `demoura2008z3` | downloaded | open access (Semantic Scholar) | Skimmed. |
| `demoura2021lean4` | downloaded | open access (Semantic Scholar) | Skimmed. |
| `diekert1995traces` | book or web page |  |  |
| `falk2016taclebench` | downloaded | open access (Semantic Scholar) | Sections 1 and 3.1 read. Confirms: all benchmarks are annotated with flow facts as pragmas (loop bounds with a lower and an upper bound). Correction made: the paper called TACLeBench 'the successor of' the Mälardalen benchmarks; the article says its programs are gathered from several sources, Mälardalen (MRTC) among them. |
| `falke2011termination` | downloaded | DROPS (Dagstuhl, open access) | Abstract and the description of the translation read. Confirms: instructions returning an integer such as `load` are abstracted to an unspecified value, floating-point results are arbitrary; modelling memory is listed as future work. Supports the paper's statement that values in memory become unknown inputs. |
| `floresmontoya2014cofloco` | no open-access copy found |  |  |
| `floyd1967assigning` | no open-access copy found |  |  |
| `frohn2020calculus` | downloaded | arXiv | Abstract read. A calculus combining loop acceleration techniques modularly. |
| `giesl2019termcomp` | downloaded | open access (Semantic Scholar) | Skimmed. Confirms the competition has categories for C programs and C programs restricted to integers. |
| `gueneau2018fistful` | downloaded | open access (Semantic Scholar) | Abstract and contributions read. Confirms: Coq, separation logic with time credits, asymptotic (O) bounds. |
| `gulwani2009speed` | no open-access copy found |  |  |
| `gustafsson2010malardalen` | downloaded | DROPS (Dagstuhl, open access) | Skimmed. Describes the Mälardalen WCET benchmark suite. |
| `haslbeck2018hoare` | downloaded | publisher (Springer, open access) | Sections 1-3.1 and 5 read. Three logics (Nielson style, potentials after Carbonneaux et al., separation logic with time credits) for the deterministic language IMP, in Isabelle/HOL; sound and complete; verified VCGs; a valid triple asserts termination within the bound. The comparison in subsec:cost-logic was rewritten from this reading. |
| `heckmann2013ait` | downloaded (2026-11-14) | AbsInt web site | Section 4 read (user annotations): `loop "R" + n loops [begin\|end] max j;` (n-th loop of routine R, counted from 1, in the executable), source annotations `/* ai: loop here max j; */`. Undated; PDF metadata 2013. Used for the AIS exporter. |
| `hoffmann2012multivariate` | no open-access copy found |  |  |
| `hoffmann2022two` | downloaded | open access (Semantic Scholar) | Abstract read. Survey of automatic amortized resource analysis. |
| `infercost` | book or web page |  |  |
| `kahn1987natural` | no open-access copy found |  |  |
| `kincaid2019closed` | no open-access copy found |  |  |
| `lattner2004llvm` | downloaded | LLVM project page | Skimmed. Describes the LLVM framework; it does not describe ScalarEvolution, which the paper uses as a tool and cites LLVM for. |
| `leroy2009coinductive` | downloaded | arXiv | Abstract read. Coinductive big-step semantics describing diverging evaluations. |
| `li1995ilp` | no open-access copy found |  |  |
| `lommen2022automatic` | downloaded | publisher (Springer, open access) | Abstract read. Runtime bounds for triangular weakly non-linear loops, in KoAT. |
| `manna1974mathematical` | book or web page |  |  |
| `maroneze2014formally` | downloaded | open access (Semantic Scholar) | Abstract read. Confirms: formally verified WCET estimation tool integrated into CompCert (loop bounds + IPET). |
| `mathlib2020` | downloaded | arXiv | Abstract read. |
| `matiyasevich1970enumerable` | no open-access copy found |  |  |
| `nielson1987hoare` | no open-access copy found |  |  |
| `podelski2004complete` | no open-access copy found |  |  |
| `podelski2004transition` | no open-access copy found |  |  |
| `puschner1989calculating` | no open-access copy found |  |  |
| `sarif2023` | web page (2026-11-14) | OASIS | Title and editors read; the JSON schema (`sarif-2.1/schema/sarif-schema-2.1.0.json` of the OASIS repository) is used by the tests. |
| `schrijver1986theory` | book or web page |  |  |
| `shaw1989reasoning` | no open-access copy found |  |  |
| `sinn2014complexity` | downloaded | arXiv | Abstract read. Bound analysis with amortisation via lexicographic ranking functions on vector addition systems. |
| `wegbreit1975mechanical` | no open-access copy found |  |  |
| `wilhelm2008worst` | no open-access copy found |  |  |
| `winskel1993formal` | book or web page |  |  |

## Not read

`nielson1987hoare` (the origin of Hoare logics for running time) could not be obtained;
what the paper says about it rests on its description in `haslbeck2018hoare`, and the
paper carries an `\authortodo` for it. The other entries without a copy were not read
either: `cousot1977abstract`, `podelski2004transition`, `podelski2004complete`,
`wilhelm2008worst`, `li1995ilp`, `wegbreit1975mechanical`, `floyd1967assigning`,
`gulwani2009speed`, `albert2011closed`, `hoffmann2012multivariate`,
`carbonneaux2015compositional`, `bardin2008fast`, `shaw1989reasoning`,
`puschner1989calculating`, `kincaid2019closed`, `kahn1987natural`, `demichiel2008orange`,
`floresmontoya2014cofloco`, `matiyasevich1970enumerable`, and the books.

`kirchner2015framac` (added 2026-11-16, cited in Paper II for ACSL and Frama-C): not read;
its title, authors, journal, volume, pages and year were checked on Crossref
(DOI 10.1007/s00165-014-0326-7). Cited from the assistant's general knowledge of what
Frama-C and ACSL are: **the author must check that the citation is the appropriate one**.
