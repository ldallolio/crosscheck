# Part 8 — The bibliography, as a map

`paper/crosscheck.bib`, shared by the three papers; each paper's list contains only the
entries it cites. Theory-side related work (cost logics, ranking functions,
closed forms, amortisation, mechanised cost) is discussed in Paper I's `sec:related`; tool-side
related work (bound analysers, WCET flow analysis, verified and certified bounds, Clang's
function effects) in Paper II's `sec:related`. On 2026-11-13/14 the bibliographic data of
every entry were checked against Crossref, DataCite or Open Library (one error fixed). The
column **Read** says how far the assistant read each work (2026-11-22).
Summaries are short on purpose; read the originals before quoting a detail.

```mermaid
flowchart LR
  SEM["Semantics<br/>Manna, Winskel, Kahn,<br/>Leroy & Grall, Diekert,<br/>Courcelle (trees)"] --> CC["CrossCheck"]
  TERM["Ranking functions<br/>Floyd, Colón & Sipma,<br/>Podelski & Rybalchenko,<br/>Ben-Amram & Genaim"] --> CC
  COST["Cost / bound analysis<br/>Wegbreit, SPEED, Alias,<br/>Albert, Sinn, KoAT, CoFloCo"] --> CC
  ACC["Loop acceleration,<br/>closed forms<br/>Bardin, Frohn, Kincaid"] --> CC
  AARA["Amortised analysis<br/>Tarjan, Hoffmann, Carbonneaux,<br/>Hoffmann & Jost, Atkey"] --> CC
  WCET["WCET<br/>Wilhelm, Li & Malik, Shaw,<br/>Puschner & Koza, oRange,<br/>TACLeBench, Mälardalen"] --> CC
  MECH["Mechanised cost<br/>Blazy, Maroneze, Guéneau,<br/>Haslbeck & Nipkow, Nielson, Nipkow"] --> CC
  TOOLS["Tools<br/>Z3, Lean, mathlib, LLVM,<br/>llvm2kittel, Infer, TermComp"] --> CC
  PCC["Proof-carrying code and<br/>translation validation<br/>Necula, Pnueli et al."] --> CC
  RT["Real-time scheduling<br/>Joseph & Pandya, Audsley,<br/>Graham, Prosa"] --> CC
```

## Theory (Paper I)

| Key | Work | Role in the papers | Read |
|---|---|---|---|
| `manna1974mathematical` | Manna, *Mathematical Theory of Computation*, 1974 | fixed points, program semantics background | book or web page |
| `winskel1993formal` | Winskel, *Formal Semantics of Programming Languages*, 1993 | big-step semantics | book or web page |
| `kahn1987natural` | Kahn, *Natural Semantics*, 1987 | big-step (natural) semantics | not obtained |
| `leroy2009coinductive` | Leroy & Grall, coinductive big-step semantics, 2009 | divergence captured coinductively (contrast) | read (parts) |
| `diekert1995traces` | Diekert & Rozenberg, *The Book of Traces*, 1995 | trace monoids | book or web page |
| `courcelle1983trees` | Courcelle, *Fundamental Properties of Infinite Trees*, 1983 | the order on trees (Section 2.4): Paper I's tree order with the leaf as Ω | read (Section 2.4) |
| `matiyasevich1970enumerable` | Matiyasevich, 1970 | undecidability for polynomial arithmetic | not obtained |
| `baccelli1992synchronization` | Baccelli et al., *Synchronization and Linearity*, 1992 | the (max,+) semiring | read (Chapter 3) |
| `cousot1977abstract` | Cousot & Cousot, abstract interpretation, 1977 | contrast: fixed points in abstract domains | read (introduction) |
| `floyd1967assigning` | Floyd, *Assigning Meanings to Programs*, 1967 | ranking functions; also the number of steps as a bound, lexicographic tuples, after Perlis and Gorn | read |
| `colon2001synthesis` | Colón & Sipma, 2001 | linear ranking synthesis by Farkas | read (parts) |
| `podelski2004complete` | Podelski & Rybalchenko, 2004 | complete linear ranking synthesis (LP, affine Farkas) | read |
| `podelski2004transition` | Podelski & Rybalchenko, 2004 | transition invariants | not obtained |
| `benamram2014ranking` | Ben-Amram & Genaim, 2014 | linear ranking: PTIME over ℚ, coNP-complete over ℤ | read (parts) |
| `schrijver1986theory` | Schrijver, 1986 | Farkas' Lemma (affine form: Corollary 7.1h, needs satisfiable premises for the converse) | read (Section 7.6) |
| `shaw1989reasoning`, `puschner1989calculating` | Shaw; Puschner & Koza, 1989 | the timing schema | read |
| `nielson1987hoare` | Nielson, 1987 | first Hoare-like logic for computation time; its while rule sums a recurrence (bubble sort): earliest form of the amortised loop rule | provided by the author (2026-1 |
| `haslbeck2018hoare` | Haslbeck & Nipkow, 2018 | three time logics for IMP in Isabelle, sound and complete: closest prior work to the cost logic | read (parts) |
| `nipkow2002hoare` | Nipkow, 2002 | rule for recursive procedures | read |
| `necula1997proof` | Necula, 1997 | proof-carrying code: the idea behind the checker | read |
| `blumofe1999scheduling` | Blumofe & Leiserson, 1999 | work and span (parallelism paragraph) | read |
| `cormen2009introduction` | Cormen et al. | recurrences, Master Theorem | read (Theorem 4.1) |

## Cost and bound analysis

| Key | Work | Role | Read |
|---|---|---|---|
| `wegbreit1975mechanical` | Wegbreit, 1975 | first automatic cost analysis | read (parts) |
| `gulwani2009speed` | Gulwani et al., SPEED, 2009 | bounds from counters and invariants | read |
| `alias2010multi` | Alias et al., 2010 | multi-dimensional rankings, complexity bounds | read (parts) |
| `albert2011closed` | Albert et al., 2011 | cost relations solved in closed form (COSTA/PUBS) | read |
| `sinn2014complexity` | Sinn et al., 2014 | amortised bounds via lexicographic rankings (Loopus) | read (parts) |
| `brockschmidt2016analyzing` | Brockschmidt et al., 2016 | runtime and size bounds (KoAT) | read (parts) |
| `lommen2022automatic` | Lommen et al., 2022 | KoAT2, twn-loops | read (parts) |
| `floresmontoya2014cofloco` | Flores-Montoya & Hähnle, 2014 | CoFloCo | technical-report version downl |
| `kincaid2019closed`, `frohn2020calculus`, `bardin2008fast` | closed forms of loops, loop acceleration | contrast with exact closed forms (not cost analyses) | read (parts) |
| `hoffmann2012multivariate`, `carbonneaux2015compositional`, `hoffmann2022two` | amortised resource analysis (RAML, C4B), survey | contrast: amortisation; certified bounds for C in Coq | read |
| `tarjan1985complexity` | Tarjan, *Amortized Computational Complexity*, 1985 | the potential method (credited to Sleator): the size potential | read |
| `atkey2010amortised` | Atkey, 2010 (LMCS 2011) | amortised resources in separation logic, sound in Coq, annotations by LP: the closest design | read (parts) |

## WCET and benchmarks (Paper II)

| Key | Work | Role | Read |
|---|---|---|---|
| `wilhelm2008worst` | Wilhelm et al., WCET survey, 2008 | what WCET analysis needs | read |
| `li1995ilp` | Li & Malik, IPET, 1995 | path-based bound calculation | read |
| `demichiel2008orange` | de Michiel et al., oRange, 2008 | WCET loop-bound tool compared | read |
| `falk2016taclebench`, `gustafsson2010malardalen` | TACLeBench; Mälardalen | the benchmarks (TACLeBench gathers several suites, Mälardalen among them) | read (parts) |
| `blazy2013formal`, `maroneze2014formally` | Blazy, Maroneze et al. | loop bounds and WCET verified in Coq/CompCert | read (parts) |
| `gueneau2018fistful` | Guéneau et al., 2018 | asymptotic bounds in Coq | read (parts) |
| `giesl2019termcomp` | Giesl et al., TermComp, 2019 | TPDB benchmarks | read (parts) |

## Tools

| Key | Work | Read |
|---|---|---|
| `demoura2008z3`, `demoura2021lean4`, `mathlib2020` | Z3, Lean 4, mathlib | read (parts) |
| `lattner2004llvm` | LLVM (ScalarEvolution is used, not described there) | read (parts) |
| `falke2011termination` | llvm2kittel: memory loads become unknown values | read (parts) |
| `infercost` | Infer cost checker documentation ("We do not handle recursion") | book or web page |
| `clangeffects` | Clang function effects / RealtimeSanitizer documentation | book or web page |
| `agmai2026responsible` | AGMAI policy on AI-generated mathematics | book or web page |
| `crosscheckTheory`, `crosscheckTool` | the two companion papers | — |

## Added in steps 5-6 (Nov 2026; data checked on Crossref, content not read)

| Key | Work | Role in the papers | Read |
|---|---|---|---|
| `pnueli1998translation` | Pnueli, Siegel & Singerman, *Translation Validation*, TACAS 1998 | the idea behind validating certificates against the source (Paper I `subsec:validation`, Paper II) | read |
| `necula2000translation` | Necula, *Translation Validation for an Optimizing Compiler*, PLDI 2000 | same, for a compiler | read |
| `joseph1986finding` | Joseph & Pandya, *Finding Response Times in a Real-Time System*, Comput. J. 1986 | the response-time equation (`thm:response-time`); Crossref lists only the first author | read |
| `audsley1993applying` | Audsley et al., *Applying New Scheduling Theory to Static Priority Pre-emptive Scheduling*, SEJ 1993 | response-time analysis | read |
| `graham1966bounds` | Graham, *Bounds for Certain Multiprocessing Anomalies*, BSTJ 1966 | greedy scheduling bound (`prop:graham`) | read |
| `cerqueira2016prosa` | Cerqueira, Stutz & Brandenburg, *PROSA*, ECRTS 2016 | the general mechanized schedulability theory (Coq), to contrast with our small model | read |


## Paper III (binaries)

| Key | Work | Role | Read |
|---|---|---|---|
| `li1995ilp` | Li & Malik, IPET, 1995 | the path analysis whose dual is the cycle certificate | read |
| `puschner1989calculating` | Puschner & Koza, 1989 | timing schema; markers and loop sequences (constraints on execution counts) | read |
| `maroneze2014formally` | Maroneze et al., 2014 | verified WCET in CompCert; IPET validated with a Farkas certificate in Coq | read (parts) |
| `sewell2016complete`, `sewell2017high` | Sewell, Kam & Heiser, 2016/2017 | loop bounds and infeasible paths of the seL4 binary, proved with SMT and C-level facts; CFG from a verified decompiler | read |
| `fox2010trustworthy` | Fox & Myreen, 2010 | ARM ISA model in HOL4, validated on hardware | read (parts) |
| `cullmann2007data` | Cullmann & Martin, 2007 | aiT's data-flow loop bounds on executables | read |
| `crary2000resource` | Crary & Weirich, 2000 | resource bounds of typed assembly, certified by typing | read |
| `granger1989static` | Granger, 1989 | congruence analysis; combined with intervals by rounding bounds to the class (Prop. 6.1) | read |
| `necula1997proof` | Necula, 1997 | proof-carrying code | read |
| `ballabriga2010otawa` | Ballabriga et al., OTAWA, 2010 | the WCET analyser compared on the binaries | — |
