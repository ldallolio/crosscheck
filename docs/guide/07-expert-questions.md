# Part 7 — Talking to experts: questions, answers, weak points, glossary

This part prepares you for seminars, reviews and conversations with specialists. The
answers are short on purpose: say them, then point to the paper section or the Lean
theorem. Where the honest answer is "this is a limitation", it says so — experts respect
precise limitations and distrust over-claims.

Contents

1. [The 60-second pitch](#1-the-60-second-pitch)
2. [Questions from a semantics / programming-languages expert](#2-semantics--programming-languages)
3. [Questions from a termination / bound-analysis expert](#3-termination--bound-analysis)
4. [Questions from a WCET / real-time expert](#4-wcet--real-time)
5. [Questions from a formal-methods / Lean expert](#5-formal-methods--lean)
6. [Questions from a C++ / compiler engineer](#6-c--compiler-engineering)
7. [Questions about AI use](#7-ai-use)
8. [Known weak points, ranked](#8-known-weak-points-ranked)
9. [Phrases to use and phrases to avoid](#9-phrases-to-use-and-phrases-to-avoid)
10. [Glossary](#10-glossary)

## 1. The 60-second pitch

> "A while loop executes the body until the guard fails. If you order execution traces by
> prefix, the executed trace is the *smallest* power of the body trace whose final state
> fails the guard — a minimisation problem. We prove, in Lean, that this minimisation is
> exactly the standard big-step semantics, and the same holds for linear and branching
> recursion with trees instead of traces. The minimiser gives the final state and the
> cost at the same time. Exact solutions exist only in decidable fragments, so we relax
> the problem: ranking potentials bound iteration counts, and costs combine with the
> timing-schema rules — sum, max, bound times body — which is the (max,+) semiring. All
> ingredients are classical; the contribution is a single formulation with a
> machine-checked link to the standard semantics, and a Clang plugin prototype that
> applies it to annotated C++ and fails the build when a cost budget may be exceeded."

## 2. Semantics / programming languages

**Q. Isn't "minimal exiting trace" just Kleene's μ-operator?**
Yes, and the paper says so (Positioning, remark after `thm:minimal-trace`). The point is
the reading in the trace order: the same minimiser minimises every monotone cost, and the
formulation extends unchanged to trees.

**Q. How does this relate to denotational semantics / least fixed points?**
Same chain, different element: denotational semantics takes the supremum of the Kleene
chain `ε ⊑ t ⊑ t² ⊑ …` (the meaning of the loop as a whole); CrossCheck takes, for one
initial state, the first element of the chain that exits (the executed run). See the
remark "Fixed-point reading". The paper does not develop the domain-theoretic side.

**Q. Your big-step semantics only covers terminating runs. What about divergence?**
Divergence = infeasibility of the minimisation (no `n̄`). We prove the negative statement
on the example (`infinite_loop_diverges`). For bounds, the cost logic of
`subsec:cost-logic` does cover it: the relation `c : s ↑ n` describes execution
*prefixes*, and a derivable bound holds for all of them, so a program with a derivable
bound and positive test weights cannot diverge. A coinductive big-step semantics (Leroy
& Grall) is not used.

**Q. Isn't your cost logic just a Hoare logic for time, which exists?**
Yes: Nielson 1987, and Haslbeck & Nipkow 2018 mechanised several in Isabelle. Say so
first. What is specific: the loop rule takes exactly what the tool computes (invariant,
rational potential decreasing by 1, context), atoms are relations (unknown inputs,
faults), and bounds hold for non-terminating executions. Its role is to connect the
tool's certificates to a program-level guarantee, not to be a new logic. Read both
papers before the talk (`\authortodo` in the paper).

**Q. Why traces of *instructions* rather than states?**
Because cost is intensional: it depends on the instructions executed, not only on the
states visited. The trace carries cost; the valuation `⟦t⟧` carries the state. That is
the "dual layer".

**Q. Is the trace order well-founded? Why does it matter?**
Yes (strict prefixes are shorter). It guarantees that "least" exists whenever a feasible
element exists — the trace analogue of the well-ordering of ℕ.

**Q. Your tree order — is it a known order?**
It is the prefix (or "substitution at leaves") order on finite trees, standard in term
rewriting and domain theory of trees; the paper only claims the properties it proves
(`prop:tree-order-properties`).

**Q. What is the expressiveness? Can you handle pointers, aliasing, mutual recursion,
concurrency?**
No (Limitations, "Language coverage"). The theory is for structured control flow over a
store; the plugin tracks only local integers whose address is never taken.

## 3. Termination / bound analysis

**Q. What is new compared with SPEED, KoAT, Loopus, COSTA, C4B?**
Not precision: those tools are more precise (amortisation, lexicographic and polynomial
bounds, size analysis). CrossCheck's difference is that the bound is derived inside a
semantics proved equivalent to big-step semantics, with machine-checked certificates, and
packaged as a compile-time real-time check. Say "we do not improve on their precision"
(Related Work says it).

**Q. Which ranking functions do you synthesise?**
Affine, one per loop (or per recursive function), over ℚ, by Farkas' Lemma and LP
(Colón–Sipma / Podelski–Rybalchenko), with Z3's optimiser minimising the entry bound.
Not lexicographic, not polynomial, no multiphase.

**Q. Integers vs rationals — is it sound?**
Sound: any rational potential satisfying the conditions on all rational points
satisfying the premises also satisfies them on integer points. Incomplete: integer-only
ranking functions can be missed (Ben-Amram & Genaim: coNP-complete over ℤ). Missing one
causes a rejection, never a wrong bound.

**Q. Where do the invariants come from?**
In the plugin: a small Houdini-style inference (candidates "only incremented ⇒ above the
entry value", "only decremented ⇒ below", and `a ≤ b` for a guard `a ≠ b`), each kept only
if Z3 proves it inductive; plus path conditions, parameter ranges and preconditions. No
abstract-interpretation domain. In the theory: assumed given ("established on an
inductive invariant").

**Q. Nested loops with dependent bounds (triangular loops)?**
Product of per-loop worst cases: `for i<n, for j<i` gets about `n·n` (outer bound times
the largest inner bound), not `n(n−1)/2`. No
amortisation. Amortised methods (Sinn et al., Hoffmann et al.) do better.

**Q. Your size potential — isn't that AARA?**
It is the potential method specialised to counting calls, with an affine potential found
by LP; the paper attributes it to the potential method / Hoffmann et al. It is much
weaker than AARA (no data structures, no size-dependent per-call cost).

**Q. Binary search?**
Linear depth bound (affine potentials cannot express `log`). Logarithmic bounds need
non-affine templates or a dedicated rule; on the roadmap.

## 4. WCET / real-time

**Q. Is this a WCET tool?**
No. It computes source-level cost bounds in abstract units: the loop-bound/flow and the
path-combination components. No micro-architectural analysis (caches, pipelines), no
analysis of the generated binary. "Cost is not time" (Limitations).

**Q. Can the weights be cycle counts?**
Only if each weight is a valid worst-case duration of the operation *in every context*,
which is false on processors with caches/pipelines, and the mapping from source
operations to machine code depends on the compiler. On simple in-order MCUs without
caches, per-operation bounds may be a reasonable approximation, but the paper makes no
such claim.

**Q. Why the timing schema and not IPET?**
The schema is compositional and matches the trace semantics directly. IPET is more
precise for infeasible-path constraints and is the industrial standard; CrossCheck's loop
bounds could feed an IPET tool. Expect this question; agree that IPET is more precise.

**Q. How pessimistic are the bounds?**
Tight on the paper's examples and on simple counted loops; pessimistic on data-dependent
branching (no infeasible-path pruning), nested dependent loops, and recursion with
size-dependent work (merge sort quadratic). On the TACLeBench kernels, in the calling
contexts reached from `main`, 128 of the 137 loop bounds derived equal the benchmark's
flow facts and 7 are larger; of the 126 bounds valid for every call, 100 are equal and
25 larger (Table `tab:tacle`).

**Q. Did you evaluate on Mälardalen / TACLeBench?**
On the 29 TACLeBench kernels, without annotations (`subsec:tacle`): 137 of 220 loops
bounded automatically in the program's calling contexts (126 for every call of their
function), 9 kernels bounded end to end. Always say which of the two kinds of bound a
figure is. Be ready for the follow-ups:
(1) *compared with what?* — with the benchmarks' flow facts (which hold for the fixed
input) and with three tools (`tab:tools`): LLVM's ScalarEvolution, KoAT2 and Infer. Know
the one-line result for each:
   - **ScalarEvolution** (the compiler's trip-count analysis): nearly the same loops as
     CrossCheck (103 in common, 99 identical bounds); it wins on float counters (it
     evaluates short constant loops exhaustively), CrossCheck wins where LLVM falls back
     to the range of `int` (`ludcmp`, `minver`).
   - **KoAT2** (state of the art in complexity analysis of integer programs): sound for
     the integer program, but llvm2kittel forgets memory, so many bounds are symbolic or
     missing; it handles `i*i <= n`, which we do not.
   - **CoFloCo** (cost equations, same integer programs as KoAT2): more numeric bounds
     than KoAT2 (128 vs 119) and never looser on the same program. Its entry-function
     bounds cover nearly the same kernels as ours: its limit is still llvm2kittel.
   - **Infer** (industrial, interprocedural): bounds the most functions thanks to
     context, but is not designed as a sound bound — it ignores recursion (constant cost
     for Fibonacci).
   - **Executions** (our instrumentation, run on the input): no bound of CrossCheck or
     ScalarEvolution is below an observed loop count. The flow facts are below it on
     two `while (1)`/`break` loops, by one: say they seem to count only iterations
     that return to the loop head, not that they are wrong. Expect "is your
     instrumentation right?": it agrees with the flow facts on 198 of 208 loops.
   - **oRange** (OTAWA's loop-bound analyser): analyses the whole program from `main`
     with its fixed input, like our in-context bounds: 131 loops against our 137, and
     identical bounds on all 113 loops both bound. It wins on float counters and
     globals; we win on its five failing kernels and on `sizeof` guards. It rejects
     recursion, and reports 1 for a `while (n-- > 0)` loop that runs twice
     (`filterbank`). Present that as an observation to be confirmed, not an attack.
   - **TPDB** (the complexity analysers' own benchmark): CrossCheck is clearly behind
     (165 programs with input ranges vs 288 for KoAT2). Say so first; then explain that
     it answers a different question (numeric bounds, no symbolic ones), and name what
     is missing (disjunctive and multi-phase potentials, facts across loops).
   If asked "why not SWEET / aiT?": aiT is commercial; check SWEET's availability
   before answering;
(2) *why do 83 loops fail?* — mostly bounds held in struct fields or globals, or in
parameters with no range even at the call (contexts are intervals of integer
arguments only), then float or `volatile` counters, then non-affine loops (binary search, `i*i <= n`, data-driven loops);
(3) *kernels are small* — yes; the sequential and application categories are next.

**Q. What about interrupts, preemption, multicore interference?**
Out of scope: the bound is for one function's sequential execution. Schedulability
analysis would consume such bounds.

**Q. Compared with Clang's `nonblocking` attributes / RTSan?**
They guarantee absence of blocking/allocating calls (statically or at run time); they do
not bound loops or recursion. The plugin's profile overlaps with them and adds bounds.

## 5. Formal methods / Lean

**Q. What exactly is machine-checked?**
The equivalences (minimisation ⇔ big-step) for while loops, linear recursion and binary
branching recursion; the orders and their properties; the cost identities; the ranking
bounds (integer, and relational over ordered fields); the soundness direction of Farkas;
the depth and size bounds for call trees of any arity; the examples; and, for a small
language with nondeterministic atoms, the soundness of a cost logic whose loop rule is
the plugin's certificate (`thm:cost-logic-soundness`), including symbolic bounds used as
function summaries. Table `tab:lean`.

**Q. What is not?**
`b > 2` for the tree order/powers/least execution tree; termination for
partial/nondeterministic updates (only run-length bounds); the equation-generation rules;
Farkas completeness; recursion inside the cost logic; the translation from C++ to the
language of the cost logic; the plugin and Z3 (`sec:mechanization`).

**Q. Any axioms or `sorry`?**
No `sorry`; no axioms beyond `propext`, `Quot.sound`, `Classical.choice` (`#print axioms`).

**Q. How do I know the Lean statements say what the paper says?**
That is the statement-fidelity question; Table `tab:lean` and `formalization.yaml` give
the correspondence, and Part 6 of this guide lists the modelling choices (binary trees,
total updates in `Ranking`, conditions over all continuing states, abstract valuation in
`exists_minimal_iteration`). The author has to compare them (`AI_USAGE.md` §3).

**Q. Why is the verified part not connected to the plugin?**
The plugin is C++; the Lean theorems justify each *kind* of certificate it emits, and
since November 2026 a cost logic (`Derivable`, module `Language`) says how they compose
over a program. Still missing: the plugin emitting a derivation, and a Lean-verified
checker for it. That is the planned next step; verifying the analyser itself (Blazy et
al.-style) is not planned.

**Q. Why Lean and not Coq/Isabelle?**
mathlib's order theory, arithmetic and automation (`omega`, `linarith`); a choice, not a
claim of superiority.

## 6. C++ / compiler engineering

**Q. Why a plugin and not a clang-tidy check or a static analyser?**
A plugin runs inside the compiler and turns a violation into a build error, which is the
desired real-time workflow; the same code also runs as a standalone libTooling tool.

**Q. Does it see templates, `constexpr`, lambdas?**
It analyses template *instantiations* reached from annotated functions; lambdas'
captures are costed; calls are followed into library code (which is why
`std::vector::push_back` is rejected — it reaches `operator new`).

**Q. What about undefined behaviour?**
Signed overflow is assumed absent (it is UB); unsigned wrap is handled; a bound holds
under "no UB" — stated in the soundness sentence.

**Q. Analysis before optimisation — does the optimiser invalidate the bound?**
The bound is on the source program's abstract operations. Optimisations change machine
code, not the source semantics, so the *count* of source operations is unchanged, but its
relation to time is not preserved. That is again "cost is not time".

**Q. Clang version?**
Built and tested against Clang 18 (LLVM plugin ABI is version-specific).

## 7. AI use

**Q. Which parts were written by an AI?**
As stated in the paper's AI statement and `AI_USAGE.md`: the AI restructured the paper,
wrote the Lean modules `WhileLoop`, `Ranking`, `Recursion`, `Certificate`, `Arity` and
extensions, compiled the bibliography, proposed the simplifications, and wrote the plugin,
its tests and examples. The framework, examples and original manuscript are yours.
Be precise and do not minimise it: AGMAI asks for exactly this disclosure.

**Q. How do you know the AI's mathematics is right?**
Everything in Lean is kernel-checked; the non-mechanised parts and the
statement-fidelity question require your personal verification (the `[AUTHOR TO
CONFIRM]` marker stays until you have done it).

## 8. Known weak points, ranked

1. **Thin evaluation** (most likely referee criticism): TACLeBench kernels only (small
   programs), no dedicated WCET flow-analysis tool in the comparison, no annotations.
2. **Novelty is in packaging**, not in individual results — must be argued well.
3. **Plugin unverified**, Z3 models not re-checked; the trusted base is large.
4. **Precision**: no amortisation, affine potentials only, timing schema without
   infeasible-path pruning.
5. **Cost is not time**: a WCET audience will want a path to cycles.
6. **Mechanisation gaps**: binary tree order, invariant-relative ranking, no link from
   C++ to the Lean model.
7. **Exact layer** (equation generation) is described informally and not mechanised; the
   claim that the example systems are "produced by a prototype" must be checked
   (`AI_USAGE.md` §3 item 3/8).
8. **Bibliography content** of recent references not yet read by the author.

## 9. Phrases to use and phrases to avoid

| Prefer | Avoid |
|---|---|
| "sound upper bound under the listed assumptions" | "guaranteed WCET" |
| "cost bound in abstract units" | "execution time" |
| "machine-checked in Lean, no axioms beyond the three standard ones" | "fully verified", "zero axioms" |
| "the timing schema, read in the (max,+) semiring" | "our tropical algebra of control flow" (as if new) |
| "research prototype; on the TACLeBench kernels, close to LLVM's trip counts, sound where Infer is not" | "the tool scales to real code" |
| "affine ranking potentials synthesised by Farkas/LP (standard method)" | "our synthesis method" |
| "the plugin's certificates are justified by Lean theorems" | "the plugin is verified" |
| "uniform formulation of known ingredients" | "novel framework" without qualification |

## 10. Glossary

| Term | Meaning (one line) | Where |
|---|---|---|
| **Abstract interpretation** | static analysis computing over-approximations as fixed points in abstract domains | Part 1 §11 |
| **Acceleration** | closed form of the `n`-fold iteration of a loop body | Part 1 §17 |
| **Activation** | one execution of a function call (one node of the call tree) | plugin |
| **Affine** | linear plus a constant: `w·x + c` | |
| **Amortised analysis** | bounds the total cost of a sequence via potentials | Part 1 §16 |
| **AST** | abstract syntax tree (Clang's program representation) | Part 4 §2 |
| **Big-step / natural semantics** | relation initial state ⇓ final state defined by inference rules | Part 1 §6 |
| **Bottom (⊥)** | the undefined/fault outcome; `none` in Lean | Part 1 §2 |
| **Catamorphism** | bottom-up fold over a tree | Part 1 §5 |
| **Certificate** | data (potential, multipliers) that proves a bound and can be re-checked | Part 4 §9 |
| **Coinduction** | reasoning about possibly infinite objects (dual of induction) | Leroy & Grall |
| **Cost envelope** | the paper's term for a sound upper bound on cost | Part 2 §6.2 |
| **Cost norm** | function from traces to ℕ, subadditive; weighted cost | `def:subadditive-norm` |
| **Decidable** | solvable by an always-terminating algorithm | Part 1 §10 |
| **Depth potential** | ℕ-valued function decreasing at every recursive call; bounds depth | `prop:tree-envelope` |
| **Derivation** | finite tree of inference-rule applications | Part 1 §6 |
| **Dual-layer semantics** | intensional (trace/cost) + extensional (state) together | Part 1 §7 |
| **Entailment** | facts ⊨ goal: every assignment satisfying the facts satisfies the goal | plugin |
| **Extensional** | only input/output behaviour counts | Part 1 §7 |
| **Farkas' Lemma** | linear implication ⇔ non-negative combination of premises | Part 1 §18 |
| **Free monoid Σ\*** | finite words with concatenation, no extra equations | Part 1 §4 |
| **Grafting (⊗)** | substituting a tree at every leaf | Part 1 §5 |
| **Havoc** | replace a variable's value by a fresh unknown | Part 4 §6 |
| **Houdini** | invariant inference by iteratively dropping non-inductive candidates | Part 1 §15 |
| **Inductive invariant** | holds initially and is preserved by each iteration | Part 1 §15 |
| **Intensional** | how the result is computed (steps, cost) counts | Part 1 §7 |
| **IPET** | WCET path analysis as an integer linear program | Part 1 §12 |
| **Kernel (Lean)** | small trusted checker of proof terms | Part 1 §21 |
| **Kleene chain** | `⊥ ⊑ F(⊥) ⊑ F²(⊥) ⊑ …` whose limit is the least fixed point | Part 1 §8 |
| **LP** | linear programming | Part 1 §18 |
| **mathlib** | Lean's mathematics library | Part 5 §9 |
| **μ-operator** | least `n` satisfying a predicate | Part 1 §9 |
| **Order-by-composition (⊑)** | prefix order on traces (and its tree analogue) | `def:order-by-composition` |
| **Path selector τ** | state ↦ trace emitted by one body execution | `def:path-selector` |
| **Pointed domain S⊥** | states plus ⊥ | `def:state-transition` |
| **Potential method** | amortisation via a potential function | Part 1 §16 |
| **Presburger arithmetic** | integer arithmetic without variable multiplication; decidable | Part 1 §10 |
| **Ranking potential / function** | quantity decreasing by ≥ Δ per iteration, positive while looping | Part 1 §14 |
| **Relational ranking** | ranking conditions over a transition relation (nondeterminism) | `ranking_bound_floor` |
| **Size potential** | `U(x) ≥ 1 + Σ U(children)`; bounds number of calls | `prop:size-potential` |
| **SMT** | satisfiability modulo theories (Z3) | Part 1 §19 |
| **Sound / complete / tight** | never under-estimates / always finds a bound / close to the truth | Part 1 §20 |
| **Statement fidelity** | whether a Lean statement says what the paper's statement says | Part 6 |
| **Strict function** | maps ⊥ to ⊥ | Part 1 §2 |
| **Symbol (plugin)** | immutable unknown integer; variables map to affine expressions over symbols | Part 4 §6 |
| **Tactic** | Lean command that builds part of a proof | Part 5 §7 |
| **Timing schema** | sum / max / bound × body rules (Shaw; Puschner & Koza) | Part 1 §12 |
| **Tree order (⊑_tree)** | `T₂` obtained from `T₁` by substituting trees at leaves | `def:tree-order` |
| **Tropical (max,+) semiring** | ⊕ = max, ⊗ = +; algebra of worst-case cost | Part 1 §13 |
| **Valuation ⟦·⟧** | meaning of a trace as a state transformer | `def:trace-functional` |
| **WCET / BCET** | worst-/best-case execution time | Part 1 §12 |
| **Well-founded** | no infinite strictly decreasing chain | Part 1 §3 |
| **Widening** | operator forcing abstract fixed-point iteration to terminate | Part 1 §11 |
