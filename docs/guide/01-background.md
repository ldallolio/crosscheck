# Part 1 — Background concepts, from zero

This part explains the ideas the paper *uses* without defining them, because a
specialist reader is supposed to know them. Each section has the same shape:
an intuition for a software engineer, the precise definition, where CrossCheck uses
it, and the vocabulary experts use.

Contents

1. [Sets, functions, relations — the minimum notation](#1-sets-functions-relations--the-minimum-notation)
2. [Partial functions and the bottom element ⊥](#2-partial-functions-and-the-bottom-element-)
3. [Orders: partial orders, well-foundedness, least elements](#3-orders-partial-orders-well-foundedness-least-elements)
4. [Monoids, free monoids, homomorphisms](#4-monoids-free-monoids-homomorphisms)
5. [Trees, term algebras, catamorphisms](#5-trees-term-algebras-catamorphisms)
6. [Semantics of programs: operational, denotational, big-step](#6-semantics-of-programs-operational-denotational-big-step)
7. [Intensional versus extensional](#7-intensional-versus-extensional)
8. [Fixed points, the Y combinator and Kleene chains (the Manna connection)](#8-fixed-points-the-y-combinator-and-kleene-chains-the-manna-connection)
9. [Kleene's μ-operator and the well-ordering principle](#9-kleenes-μ-operator-and-the-well-ordering-principle)
10. [Decidability: halting problem, Presburger, Hilbert's 10th problem](#10-decidability-halting-problem-presburger-hilberts-10th-problem)
11. [Static analysis landscape: abstract interpretation, symbolic execution, model checking](#11-static-analysis-landscape)
12. [WCET analysis: what the real-time community does](#12-wcet-analysis-what-the-real-time-community-does)
13. [Semirings and the tropical (max,+) semiring](#13-semirings-and-the-tropical-max-semiring)
14. [Ranking functions and the Lyapunov analogy](#14-ranking-functions-and-the-lyapunov-analogy)
15. [Invariants and inductive invariants](#15-invariants-and-inductive-invariants)
16. [Amortised analysis and the potential method](#16-amortised-analysis-and-the-potential-method)
17. [Recurrences, closed forms, acceleration, the Master Theorem](#17-recurrences-closed-forms-acceleration-the-master-theorem)
18. [Linear programming and Farkas' Lemma](#18-linear-programming-and-farkas-lemma)
19. [SAT, SMT and Z3](#19-sat-smt-and-z3)
20. [Soundness, completeness, precision](#20-soundness-completeness-precision)
21. [Proof assistants, Lean, mathlib, axioms](#21-proof-assistants-lean-mathlib-axioms)
22. [Things with similar names that CrossCheck is *not*](#22-things-with-similar-names-that-crosscheck-is-not)

---

## 1. Sets, functions, relations — the minimum notation

| Notation | Read as | C++ intuition |
|---|---|---|
| `ℕ` | natural numbers 0, 1, 2, … | `std::size_t` without overflow |
| `ℤ` | integers | `long long` without overflow |
| `ℚ` | rationals `p/q` | exact fractions |
| `𝔹` | booleans `{true, false}` | `bool` |
| `A × B` | pairs | `std::pair<A,B>` |
| `A → B` | (total) functions | a pure function defined on *every* input |
| `A ⇀ B` | partial functions | a function that may be undefined on some inputs |
| `f ∘ g` | composition: first `g`, then `f` | `f(g(x))` |
| `f^n` | `f` applied `n` times (`f^0 = id`) | a `for` loop calling `f` |
| `∀ x, P x` | for all | |
| `∃ x, P x` | there exists | |
| `P ⟹ Q`, `P ↔ Q` | implies, if and only if | |
| `{x ∈ A ∣ P x}` | the subset of `A` where `P` holds | `std::views::filter` |
| `min N` | least element of a set of naturals | |
| `⌈x⌉`, `⌊x⌋` | ceiling, floor | `std::ceil`, `std::floor` |

A **relation** `R ⊆ A × B` is just a set of pairs: "`a` is related to `b`". A function
is a relation where every `a` has exactly one partner; a *partial* function is a
relation where every `a` has **at most** one partner (this is how the paper defines
a partial state transition, `def:state-transition`).

**Inductive definitions.** "The least set closed under these rules" means: the set
of things you can build by applying the rules a finite number of times, and nothing
else. Natural numbers are the least set containing `0` and closed under `n ↦ n+1`;
lists are the least set containing `[]` and closed under "add an element in front".
Proofs about inductively defined things go by **induction** on how they were built.
This one idea underlies the big-step semantics, trees, and almost every Lean proof
in the repository.

## 2. Partial functions and the bottom element ⊥

A program fragment may *fail*: division by zero, out-of-bounds access, assertion
failure. Mathematically the fragment is a **partial function** `f : S ⇀ S` on
states: undefined on states where it fails.

Partial functions are awkward to compose (you must track domains), so the classical
trick is to add one extra value `⊥` ("bottom", "undefined") and make everything
total:

- `S⊥ = S ∪ {⊥}` is the **pointed** (or **lifted**) state space;
- `f⊥ : S⊥ → S⊥` is `f` where defined, `⊥` elsewhere, and `f⊥(⊥) = ⊥`.

The last equation says `f⊥` is **strict**: once you have failed, you stay failed.

C++ intuition: `std::optional<State>` with `and_then`. `std::nullopt` is ⊥, and
`opt.and_then(f)` is exactly `f⊥`. Lean uses the same encoding: `Option S`, with
`none` for ⊥ (module `State`).

In the paper, ⊥ means a **fault**. Non-termination is *not* represented by ⊥ in
the paper's state space: a diverging loop simply has no minimal exit (no `n̄`
exists). In classical domain theory (Scott, Winskel, Manna) ⊥ usually means
"no information yet / does not terminate"; be ready to say that the paper uses ⊥
for faults and treats divergence separately.

## 3. Orders: partial orders, well-foundedness, least elements

A **partial order** `≤` on a set is a relation that is

- *reflexive*: `x ≤ x`;
- *transitive*: `x ≤ y` and `y ≤ z` give `x ≤ z`;
- *antisymmetric*: `x ≤ y` and `y ≤ x` give `x = y`.

"Partial" because two elements may be incomparable (neither `x ≤ y` nor `y ≤ x`).
Examples: `≤` on numbers (total order), `⊆` on sets (partial), "is a prefix of" on
strings (partial: `"ab"` and `"ba"` are incomparable).

A **preorder** is reflexive and transitive but not necessarily antisymmetric
(e.g. "`f` grows at most as fast as `g`", big-O, where `n` and `2n` are each below
the other but are different).

Vocabulary:

- **Least element** of a set `X`: an element of `X` below *every* element of `X`.
  It is unique if it exists (antisymmetry).
- **Minimal element**: nothing in `X` is strictly below it. In a total order,
  minimal = least; in a partial order there can be several minimal elements and
  no least one. The paper always proves *least*, which is stronger.
- **Chain**: a set of pairwise comparable elements, e.g. `ε ⊑ t ⊑ t² ⊑ …`.
- **Monotone function**: `x ≤ y ⟹ f x ≤ f y`. The paper's key property is that
  *cost is monotone* along the order-by-composition.
- **Order isomorphism**: a bijection that preserves and reflects the order.
  `n ↦ tⁿ` is one between `(ℕ, ≤)` and the chain of powers of `t` (`prop:n-monotony`).
- **Well-founded order**: there is no infinite strictly decreasing chain
  `x₀ > x₁ > x₂ > …`. Equivalently, every non-empty subset has a minimal element.
  `(ℕ, ≤)` is well-founded; `(ℤ, ≤)` is not (…, −2, −1, 0). Well-foundedness is
  *the* tool for termination proofs: if each loop iteration moves strictly down in a
  well-founded order, the loop stops.

Expert phrasing: "the prefix order on Σ* is a well-founded partial order with
bottom ε, and cost is a monotone map into (ℕ, ≤)".

## 4. Monoids, free monoids, homomorphisms

A **monoid** is a set with an associative operation `·` and a neutral element `e`:
`(a·b)·c = a·(b·c)` and `e·a = a·e = a`. Examples:

| Set | Operation | Neutral |
|---|---|---|
| ℕ | `+` | 0 |
| ℕ | `max` | 0 |
| strings | concatenation | `""` |
| functions `S → S` | composition | identity |

The **free monoid** `Σ*` over an alphabet `Σ` is the set of finite words (lists)
over `Σ` with concatenation. "Free" means: no equations hold except those forced by
the monoid laws — `ab ≠ ba`, `aa ≠ a`, etc. In C++ terms, `Σ*` is
`std::vector<Instr>` with `insert(end, …)` as the operation.

A **homomorphism** `h : M → N` between monoids preserves the structure:
`h(x·y) = h(x)·h(y)` and `h(e) = e`. Example: `length : Σ* → (ℕ, +)` is a
homomorphism, `length(uv) = length(u) + length(v)`.

The **universal property** of the free monoid ("freeness") says: to define a
homomorphism from `Σ*` you only need to say where each *letter* goes; the value on
words is then forced. The paper uses it twice:

- the **valuation** `⟦·⟧` (meaning of a trace) is defined by giving `⟦a⟧ = I(a)⊥`
  for each instruction `a`; the meaning of a word is then the composition of the
  meanings of its letters (`def:trace-functional`);
- the **weighted cost** is defined by giving a weight `ω(a)` to each letter; the
  cost of a word is the sum (`def:subadditive-norm`).

A subtlety you may be asked about: `⟦t₁·t₂⟧ = ⟦t₂⟧ ∘ ⟦t₁⟧` — the order is reversed
because composition `∘` applies right-to-left while traces are read left-to-right.
The paper says it is a homomorphism "under reverse composition"; experts call it an
*anti-homomorphism* into `(S⊥ → S⊥, ∘)` or a homomorphism into the *opposite* monoid.

## 5. Trees, term algebras, catamorphisms

A **term algebra** `T_Σ` over a signature (a set of constructors with arities) is
the set of all finite trees built from the constructors — again "free": two terms
are equal only if they are syntactically identical. For CrossCheck the signature is
"a leaf ε (arity 0)" and "a node g with b children (arity b)", so `T_Σ` is the set
of finite b-ary tree shapes. In C++ this is

```cpp
struct Tree { std::vector<std::unique_ptr<Tree>> children; };  // leaf = no children
```

Vocabulary used by the paper:

- **size** (cost): number of nodes, leaves included;
- **leaves**: number of leaf nodes; **depth**/**height**: longest root-to-leaf path
  (a single leaf has depth 0);
- **full b-ary tree** `F_d`: every internal node has b children, all leaves at depth d;
  it has `1 + b + … + b^d = (b^{d+1}−1)/(b−1)` nodes;
- **grafting** (substitution): replace leaves by trees. Uniform grafting `T₁ ⊗ T₂`
  puts the same `T₂` on every leaf; general leaf substitution may put different
  trees on different leaves;
- **catamorphism** (a "fold"): compute a value bottom-up by giving one function
  for leaves and one for nodes. `std::accumulate` is the list version. The value
  returned by a recursive function is a catamorphism over its call tree.

Expert phrasing: "computation trees are the initial algebra of the signature; the
result of the recursive function is the unique homomorphism (catamorphism) from it
into the algebra of results."

## 6. Semantics of programs: operational, denotational, big-step

"Semantics" = a mathematical definition of what a program *means*, so that one can
*prove* things about programs. Three classical styles:

| Style | Meaning of a program is… | Typical notation | Reference in the paper |
|---|---|---|---|
| **Small-step operational** (Plotkin, "structural operational semantics") | a transition system: one step at a time, `⟨c, s⟩ → ⟨c', s'⟩` | `→` | not used |
| **Big-step operational** / **natural semantics** (Kahn) | a relation between initial and final state, `⟨c, s⟩ ⇓ s'`, defined by inference rules | `⇓` | `eq:bigstep-while`, cites Kahn, Winskel |
| **Denotational** (Scott, Strachey) | a mathematical object, typically a function `⟦c⟧ : S → S⊥`, defined compositionally; loops via least fixed points | `⟦c⟧` | the valuation `⟦t⟧` of traces |
| **Axiomatic** (Floyd, Hoare) | the set of provable specifications `{P} c {Q}` | Hoare triples | Floyd is cited for ranking functions |

**Inference rules.** A rule

```
  premise₁   premise₂
  ───────────────────
      conclusion
```

says "if the premises hold, the conclusion holds". The big-step relation of a
`while` loop in the paper is the *least* relation closed under two rules: exit
(`P(s)` false ⟹ `s ⇓ s`) and step (`P(s)` true, body takes `s` to `s'`, `s' ⇓ s''` ⟹
`s ⇓ s''`). A **derivation** is a finite tree of rule applications ending in the
judgment; `s ⇓ s''` holds iff a derivation exists. Since derivations are finite,
big-step semantics only talks about **terminating** runs — a diverging loop has no
derivation (which is why Leroy & Grall introduced *coinductive* big-step semantics,
which allows infinite derivations).

C++ intuition: big-step semantics is a recursive interpreter
`State run(Stmt, State)`; the relation holds when the interpreter returns.

Why the paper insists on it: the CrossCheck claim "solving the minimisation problem
is the same as running the loop" is only meaningful relative to an accepted
definition of "running the loop". Big-step semantics is that accepted definition;
`thm:extensional-equivalence` proves the equivalence. In Lean the rules become an
`inductive` predicate (`WhileBigStep`).

## 7. Intensional versus extensional

These two words come from logic and philosophy and are central to the paper's
vocabulary.

- **Extensional**: only the input/output behaviour counts. Two programs are
  extensionally equal if they compute the same function. `x*2` and `x+x` are
  extensionally equal.
- **Intensional**: *how* the result is computed counts — the steps, the trace, the
  cost. `x*2` and `x+x` are intensionally different (different instructions).

CrossCheck's **dual-layer** semantics carries both at once:

- intensional layer: the trace `t ∈ Σ*` (or the computation tree), its order `⊑`,
  its cost;
- extensional layer: the state transformation `⟦t⟧`, the final state, the
  recurrence equations.

Cost is an intensional property (bubble sort and merge sort are extensionally
equal), which is why a semantics that only tracks states cannot talk about WCET.
Experts in "intensional semantics" / "cost semantics" will recognise the idea:
cost-instrumented semantics, where each evaluation step also produces a cost.

## 8. Fixed points, the Y combinator and Kleene chains (the Manna connection)

You read Manna, so this is the part of the paper closest to your background.

**Fixed point**: `x` with `F(x) = x`. A **least fixed point** `lfp F` is a fixed
point below all others in some order.

**Why loops are fixed points.** The loop `while (c) body` is the function `W`
satisfying the unfolding equation

```
W(s) = if c(s) then W(body(s)) else s
```

i.e. `W` is a fixed point of the functional `F(w) = λs. if c(s) then w(body(s)) else s`.
In the λ-calculus this is written `while = Y F` with the fixed-point combinator `Y`
(`Y F = F (Y F)`); the paper recalls this form in Section "Loops and Recursion as
Optimization Problems", citing Manna.

**Kleene's fixed-point theorem.** If `F` is monotone and *continuous* on a complete
partial order (cpo) with bottom ⊥, then `lfp F = sup { ⊥, F(⊥), F(F(⊥)), … }`. The
sequence `⊥ ⊑ F(⊥) ⊑ F²(⊥) ⊑ …` is the **Kleene chain**. For a loop, `Fⁿ(⊥)` is the
loop "unrolled n times and undefined beyond", and the limit is the loop's meaning.
Manna's book develops exactly this theory (with "Kleene's first recursion theorem"
and computational induction).

**CrossCheck's version.** The paper observes (remark "Fixed-point reading") that on
traces, `ε ⊑ t ⊑ t² ⊑ …` is the Kleene chain of the unrolling operator `x ↦ t·x` on
finite and infinite words ordered by prefix; its supremum is the infinite word
`t^ω`. An executed loop is a finite prefix `t^n̄` of it; a diverging loop "emits all
of it". The paper does **not** build on this (the cpo of infinite words was removed in
the November 2026 simplification); it only uses the finite chain and well-ordering.

The difference to stress with experts: classical denotational semantics gets the
loop's meaning as a *supremum* (limit of approximations); CrossCheck gets the
executed trace as a *minimum* (first element of the chain that exits). Both use the
same chain; CrossCheck exploits that, for a single run, the relevant element is
found at a finite position.

## 9. Kleene's μ-operator and the well-ordering principle

**Well-ordering principle**: every non-empty set of natural numbers has a least
element. It is equivalent to induction on ℕ.

**μ-operator** (minimisation, Kleene 1936): given a predicate `P(n)`,
`μn. P(n)` = the least `n` with `P(n)`, if one exists (undefined otherwise). Adding
μ to primitive recursion gives all computable (partial recursive) functions; μ is
"the" source of partiality and non-termination in computability theory — it is a
`while` loop in disguise:

```cpp
unsigned n = 0; while (!P(n)) ++n; return n;   // μn. P(n)
```

The paper's `n̄ = min{ n ∣ ⟦tⁿ⟧(s₀) exits }` is literally μ. The `Positioning`
subsection says so explicitly: the minimisation itself is classical; what is new is
reading it in the trace order and coupling it with cost. In Lean, μ is `Nat.find`
(which needs a proof that some `n` exists — Lean functions must be total).

## 10. Decidability: halting problem, Presburger, Hilbert's 10th problem

A problem is **decidable** if some algorithm answers every instance correctly and
always terminates.

- **Halting problem** (Turing 1936): "does this program terminate on this input?"
  is undecidable. Consequently, computing the exact terminal state or exact
  iteration count of arbitrary loops is impossible in general (**Rice's theorem**
  extends this to every non-trivial behavioural property).
- **Presburger arithmetic**: first-order logic over integers with `+`, `<`,
  constants, but *no multiplication of variables*. It is **decidable** (Presburger
  1929), though with very high worst-case complexity. Loops whose updates are
  translations `x := x + c` with linear guards produce Presburger formulas
  (`n·c` is multiplication by a constant, allowed). That is the paper's decidable
  fragment.
- **Hilbert's 10th problem**: "does this polynomial equation with integer
  coefficients have an integer solution?" Matiyasevich (1970), completing work of
  Davis, Putnam and Robinson, proved it **undecidable** ("MRDP theorem": every
  recursively enumerable set is Diophantine). The paper uses this to say that
  even loops with *polynomial* integer updates have undecidable exit problems.

Why it matters: it justifies the **relaxation** strategy — give up exact answers
and compute sound *upper bounds* that are always computable (or fail safely).

## 11. Static analysis landscape

Three families mentioned in the Introduction:

- **Abstract interpretation** (Cousot & Cousot 1977): compute, for each program
  point, an over-approximation of the reachable states in an *abstract domain*
  (intervals `x ∈ [0, 10]`, octagons `±x ± y ≤ c`, polyhedra). Loops are handled by
  iterating to a fixed point; to force termination on infinite-height domains one
  uses **widening** (jump to a coarser value, e.g. `[0,1],[0,2],… ↦ [0,+∞)`), which
  loses precision. Industrial tools: Astrée, Frama-C/EVA, Polyspace. AbsInt's aiT
  WCET tool is built on abstract interpretation.
- **Symbolic execution**: run the program on symbolic inputs, forking at branches,
  collecting path conditions (KLEE). Path explosion: `2^n` paths after n branches.
- **(Bounded) model checking**: explore the state space (exhaustively, or up to a
  depth bound by unrolling loops k times, CBMC). Loops are unrolled, which is what
  CrossCheck avoids.

CrossCheck's plugin is closest to a *symbolic execution with joins* plus *invariant
inference* plus *ranking-function synthesis* — the standard architecture of
academic bound analysers (see Part 3: SPEED, KoAT, Loopus).

## 12. WCET analysis: what the real-time community does

**WCET** (worst-case execution time): the maximum execution time of a task over all
inputs and all hardware states. Needed for schedulability analysis (e.g. rate
monotonic: `Σ Cᵢ/Tᵢ ≤ bound`). Since the exact WCET is uncomputable, tools compute a
**safe upper bound** (never below the true WCET) that is as **tight** as possible.
The **BCET** is the best case.

Classical tool architecture (Wilhelm et al. 2008 survey), on the *binary*:

1. **Flow analysis**: reconstruct the control-flow graph, find **loop bounds**
   (from annotations or a bound analysis) and infeasible paths.
2. **Micro-architectural / low-level analysis**: cache analysis (always-hit /
   always-miss classification by abstract interpretation), pipeline analysis →
   a time bound for each basic block.
3. **Path analysis / bound calculation**: combine block times and loop bounds into
   the global bound. Two techniques:
   - **timing schema** / tree-based (Shaw 1989; Puschner & Koza 1989): recursive
     rules on the syntax tree — sequence = sum, `if` = condition + max of branches,
     loop = bound × body. Simple, compositional, may be pessimistic;
   - **IPET** (Implicit Path Enumeration Technique, Li & Malik 1995): an integer
     linear program whose variables are execution counts of CFG edges, constrained
     by flow conservation and loop bounds, maximising `Σ count × time`.

**Measurement-based** and **hybrid** approaches exist too (run on hardware, take the
high-water mark plus margin) — common in industry, not safe in the strict sense.

**Where CrossCheck sits**: it contributes to step 1 (loop and recursion bounds, by
ranking potentials) and step 3 (timing-schema combination), at source level and
with an abstract cost unit instead of cycles. It does not do step 2. Say this
plainly; WCET experts will check it immediately. The paper's `Limitations` section
("Cost is not time") says exactly this.

Industrial tools you may hear about: AbsInt **aiT** (static, abstract
interpretation), **OTAWA** (academic, static), **SWEET** (flow analysis, Mälardalen),
**RapiTime** (hybrid, measurement-based), **Bound-T**, **Heptane**. Standard benchmark
suites: **Mälardalen WCET benchmarks**, **TACLeBench**.

## 13. Semirings and the tropical (max,+) semiring

A **semiring** has two operations, ⊕ ("addition") and ⊗ ("multiplication"), with
⊕ associative, commutative, neutral element **0**; ⊗ associative with neutral
element **1**; ⊗ distributes over ⊕; **0** absorbs for ⊗. No subtraction needed.

The **(max,+) semiring** (one of the "tropical" semirings): ⊕ = `max`, ⊗ = `+`,
**0** = `−∞`, **1** = `0`. Check distributivity: `a + max(b, c) = max(a+b, a+c)`. ✓

Why it fits worst-case cost:

- doing `A` then `B`: costs add → ⊗;
- doing `A` or `B` (a branch): the worst case is the larger → ⊕;
- distributivity: "`A` then (`B` or `C`)" has the same worst case as
  "(`A` then `B`) or (`A` then `C`)" — you can push choices inward or outward.

The longest path in a DAG, the critical path in project planning, and the cycle
time of synchronous systems (Baccelli et al., *Synchronization and Linearity*) are
all (max,+) computations. "Idempotent" means `a ⊕ a = a` (`max(a,a) = a`).

In the paper (`subsubsec:tropical-semiring`, `prop:tropical-collapse`) this is a
*reading* of the timing schema, not a new technique; the paper credits Shaw and
Puschner & Koza for the rules and Baccelli et al. for the algebra.

## 14. Ranking functions and the Lyapunov analogy

**Ranking function** (Floyd 1967, "Assigning meanings to programs"): a map `V` from
states into a well-founded set (classically ℕ) that strictly decreases at every
loop iteration. Since there is no infinite decreasing sequence in ℕ, the loop
terminates. Example: for `for (i = 0; i < n; ++i)`, `V = n − i`.

**Quantitative version** (used for bounds): if `V` decreases by at least `Δ > 0` per
iteration and must be `> 0` to continue, the loop runs at most `⌈V(s₀)/Δ⌉` times.
This is `thm:lyapunov-bound`.

**Lyapunov analogy** (you know it from robotics/control): a Lyapunov function
`V(x) ≥ 0` with `V̇ < 0` along trajectories proves convergence to equilibrium. A
ranking function is the discrete-time, "finite-time" analogue: `V(x_{k+1}) ≤ V(x_k) − Δ`
proves the trajectory leaves the region `{V > 0}` (the loop guard) within
`V(x₀)/Δ` steps — like a Lyapunov function with a strict *rate* that gives a
finite-time convergence bound. The paper's name "Lyapunov Cost Dominance Bound" uses
this analogy; experts in termination call it simply a "linear ranking function with
a bound".

**Variants experts will mention**:

- **Linear (affine) ranking functions** `V(x) = w·x + c`: synthesisable by LP
  (Colón & Sipma; Podelski & Rybalchenko). CrossCheck uses these.
- **Lexicographic ranking functions** `(V₁, V₂)`: decrease lexicographically; needed
  for loops like `while (x > 0) { if (y > 0) y--; else { x--; y = N; } }`
  (Alias, Darte, Feautrier, Gonnord — "multi-dimensional rankings").
- **Polynomial / non-linear** ranking functions.
- **Disjunctive well-foundedness / transition invariants** (Podelski & Rybalchenko
  2004): instead of one ranking function, a finite union of well-founded relations
  covering the transitive closure of the loop — the theory behind Terminator.
- **Multiphase ranking functions** (Ben-Amram & Genaim, later work).

**Relational variant.** A loop body need not be a function: with unknown inputs
(sensor values) the next state is not determined. Then the body is a **transition
relation** `s → s'`, and the conditions must hold for *every* possible successor.
CrossCheck's plugin uses this form (`ranking_bound_floor`).

## 15. Invariants and inductive invariants

An **invariant** of a loop is a property true at the loop head on every iteration.
An **inductive invariant** is one you can *prove* locally: it holds on entry
(base case), and if it holds before an iteration it holds after (inductive step).
Every inductive invariant is an invariant; not every true invariant is inductive
(it may need strengthening).

Ranking functions usually need invariants: `V = n − i` is positive only if one knows
`i < n` (the guard) — fine — but in `while (i != n) i++` one needs the invariant
`i ≤ n` to turn `i ≠ n` into `i < n`. The plugin infers such facts by a
**Houdini**-style loop (Flanagan & Leino 2001, not cited in the paper): propose
candidate invariants, check each for inductiveness with the solver, drop those that
fail, repeat until stable. The result is the largest inductive subset of the
candidates.

## 16. Amortised analysis and the potential method

Amortised analysis (Tarjan 1985; textbook: Cormen et al.) bounds the *total* cost of
a sequence of operations even when single operations can be expensive. In the
**potential method**, you define a potential `Φ ≥ 0` of the data structure; each
operation's amortised cost is `actual + ΔΦ`; the sum of amortised costs bounds the
sum of actual costs. Example: `std::vector::push_back` is amortised O(1) with
`Φ = 2·size − capacity`.

**AARA** (Automatic Amortized Resource Analysis — Hofmann & Jost 2003, Hoffmann et
al.) infers potentials automatically by type inference + LP, for functional and
imperative programs.

CrossCheck's **size potential** (`prop:size-potential`) is the potential method
specialised to counting calls: `U(x) ≥ 1 + Σ U(children)` means each activation
"pays 1" from its potential and passes the rest to its children; so the total
number of activations is at most `U(x)`. For a recursive split of a range of length
`m` into two non-empty halves, `U = 2m − 1` works (a binary tree with `m` leaves has
`2m − 1` nodes) — linear, whereas the depth argument gives `2^m`.

Merge sort's `O(n log n)` needs more: charging each activation a *size-dependent*
cost (the merge is linear in the range) and summing per level. CrossCheck charges
every activation the worst-case merge, hence its quadratic bound. Experts will
recognise "no amortisation" immediately.

## 17. Recurrences, closed forms, acceleration, the Master Theorem

- A **recurrence** defines a sequence by its previous values: `x_{k+1} = x_k + 2`.
  A **closed form** gives `x_k` directly: `x_k = x_0 + 2k`.
- **C-finite / linear recurrences** with constant coefficients always have closed
  forms (sums of exponential-polynomials); this is what Kincaid et al. exploit.
- **Loop acceleration**: compute the effect of `n` iterations as a formula in `n`
  (the closed form of the iterated body), turning a loop into a single
  transition parametrised by `n` (FAST, Frohn's calculus). CrossCheck's exact
  treatment of loops = acceleration + minimisation over `n`.
- **Master Theorem** (Cormen et al.): closed-form asymptotics for divide-and-conquer
  recurrences `T(n) = a·T(n/b) + f(n)`. Mentioned in the paper as the tool needed for
  sharper recursion bounds (out of scope).

## 18. Linear programming and Farkas' Lemma

**Linear programming (LP)**: optimise a linear objective under linear inequalities,
over real/rational numbers. Solvable in polynomial time (ellipsoid, interior point;
simplex is fast in practice). **Integer** linear programming (ILP) — same with
integer variables — is NP-hard. IPET (Section 12) is an ILP.

**Farkas' Lemma** (Gyula Farkas, 1902) answers: *when does a system of linear
inequalities imply another inequality?* Affine form, over the rationals/reals:

> If the system `A x ≤ b` has a solution, then
> `∀x. (A x ≤ b ⟹ c·x ≤ d)`
> holds **if and only if** there exist multipliers `λ ≥ 0` with `λᵀA = c` and `λᵀb ≤ d`.

Intuition: the only way to *derive* a linear consequence is to add up the premises
with non-negative weights (and weaken the constant). The "if" direction (multipliers
⟹ implication) is elementary: multiply, add, done. The "only if" direction
(implication ⟹ multipliers exist) is the deep part (it is LP duality).

**Why it matters for synthesis.** The ranking conditions are statements
"for all states x satisfying the guard, V decreases", i.e. `∀x. guard(x) ⟹ …`, with
`V`'s coefficients `w` unknown — a ∀∃ problem, hard for solvers. Farkas replaces
"∀x" by "∃λ": the problem becomes a plain existential system of linear constraints
in `(w, c₀, λ)` — an LP. Note that the products `λᵢ·a_{ij}` are linear because the
`a_{ij}` are known numbers, and products `w_j · (known expr)` are linear in `w`.
This is the **Colón–Sipma / Podelski–Rybalchenko** method.

**Soundness vs completeness for CrossCheck**: the plugin only needs the easy
direction (if Z3 finds `λ`, the implication is true — proved in Lean as
`farkas_sound`). Completeness (if a linear ranking function exists, Farkas finds
it) holds over the rationals; over the *integers*, a loop may have a linear ranking
function valid on integer points but not on the rational relaxation, so the method
can miss it (Ben-Amram & Genaim: the integer problem is coNP-complete). Missing a
certificate only causes a (safe) rejection.

## 19. SAT, SMT and Z3

- **SAT**: is a propositional formula satisfiable? NP-complete, but modern CDCL
  solvers handle millions of variables.
- **SMT** (Satisfiability Modulo Theories): SAT plus background theories —
  linear integer/real arithmetic (LIA/LRA), bit-vectors, arrays, uninterpreted
  functions… A query is a formula; the answer is `sat` (with a model = a satisfying
  assignment), `unsat`, or `unknown` (timeout, incomplete theory).
- **Z3** (de Moura & Bjørner, Microsoft Research, 2008): the most widely used SMT
  solver; has an *optimisation* extension (`z3::optimize`, "νZ") that minimises an
  objective.

How the plugin uses Z3 (details in Part 4):

- **entailment** "do facts F imply goal g over ℤ?": ask whether `F ∧ ¬g` is
  satisfiable; `unsat` means yes. `unknown` is treated as "no" (safe);
- **feasibility**: is a path condition satisfiable? `unknown` is treated as "yes"
  (safe: keeps the path);
- **synthesis**: an LRA optimisation problem in `(w, c₀, K, λ…)` minimising `K`.

Trust: the paper stresses that the certificate (`w`, `c₀`) can be re-checked
independently, so "the solver need not be trusted" *in principle*; the current
plugin does not re-check, so in practice Z3 is in the trusted base (Part 7).

## 20. Soundness, completeness, precision

For a bound analyser:

- **Sound**: every reported bound is ≥ the true worst case (no under-estimation).
  An unsound WCET tool is dangerous; soundness is non-negotiable.
- **Complete**: every program that has a finite bound gets one. Impossible in general
  (halting problem); all real tools are incomplete.
- **Precise / tight**: the reported bound is close to the true worst case. Measured
  as overestimation ratio on benchmarks.

A sound-but-incomplete tool can **reject** good programs (false alarms) but never
**accept** bad ones. CrossCheck's plugin is designed that way: whenever the analysis
cannot prove something, it fails the build or treats a value as unknown. The
"Unsound" test suite in `clang-plugin/tests/analyzer_test.cpp` lists loops that
*must* be rejected (moving bound, wrap-around, aliasing, `continue` skipping the
increment…).

"Sound *relative to* assumptions": the plugin's bounds hold if the listed
assumptions (annotations, no undefined behaviour) hold and the implementation is
correct. Always state the relative form.

## 21. Proof assistants, Lean, mathlib, axioms

A **proof assistant** (interactive theorem prover) is a programming language whose
type checker checks mathematical proofs. Main systems: **Coq/Rocq** (CompCert,
Blazy et al.), **Isabelle/HOL** (seL4, Haslbeck & Nipkow), **Lean** (mathlib, this
project), **Agda**, **HOL4**.

Key ideas (detailed in Part 5):

- **Propositions as types** (Curry–Howard): a theorem statement is a type; a proof
  is a program of that type. Checking the proof = type-checking the program.
- **Kernel**: a small trusted core re-checks every proof term. Tactics (automation)
  are untrusted helpers that *produce* terms; the kernel validates them. This is the
  **de Bruijn criterion**: trust reduces to a small checker.
- **Axioms**: assumptions accepted without proof. Lean's standard library uses three:
  `propext` (equivalent propositions are equal), `Quot.sound` (quotients), and
  `Classical.choice` (choice; gives excluded middle). `#print axioms thm` lists those
  a theorem depends on. A project-specific `axiom` or a `sorry` (a placeholder
  "trust me") would be a hole; CrossCheck has neither.
- **mathlib**: Lean's community mathematics library (~2 million lines): numbers,
  algebra, order theory, analysis, tactics like `linarith`, `ring`, `omega`.
- **What a Lean proof guarantees**: the *Lean statement* is true. Whether the Lean
  statement means what the paper says ("statement fidelity") is a human question —
  this is why `AI_USAGE.md` §3 asks you to compare each row of Table 1.

## 22. Things with similar names that CrossCheck is *not*

| Term | What it is | Relation to CrossCheck |
|---|---|---|
| **Mazurkiewicz traces** | equivalence classes of words under commutation of independent letters (concurrency theory) | none; CrossCheck traces are plain words (paper says so) |
| **Trace semantics** (process algebra) | the set of all possible action sequences of a process | related in spirit; CrossCheck uses the trace of one run |
| **Operads** | algebraic structures for composing operations with many inputs | early drafts used the word for grafting; removed |
| **Kleene algebra (with tests), KAT** | algebra of regular expressions + tests for reasoning about while programs | removed from the paper; a referee might still suggest it as related |
| **Tropical geometry** | geometry over the (min,+) semiring | unrelated beyond the semiring |
| **Lyapunov function** (control) | energy-like function proving stability | analogy only |
| **Program synthesis** | generating programs from specifications | removed from the title: CrossCheck synthesises *potentials*, not programs |
| **WCET tool** | full timing analyser on binaries | CrossCheck is a source-level *cost bound* analysis, a component of one |
