# Part 2 — Reading the paper, section by section

This part follows `paper/crosscheck.tex` in order. For each definition and result it
gives: **what it says** in plain words, **why it is true** (the proof idea), **where
it lives in Lean**, and **what to say if asked**. Background terms are explained in
[Part 1](01-background.md); Lean syntax in [Part 5](05-lean-tutorial.md).

Paper labels (`thm:…`, `prop:…`) are used instead of numbers.

Contents

1. [Title and abstract](#1-title-and-abstract)
2. [Introduction, Positioning, Contributions](#2-introduction-positioning-contributions)
3. [Related Work](#3-related-work)
4. [Foundations](#4-foundations)
5. [Loops and Recursion as Optimization Problems](#5-loops-and-recursion-as-optimization-problems)
6. [Application to Imperative Programming](#6-application-to-imperative-programming)
7. [Examples, recomputed by hand](#7-examples-recomputed-by-hand)
8. [Prototype Implementation](#8-prototype-implementation)
9. [Mechanization in Lean 4](#9-mechanization-in-lean-4)
10. [Limitations, Conclusions, AI statement](#10-limitations-conclusions-ai-statement)
11. [The whole paper on one page](#11-the-whole-paper-on-one-page)

---

## 1. Title and abstract

*"CrossCheck: Dual-Layer Semantics of Imperative Programs and WCET Verification via
Constrained Optimization."*

- **Dual-layer semantics**: every execution is described twice, by *what is executed*
  (a trace or tree — intensional) and by *what it does to the state* (extensional).
- **WCET verification**: the practical goal is to check, at compile time, that code
  meets a cost budget.
- **Constrained optimization**: loops and recursion are characterised as "find the
  smallest trace/tree satisfying the exit constraint".

The abstract's chain of argument, which you should be able to recite:

1. Structured control flow (while, linear recursion, branching recursion) can be
   written as minimisation problems over traces (free monoid) and trees (free term
   algebra), ordered by **order-by-composition** `⊑`.
2. Halting = finding the minimal trace/tree satisfying the negated loop condition;
   this **coincides with the standard big-step semantics** (proved).
3. For translation updates (`x += c`), the problem is solvable in closed form
   (state and iteration count together); in general it is undecidable.
4. So the exact equations are **relaxed** into **cost envelopes** (upper bounds),
   using **ranking potentials** and the **(max,+) reading of the timing schema**.
5. This gives sound bounds on cost — the loop-bound and path-cost ingredients of
   WCET — without simulation or unrolling.
6. Mechanised in Lean 4.

## 2. Introduction, Positioning, Contributions

**Introduction.** Contrasts two families of static analysis — path exploration
(model checking, symbolic execution) and over-approximation (abstract
interpretation) — and the WCET question ("will it finish within budget?"). It notes
that classical WCET (IPET) needs loop bounds as *input*, and that recursion is
usually excluded. CrossCheck's pitch: a single framework that gives loop *and*
recursion bounds.

**Positioning** — the most important paragraph for talking to experts. It says,
honestly, that every ingredient is classical:

| Ingredient | Classical source |
|---|---|
| `n̄ = min{n ∣ ¬P(fⁿ(s₀))}` | Kleene's μ-operator |
| ranking functions | Floyd 1967 |
| ranking functions → complexity bounds | Alias et al., SPEED, Sinn et al. |
| branch = max, loop = bound × body | timing schema (Shaw; Puschner & Koza) |
| (max,+) algebra | Baccelli et al. |

and that the contribution is the **uniform packaging**: one order-theoretic
formulation for loops, linear recursion and branching recursion; cost and state
carried together; soundness w.r.t. big-step semantics machine-checked end to end.

If an expert says "this is all known", the right answer is "yes — the paper says so
in Positioning; the contribution is the uniform formulation and its mechanised
link to the standard semantics, plus the prototype". Do not claim novelty of the
individual results.

**Contributions** list: order-by-composition and minimal exiting trace;
generalisation to recursion; cost envelopes; machine-checked soundness; constraint
generation; prototype. Each maps to a section below.

## 3. Related Work

Seven paragraphs; each reference is summarised in [Part 3](03-bibliography.md). The
key comparative claims you must be able to defend:

- *Cost and bound analysis*: the Lyapunov bound is "the single-loop core shared by
  these methods"; CrossCheck is **less precise** than them (no amortisation across
  nested loops). Its difference is the semantic embedding.
- *Ranking function synthesis*: the Farkas method is adopted **unchanged**.
- *Loop acceleration*: exact loop treatment = acceleration + minimisation.
- *WCET*: the cost rules **are** the timing schema; what is added is their
  derivation from a trace semantics and a mechanised soundness proof. CrossCheck
  covers flow/bound analysis and path combination, not micro-architecture.
- *Mechanized cost analysis*: compared with Blazy et al. (verified loop-bound
  estimation in CompCert) and Carbonneaux et al., "our mechanization is smaller in
  scope" — it covers the theory, not a verified analyser for a real language.
- *Compile-time real-time checks*: Clang's function effect attributes
  (`[[clang::nonblocking]]`) forbid blocking/allocation but do not bound loops.
- *Semantics*: big-step is Kahn's natural semantics; divergence can be modelled
  coinductively (Leroy & Grall); here divergence = infeasibility. CrossCheck traces
  are not Mazurkiewicz traces.

## 4. Foundations

### 4.1 `def:state-transition` — State space and partial transitions

**Says.** States `S` (e.g. maps from variables to values). A partial transition is a
partial function `f : S ⇀ S`. `S⊥ = S ∪ {⊥}` and `f⊥` is the strict total extension.

**Why.** Lets us compose possibly-failing steps without tracking domains (Part 1 §2).

**Lean.** `PointedState S := Option S`, `PartialTransition S := S → Option S`,
`extendToPointed` (module `State`).

### 4.2 `def:trace-functional` — Traces, iteration, valuation

**Says.**
- `Σ` = alphabet of primitive instructions; `Σ*` = finite traces, concatenation `·`,
  empty trace `ε`.
- Iteration `tⁿ`: `t⁰ = ε`, `tⁿ = tⁿ⁻¹·t`.
- Valuation `⟦·⟧ : Σ* → (S⊥ → S⊥)`: `⟦ε⟧ = id`, `⟦a⟧ = I(a)⊥`, `⟦t₁·t₂⟧ = ⟦t₂⟧ ∘ ⟦t₁⟧`.

Then equation `eq:iter-hom`: `⟦tⁿ⟧ = ⟦t⟧ⁿ`.

**Why.** Freeness of `Σ*` (Part 1 §4) makes `⟦·⟧` well defined; `eq:iter-hom` by
induction on `n`.

**Lean.** `Trace Instr := List Instr`, `traceIter` (notation `t ^[n]`),
`evalTrace`, `evalTrace_concat`, `evalTrace_iter`. In Lean, `evalTrace` *is* defined
by recursion on the list (instruction by instruction), and the homomorphism property
is a theorem.

**If asked "what is an instruction?"** Any atomic step you choose to count: an
assignment, a comparison, a machine instruction. The theory is parametric in `Σ`
and in the interpretation `I`.

### 4.3 `def:subadditive-norm` — Cost norms

**Says.** A *subadditive cost norm* `‖·‖ : Σ* → ℕ` has `‖ε‖ = 0` and
`‖u·v‖ ≤ ‖u‖ + ‖v‖`. The *weighted cost* `‖a₁…a_k‖_ω = Σ ω(aⱼ)` is additive (equality).
`cost(t) = |t|` (length) is the unit-weight case.

**Why this generality.** Exact identities are stated for `cost`; upper bounds hold for
any subadditive norm, so the same theorems work for "number of instructions",
"cycles with per-instruction worst-case latencies", "energy", etc. The weights `ω(a)`
are where timing information would come in — the paper is careful that obtaining
valid `ω` on a real processor is micro-architectural analysis (not done).

**Lean.** `cost`, `wcost`, `wcost_append`, `wcost_iter`, `wcost_one`. Note: Lean
proves the *weighted (additive)* case, not general subadditive norms.

### 4.4 `def:order-by-composition` and `prop:poset-properties`

**Says.** `u ⊑ w` iff `w = u·v` for some `v` — `u` is a **prefix** of `w`, i.e. `w`
is obtained by *executing more* after `u` ("order-by-composition"). Properties:
partial order, least element `ε`, well-founded; `cost` additive and monotone.

**Why.** Reflexive (`v = ε`), transitive (concatenate the extensions), antisymmetric
(lengths force the extension to be empty). Well-founded: a strict prefix is strictly
shorter. Monotone: `cost(u·v) = cost(u) + cost(v) ≥ cost(u)`.

**Lean.** `OrderByComposition` (infix `⊑`), `order_refl`, `order_trans`,
`order_antisymm`, `order_cost_le`, `cost_additive`, `cost_iter`.
(Well-foundedness is argued in the paper; Lean proves the facts used downstream.)

**Intuition to give.** The prefix order is "time": `u ⊑ w` means `u` is what the
program had done at some earlier moment of the run that produced `w`.

### 4.5 `prop:n-monotony` — Monotonicity of trace iteration

**Says.** `n ≤ m ⟹ tⁿ ⊑ tᵐ`; if `t ≠ ε` the converse holds too, so `n ↦ tⁿ` is an order
isomorphism onto the chain of powers.

**Why.** `tᵐ = tⁿ·t^{m−n}`. Converse: compare costs, `n·|t| ≤ m·|t|` with `|t| > 0`.

**Lean.** `iter_monotone`, `iter_monotone_iff` (with hypothesis `ht : t ≠ []`).

**Why it matters.** It transports "smallest `n`" (in ℕ) to "smallest trace" (in
`⊑`) — that is the bridge between the μ-operator and the trace order.

### 4.6 `thm:minimal-trace` — Minimal Exiting Trace Existence

**Says.** Let `N = {n ∣ ⟦tⁿ⟧(s₀) exits}` (exits = defined and `P` false). If `N ≠ ∅`
it has a unique minimum `n̄`; `t^n̄` is the `⊑`-least exiting power; its cost is
`n̄·cost(t)` and is minimal.

**Why.** Well-ordering of ℕ + `prop:n-monotony` + monotonicity of cost.

**Lean.** `exists_minimal_iteration` (uses `Nat.find`, i.e. μ). The `evalTrace`
there is a *parameter* — the theorem holds for any valuation function.

**Remark after it.** `n̄` is exactly Kleene's μ. The paper's claim is not that this is
new, but that reading it in the trace order minimises every monotone cost at once.

### 4.7 `def:path-selector`, `prop:worst-case-step` — Bodies with data-dependent paths

**Problem.** A body with an `if` does not produce the same trace every iteration.

**Says.** A *path selector* `τ : S → Σ*` gives, for each state, the trace one body
execution produces from it. `f(s) = ⟦τ(s)⟧(s)` is the induced update. `n` iterations
produce `ρₙ(s) = τ(s₀)·τ(s₁)⋯τ(s_{n−1})`, `s_k = fᵏ(s)`. For a conditional,
`τ_if(s) = t_c · (t_then or t_else depending on c)` (`eq:cond-selector`).

`thm:minimal-trace` carries over with `ρₙ` in place of `tⁿ`.

`prop:worst-case-step`: if every `‖τ(s)‖ ≤ W` then `‖ρₙ(s)‖ ≤ n·W`.

**Why.** Induction on `n`, `ρ_{n+1}(s) = τ(s)·ρₙ(f(s))`, subadditivity.

**Lean.** `runTrace τ f n s` is `ρₙ(s)`; `runTrace_const` (constant τ gives `tⁿ`);
`runTrace_cost_le`, `runTrace_wcost_le`. `condTrace` in `Dominance` is `τ_if`.

**Software intuition.** `τ` is "the instruction trace your profiler would record
for one iteration starting from this state".

### 4.8 `prop:nested-cost` — Nested and sequential loops

**Says.** Nested: `n` outer iterations each doing `t₁` then `m` inner iterations of
`t₂` give trace `(t₁·t₂ᵐ)ⁿ` with cost `n·cost(t₁) + n·m·cost(t₂)`. Sequential:
`t₁^{n₁}·t₂^{n₂}` costs `n₁·cost(t₁) + n₂·cost(t₂)`, and the first loop is a prefix.

**Lean.** `nestedTrace`, `nested_trace_cost`, `sequential_loops_cost`,
`sequential_loops_prefix`.

The paragraph after it says the state-dependent inner count is handled by path
selectors and bounded later (`subsubsec:compositional-wcet`).

### 4.9 `prop:tropical-dominance` — Branch Rule

**Says.** `‖τ_if(s)‖ ≤ ‖t_c‖ + max(‖t_then‖, ‖t_else‖)` for every state.

**Why.** Only one branch runs; both possibilities are ≤ the max.

**Lean.** `condTrace_cost_le`, `branch_supremum_bound` (`Dominance`).

This is the timing schema rule for `if`; "sequencing is `+`, branching is `max`" —
the (max,+) reading (Part 1 §13). The label still says "tropical-dominance" for
historical reasons; the statement is called "Branch Rule".

### 4.10 `eq:bigstep-while`, `thm:extensional-equivalence` — Big-step semantics and the equivalence

**Says.** Big-step semantics of `while P do t`: the least relation `⇓` with

```
 P(s) = false                P(s) = true   ⟦t⟧(s) = s' ∈ S   s' ⇓ s''
 ────────────               ──────────────────────────────────────────
   s ⇓ s                                    s ⇓ s''
```

Theorem: `s₀ ⇓ s̄` **iff** there is `n̄` with (1) `⟦t^n̄⟧(s₀) = s̄` and `P(s̄)` false;
(2) for every `k < n̄`, `⟦tᵏ⟧(s₀)` is defined and `P` holds there. `n̄` is unique
(= the minimum of `thm:minimal-trace`), and big-step is deterministic.

**Why.** (⇒) Induction on the derivation: exit rule gives `n̄ = 0`; step rule adds 1.
(⇐) Induction on `n̄`: `n̄ = 0` is the exit rule; otherwise `P(s₀)` holds (k = 0) and
`⟦t⟧(s₀) ≠ ⊥` (else everything after is ⊥ by strictness), apply induction to `s'`.
Uniqueness: two different counts would make the same state both exit and continue.

**Lean.** `WhileBigStep` (inductive), `MinimalExit`, `whileBigStep_iff_minimalExit`,
`MinimalExit.unique`, `WhileBigStep.deterministic`, `while_trace_semantics` (the
trace form, exactly this theorem).

**Consequence.** If no `n̄` exists, there is no derivation: the loop faults or
diverges. This is the paper's treatment of non-termination — *infeasibility* of the
minimisation problem.

**This is the central correctness theorem.** If an expert asks "why should I believe
your minimisation is the loop's meaning?", this is the answer, and it is
machine-checked.

**Remark "Fixed-point reading".** The chain `ε ⊑ t ⊑ t² ⊑ …` is a Kleene chain whose
limit is `t^ω`; not used further (Part 1 §8).

### 4.11 `def:tree-algebra`, `def:tree-order`, `prop:tree-order-properties` — Computation trees

**Says.** Trees with leaves `ε` (base-case calls) and nodes `g(T₁,…,T_b)` (a call
that makes `b` recursive calls). Grafting `T₁ ⊗ T₂` puts `T₂` on every leaf; leaf
substitution puts possibly different trees on each leaf. `cost` = nodes, `leaves`,
`depth`.

Tree order `T₁ ⊑_tree T₂`: `T₂` is obtained from `T₁` by leaf substitution;
equivalently, the least relation with `ε ⊑_tree T` and node-wise extension.

Properties: partial order with least element `ε`; cost and depth monotone;
`T ⊑_tree T ⊗ T'`; every tree of depth ≤ d is below the full tree `F_d`, so
`cost(T) ≤ (b^{d+1}−1)/(b−1)`.

**Intuition.** `⊑_tree` is the tree version of "prefix": `T₂` is `T₁` with some calls
that were base cases now expanded further. It is "time" for a recursion: the call
tree at an earlier moment of exploration.

**Lean.** `BTree` (binary), `TreePrefix` (infix `⊑_tree`), `treePrefix_refl/trans`,
`treePrefix_antisymm` (on `BTree Unit`, i.e. shapes), `treePrefix_size_le`,
`treePrefix_depth_le`, `treePrefix_graft`, `treePrefix_fullTree`,
`size_le_of_depth_le`. **Binary only** for the order (paper says so in
`sec:mechanization`).

### 4.12 `def:tree-exponentiation`, `prop:tree-power-complexity` — Tree powers

**Says.** `B^{⊗0} = ε`, `B^{⊗(d+1)} = B ⊗ B^{⊗d}` (one level of unfolding, repeated).
With `L` leaves and `I` internal nodes in `B`:
leaves `L^d`; cost `I·(L^d−1)/(L−1) + L^d`; for the elementary step (`I=1, L=b`),
`B^{⊗d}` is the full tree, cost `(b^{d+1}−1)/(b−1)`; and the powers form a chain.

**Why.** Grafting multiplies leaves and satisfies
`cost(T₁⊗T₂) = (cost(T₁) − leaves(T₁)) + leaves(T₁)·cost(T₂)` (internal nodes of
`T₁` stay; each leaf becomes a copy of `T₂`). Solve the recurrence
`c_{d+1} = I + L·c_d`, `c_0 = 1`.

**Lean.** `graft`, `graft_size`, `graft_leafCount`, `graft_assoc`, `treePow`,
`treePow_leafCount`, `treePow_size` (binary form `2L^d − 1`), `cherry`,
`treePow_cherry`, `treePow_chain`.

## 5. Loops and Recursion as Optimization Problems

### 5.1 While loops — `prop:min_x`

The generic loop `while (cond(x)) x = body(x);` is the fixed point
`Y(λw.λx. cond(x) (w (body x)) x)` (Manna).

**Says.** With path selector `τ` and induced partial update `f`, the loop terminates
from `s₀` in `s̄` iff `s̄ = f^n̄(s₀)` with `n̄ = min{n ∣ fⁿ(s₀) exits}` (all iterates up
to `n̄` defined). `(n̄, s̄)` unique; executed trace `ρ_n̄(s₀)` is the `⊑`-least exiting
one.

**Why.** Same proof as `thm:extensional-equivalence`, which only used that the body is
a strict extension of a partial function.

**Lean.** `whileBigStep_iff_minimalExit`, `MinimalExit.unique`; for total bodies
`whileBigStep_total_iff` and `solveLoop_sound`.

"*A loop is solved, rather than executed, whenever a closed form of `n ↦ fⁿ(s₀)` is
available*" — the one-sentence summary of the exact layer.

### 5.2 Linear recursion — `prop:linrec`

```
function rlin(x) { if (cond(x)) return back(x, rlin(fwd(x))); return stop(x); }
```

**Says.** `rlin(s₀)` returns
`back(s₀, back(s₁, … back(s_{n̄−1}, stop(s_n̄))))` with `s_k = fwdᵏ(s₀)` and
`n̄ = min{n ∣ ¬P(fwdⁿ(s₀))}`. Frame-independent case (`back` ignores `x`):
`(backⁿ̄ ∘ stop ∘ fwdⁿ̄)(s₀)`. Trace `t_fwd^n̄ · t_stop · t_back^n̄`, cost
`n̄(cost t_fwd + cost t_back) + cost t_stop`.

**Intuition.** A linear recursion is two loops: a **descending** loop (calls,
`fwd`), which is a while loop deciding the depth `n̄`, and an **ascending** loop
(returns, `back`), which runs exactly `n̄` times. "Frame-dependent" = the
ascending phase needs the saved stack frames `s_k` (which is why the stack is needed);
frame-independent recursions are "tail-recursion plus a counter".

**Lean.** `FramedRecurrence`, `unwind`, `FramedBigStep`, `framedBigStep_iff`,
`LinearRecurrence.toFramed`, `linRec_iff`, `linear_recursion_cost`.

### 5.3 Branching recursion — `prop:tree-optimization`

```
function rtree(x) { if (cond(x)) return combine(rtree(fwd_1(x)), …, rtree(fwd_b(x))); return stop(x); }
```

Positions `π ∈ {1..b}*` address calls; `s_π` is the argument at position `π`. A tree is
**feasible** if every leaf position `π` has `¬P(s_π)`. The **execution tree**: internal
positions = calls with `P`, leaves = calls with `¬P`.

**Says.** If the call terminates, its execution tree `T̄` is the `⊑_tree`-least
feasible tree; it is unique, of minimal cost and depth among feasible trees, and the
returned value is the catamorphism (stop at leaves, combine at nodes).

**Why.** Induction on `T̄`, for all states simultaneously. If `T̄` is a leaf: least
element. Otherwise `P(s₀)`, so a feasible `T` cannot be a leaf (its only leaf would be
at a state where `P` holds); compare subtrees by induction.

**Lean.** `TreeRecurrence`, `IsExecTree`, `LeavesExit`, `evalTree`, `exec_least`,
`exec_unique`, `exec_size_min`, `TreeBigStep`, `treeBigStep_iff` (binary).

**Note after it.** A feasible tree may expand a position where `P` already fails
(over-expansion); such trees are strictly larger — the analogue of `tⁿ` with `n > n̄`.

## 6. Application to Imperative Programming

### 6.1 `subsec:equation-generation` — Equation generation (exact)

A **symbolic evaluation** that emits unknowns and equations instead of values:

- each variable `L` gets a family of unknowns `L₀, L₁, …`, one per assignment
  (this is SSA — *static single assignment* — form, familiar from compilers);
- for each loop, three symbolic stores: `σ_init` (entry), `σ_loop` (after `n`
  iterations, last successful guard), `σ_last` (failing guard), linked by binding
  equations;
- the loop rule: guard true in `σ_init` and `σ_loop`, false in `σ_last`, body
  iterated `n` times (`body^{∘n}`), `n` minimal.

`body^{∘n}` disappears when the iterate has a closed form (translations: `x + n·c`).
If the guard fails initially, the loop is skipped; if no `n` satisfies the exit
constraint, the system is infeasible ⟹ non-termination.

Recursion: descending-phase loop constraints + ascending-phase equations (linear);
unknowns indexed by tree positions (branching).

**Not mechanised.** These rules are described at the level needed for the examples;
their justification is Section 5.

**Remark "Decidability Boundaries".** Translations + linear guards ⟹ Presburger,
decidable (loop acceleration); multiplication between variables ⟹ Diophantine,
undecidable (Matiyasevich). Hence relaxation.

### 6.2 `subsec:asymptotic-relaxation` — Relaxation and WCET envelopes

Exact solutions need closed forms and known inputs; real code branches on data
(`2ⁿ` paths). For real-time, the question is `WCET(s₀) ≤ Deadline`. So: project
state onto a scalar cost, collapse branches with (max,+), bound iteration counts by
ranking potentials. **Every bound is a sound upper bound, not an asymptotic
statement** (despite the historical label).

#### `prop:tropical-collapse` — Tropical branch collapsing

A body with `k` sequential conditional blocks:
`‖τ(s)‖ ≤ W = Σⱼ (‖t_{cⱼ}‖ + max_b ‖t_b‖)`. Up to `2ᵏ` paths summarised by one
number, computed in linear time. Exact when the maximising branches are jointly
feasible; otherwise an over-approximation (infeasible paths not excluded).
Lean: `branch_supremum_bound`, `condTrace_cost_le` + subadditivity.

#### `def:ranking-potential`, `thm:lyapunov-bound` — Ranking potentials

`V : S → ℤ` is a ranking potential with decrease `Δ > 0` if, on every state where
the loop continues: **descent** `V(f(s)) ≤ V(s) − Δ` and **positivity** `V(s) > 0`.

Theorem: the loop terminates and `n̄ ≤ N̄(s₀) = max(0, ⌈V(s₀)/Δ⌉)`; the executed trace
costs at most `N̄(s₀)·‖t_wc‖`.

**Proof idea.** After `k` continuing iterations `V ≤ V(s₀) − kΔ`. Before the last
continuing iteration `n−1`, positivity gives `0 < V(s₀) − (n−1)Δ`, so
`n ≤ ⌈V(s₀)/Δ⌉`. Hence `P` cannot hold at all of `s₀..s_N̄`: some iterate exits, and
`thm:minimal-trace` gives `n̄`, also bounded. Cost: `prop:worst-case-step`.

**Lean.** `rankBound` (= `⌈V₀/Δ⌉` clipped at 0), `ranking_descent`, `ranking_bound`,
`ranking_terminates`, `wcet_bound`, `wcet_bound_weighted`.

**Relational variant** (paragraph after the theorem): `V` in an ordered field (ℚ),
`→` a transition *relation* (nondeterministic or partial): if `V(s') ≤ V(s) − 1` and
`V(s) ≥ 1` whenever `s → s'`, every run has length `≤ ⌊V(s₀)⌋`. Divide by `Δ` to
normalise. This is what the plugin uses. Lean: `ranking_bound_floor`,
`ranking_bound_of_le`, `partial_ranking_floor`, `while_ranking_floor`.

Why two versions? The integer/deterministic one gives **termination** too (some
iterate exits); the relational one gives only a bound on **run length** (for a
nondeterministic loop, "terminates" needs more care), but that is what a bound
analysis needs.

#### `subsubsec:compositional-wcet` — Nested loops, branching recursion, size potential

**Nested loops.** If the inner loop runs at most `M_max` times whenever entered, each
outer iteration costs ≤ `‖t₁‖ + M_max‖t₂‖`, so the loop costs ≤
`N_max‖t₁‖ + N_max M_max ‖t₂‖` (Lean `nested_wcet_bound`). Sound, not amortised.

**`prop:tree-envelope` — Branching Recursion Envelope.** A *depth ranking potential*
`V_tree : S → ℕ` strictly decreasing along every recursive call bounds the depth by
`D_max = V_tree(s₀)`, and the cost by the full tree, `(b^{D+1}−1)/(b−1)`.
Lean: `exec_depth_le`, `exec_size_le`.

Then: counts *calls*; multiply by per-call work `w`; size-dependent work needs
recurrence solving (Master Theorem), out of scope.

**`prop:size-potential` — Size Potential** (added November 2026). General scheme: an
activation with argument `x` makes calls `c₁(x)…c_{k(x)}(x)`. If
`U(x) ≥ 1 + Σᵢ U(cᵢ(x))` for all `x`, the call tree of a terminating call has
≤ `⌊U(x)⌋` nodes. Second statement: with ≤ `b` calls per activation and a strictly
decreasing `V : S → ℕ`, ≤ `Σ_{j≤V(x)} bʲ` nodes.

**Proof.** Induction on the call tree: size = 1 + sizes of subtrees ≤ 1 + Σ U(cᵢ) ≤ U.

**Example.** Split `[lo, hi)` at an interior point, recurse on both halves:
`U = 2(hi−lo) − 1` works: leaves have `hi−lo = 1`, `U = 1`; internal nodes
`1 + (2(mid−lo)−1) + (2(hi−mid)−1) = 2(hi−lo)−1`. So linearly many calls, whereas the
depth bound (depth ≤ hi−lo) gives exponentially many. Lean:
`callTree_size_le_potential`, `callTree_size_le_geom`, `geom_closed` (`Arity`).

Attribution: the potential method of amortised analysis (Hoffmann et al.).
`AI_USAGE.md` §3 asks you to check this proposition and its attribution.

#### `subsubsec:smt-synthesis` — SMT-based synthesis of ranking potentials

Loop over `x ∈ ℤᵏ`, affine update `x' = Ax + b`, guard `Gx ≤ g`. Template
`V(x) = wᵀx + c₀`. Conditions become implications

```
Gx ≤ g ⟹ wᵀ(x − Ax − b) ≥ Δ          (descent)
Gx ≤ g ⟹ wᵀx + c₀ ≥ 1                (positivity)
```

By Farkas, each implication ⇔ ∃ multipliers `λ ≥ 0` with linear equalities (Part 1
§18): a linear query in `(w, c₀, λ)`, solved by Z3. Only the easy direction of
Farkas is needed to trust a result (Lean `farkas_sound_affine`). Sound for integer
programs; complete for linear ranking functions over ℚ (Ben-Amram & Genaim); misses
lexicographic/non-linear arguments.

The certificate `max(0, ⌈(wᵀx₀ + c₀)/Δ⌉)·‖t_wc‖ ≤ Deadline` is checked over the
admissible inputs; it can be re-checked without the solver. Unsat ⟹ the routine is
rejected (no linear potential for the given guard and invariant).

## 7. Examples, recomputed by hand

### 7.1 Parametric while loop

```c
int i = random(); int x = 1; int y = 2;
while (i++ < 13) { i = i + 1; x = y + 2; y = x + 3; }
```

Trace it with `R = 0`:

| iteration | `i` tested | `i` after guard | body: `i` | `x` | `y` |
|---|---|---|---|---|---|
| 1 | 0 | 1 | 2 | 4 | 7 |
| 2 | 2 | 3 | 4 | 9 | 12 |
| … | … | … | … | … | … |
| 7 | 12 | 13 | 14 | 34 | 37 |
| exit | 14 (fails) | 15 | | | |

So one iteration maps `(i, x, y) ↦ (i+2, y+2, y+5)`; after `n` iterations
`i = R + 2n`, `y = 2 + 5n`, `x = 5n − 1`. The guard tests `R + 2(n−1) < 13` (last
success) and `R + 2n ≥ 13` (failure) — exactly one integer `n` satisfies both:
`n = ⌈(13−R)/2⌉`. Final `i = R + 2n + 1` (failing guard's `++`). `R = 0`: `n = 7`,
`(i, x, y) = (15, 34, 37)`. ✓ If `R ≥ 13`: `i = R+1, x = 1, y = 2`.

Relaxed: `V = 13 − i`, `Δ = 2`, bound `⌈(13−R)/2⌉` — **tight**.

Lean: `ParametricState`, `parametricLoopStep`, `parametric_loop_minimal` (for every
`R`, including `R ≥ 13`), `parametric_loop_bigstep`, `parametric_loop_ranking`,
`parametric_loop_x/y`. Note that Lean models one iteration as the 3-tuple update on
the value *tested* by the guard (the docstring explains the modelling).

`AI_USAGE.md` §3 item 3: the system printed in the paper was corrected by the AI; the
paper says it is produced by a prototype — check whether that is still accurate
(the Clang plugin does not print these equation systems).

### 7.2 Infinite loop

`int i = 0; while (i != 1) i = 0;` — equations require `i_last = i_loop = 0` and
`i_last = 1`: infeasible ⟹ no big-step derivation (divergence). No ranking potential
exists (the state `i = 0` maps to itself). Lean: `infinite_loop_diverges`.

### 7.3 Linear recursion

```c
int foo(int a) { if (a > 4) a = foo(a - 2) + 3; return a + 6; }   foo(10);
```

`fwd(a) = a − 2`, `stop(a) = a + 6`, `back(r) = r + 9` (frame-independent: the
caller's `a` is overwritten). Depth: least `n` with `10 − 2n ≤ 4` ⟹ `n̄ = 3`.
`foo(4) = 10`, `foo(6) = 19`, `foo(8) = 28`, `foo(10) = 37`. ✓
Closed form: `back³(stop(fwd³(10))) = 4 + 6 + 27 = 37`.
Lean: `fooLinearRec`, `linear_recursion_depth`, `linear_recursion_solution`,
`linear_recursion_bigstep`.

### 7.4 Non-linear recursion

`int foo(int x) { if (x > 0) return foo(x-1) + foo(x-1); return 1; }   foo(2);`

Positions `ε, 0, 1, 00, 01, 10, 11`: 7 calls, value 4 = 2². Execution tree = full
binary tree of depth 2 = `B^{⊗2}`. `V_tree(x) = max(x, 0)` bounds work by
`2^{x+1} − 1` — attained. Lean: `binCountdown`, `binary_recursion_exec_tree`,
`binary_recursion_bigstep`, `binary_recursion_envelope`.

## 8. Prototype Implementation

Describes the Clang plugin (details in [Part 4](04-plugin.md)):

- **Input**: annotations — real-time, deadline, parameter ranges, linear
  preconditions (assumed inside, proved at analysed call sites), and three
  *trusted* ones (loop bound, assumed fact, cost of an external function) listed in
  the report.
- **Profile**: no dynamic allocation, exceptions, virtual/indirect calls, `goto`,
  unbounded loops/recursion — transitively through callees, including library code.
- **Cost**: weighted count of source-level operations (the weighted cost of
  `def:subadditive-norm`), composed by the timing schema refined so that a path ending
  in `return` is not charged for code after it; loop cost `K·(guard+body) + guard`
  (Lean `while_cost_bound`).
- **Bounds**: affine symbolic state; candidate invariants proved inductive; one
  transition per path; Z3 finds an affine potential satisfying the relational
  conditions on every path, plus the least `K` dominating it on entry; bound `⌊K⌋`.
  Unsigned arithmetic only when proved not to wrap; machine-integer limits never used
  as bounds. Recursion: both certificates of `prop:size-potential`, smaller kept.
- **Table `tab:plugin`**: results on the benchmark programs, with honest pessimism
  (merge sort quadratic, table lookup linear depth).
- **Trust**: implementation not verified; certificate mathematics is.

## 9. Mechanization in Lean 4

~2,100 lines, 137 theorems, no `sorry`, no axioms beyond the three standard ones.
Table `tab:lean` maps statements to theorems (mirrored by
`formalization/formalization.yaml`).

**Modelling choices** (say these precisely when asked): traces are lists; `S⊥` is
`Option S`; partial transitions are functions into `Option S`; big-step semantics are
inductive predicates; ranking potentials in the main theorem are `ℤ`-valued, the
bound `N̄` is the natural number `rankBound`.

**Not mechanised** (the honest list): branching factor `b > 2` for the order-theoretic
tree results (binary in Lean; counting bounds are arbitrary arity); termination for
partial/nondeterministic updates (only the run-length bound); the equation-generation
rules; completeness of Farkas; the plugin itself.

## 10. Limitations, Conclusions, AI statement

**Limitations**: cost is not time; precision (infeasible paths, no amortisation,
exponential branching envelope unless a size potential exists, every activation
charged the worst case); completeness (closed forms only for fragments; linear
templates; needs invariants); language coverage (no pointers/aliasing, allocation,
mutual recursion, concurrency, `goto`); no systematic evaluation.

**Conclusions** restate the chain of argument (Section 1 above) and future work:
evaluation on benchmark suites, lexicographic/logarithmic/amortised potentials,
arbitrary-arity tree order in Lean, a verified analyser, concurrency.

**Statement on the Use of AI**: required by the AGMAI recommendations; contains an
`[AUTHOR TO CONFIRM]` marker that only you can resolve, after the checks listed in
`AI_USAGE.md` §3.

## 11. The whole paper on one page

```
EXECUTION                         ORDER                    COST
trace  t ∈ Σ*        ─────────    prefix  ⊑      ──────    cost / ‖·‖_ω  (monotone, additive)
tree   T ∈ T_Σ       ─────────    ⊑_tree         ──────    size, depth   (monotone)

EXACT LAYER (extensional + intensional together)
  loop:       n̄ = min{n ∣ fⁿ(s₀) exits};  s̄ = f^n̄(s₀);  trace ρ_n̄(s₀) is ⊑-least   ⇔ big-step  [Lean ✓]
  lin. rec.:  depth n̄ = min{…};  r = back(…back(stop(s_n̄)))                           ⇔ big-step  [Lean ✓]
  tree rec.:  T̄ = ⊑_tree-least feasible tree;  value = catamorphism                   ⇔ big-step  [Lean ✓, binary]
  solvable in closed form for translations (Presburger); undecidable in general (Matiyasevich)

RELAXED LAYER (cost envelopes, always upper bounds)
  sequence  +        branch  max        loop  N̄ × body          ← timing schema = (max,+)
  N̄ = ⌈V(s₀)/Δ⌉ from a ranking potential V                       [Lean ✓, ℤ and ℚ/relational]
  recursion: depth potential → (b^{D+1}−1)/(b−1);  size potential U → ⌊U⌋   [Lean ✓, any arity]
  V, U found by Farkas + LP (Z3); certificate re-checkable          [easy Farkas direction in Lean ✓]

PROTOTYPE: Clang plugin applies the relaxed layer to annotated C++ (unverified, abstract cost units)
```
