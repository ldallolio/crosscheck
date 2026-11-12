# Part 5 — Lean 4 from scratch (with this repository's code)

This part teaches enough Lean 4 to read, modify and extend `formalization/`. It
assumes C++ and no functional programming. Every standalone example below was
type-checked with the project's toolchain (Lean v4.16.0 + mathlib); you can paste
them into a file that starts with `import ImperativeOptimization` and run them.

Contents

1. [What Lean is, and the mental model](#1-what-lean-is-and-the-mental-model)
2. [Setting up and running](#2-setting-up-and-running)
3. [Lean as a programming language](#3-lean-as-a-programming-language)
4. [Propositions, proofs and the two ways to write proofs](#4-propositions-proofs-and-the-two-ways-to-write-proofs)
5. [Logic cheat sheet: how to prove and use each connective](#5-logic-cheat-sheet)
6. [Inductive predicates (big-step semantics in Lean)](#6-inductive-predicates)
7. [The tactics used in this repository](#7-the-tactics-used-in-this-repository)
8. [Numbers: ℕ, ℤ, ℚ, casts, subtraction, division, floor](#8-numbers)
9. [Type classes and mathlib](#9-type-classes-and-mathlib)
10. [Files, namespaces, variables, notation, comments](#10-files-namespaces-variables-notation-comments)
11. [Mutual definitions and structural recursion](#11-mutual-definitions-and-structural-recursion)
12. [Reading a proof state, and a full worked proof](#12-reading-a-proof-state-and-a-full-worked-proof)
13. [Common errors and what they mean](#13-common-errors-and-what-they-mean)
14. [Exercises](#14-exercises)

---

## 1. What Lean is, and the mental model

Lean is a **functional programming language** with a very expressive type system,
in which **a theorem is a type and a proof is a value of that type**
(*propositions as types*, or Curry–Howard). Checking a proof is type-checking.

C++ analogy:

| C++ | Lean |
|---|---|
| `int f(int x);` declares a function from `int` to `int` | `def f (x : ℤ) : ℤ := …` |
| a value of type `std::pair<A,B>` is an `A` and a `B` | a proof of `P ∧ Q` is a proof of `P` and a proof of `Q` |
| `std::variant<A,B>` holds an `A` or a `B` | a proof of `P ∨ Q` is a proof of `P` or of `Q` |
| a function `B f(A)` turns an `A` into a `B` | a proof of `P → Q` turns proofs of `P` into proofs of `Q` |
| a template `template<class T> B f(T)` works for every `T` | a proof of `∀ x, P x` gives a proof of `P x` for every `x` |
| `static_assert(2 + 2 == 4)` | `example : 2 + 2 = 4 := rfl` |

There is no "running" a proof. The compiler checks that the term has the stated type;
if it does, the theorem is proved. Lean's **kernel** (a small checker) re-verifies every
definition and proof; the rest (elaborator, tactics) is untrusted convenience.

Two important differences from C++:

- **All functions are total and pure.** No exceptions, no infinite loops, no mutation.
  Partiality is modelled explicitly (`Option S` for "may fail" — exactly what the
  project does for ⊥). Recursion must be shown to terminate (usually automatic for
  structural recursion).
- **Types can depend on values.** `t ⊑ w` is a type that depends on the traces `t`,
  `w`; `n ≤ m` is a type depending on numbers. A value of it is evidence that it holds.

## 2. Setting up and running

In `formalization/`:

```bash
lake exe cache get     # once: download compiled mathlib (otherwise hours of compiling)
lake build             # check everything; must end with "Build completed successfully"
```

Interactive work: **VS Code + the "lean4" extension**. Open the `formalization` folder,
open a `.lean` file; the **Infoview** panel (`Ctrl+Shift+Enter`) shows, at the cursor,
the current goal of a proof. This is how one reads and writes Lean proofs: move the
cursor line by line through a `by` block and watch the goal change.

Useful commands (type them in any file after the imports; output appears in the Infoview):

```lean
#check double            -- double (n : ℕ) : ℕ           (the type)
#check @ranking_bound    -- the full statement with implicit arguments
#eval double 21          -- 42                            (run a computable definition)
#print axioms ranking_bound
-- 'ImperativeOptimization.ranking_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

To experiment without touching the project, create `Scratch.lean` anywhere and run
`lake env lean Scratch.lean` from `formalization/` (that is how the examples of this part
were checked).

## 3. Lean as a programming language

### Definitions and functions

```lean
def double (n : ℕ) : ℕ := 2 * n      -- name, arguments, return type, body
#eval double 21                       -- 42
```

Function application is by juxtaposition: `double 21`, `f x y` (not `f(x, y)`).
Anonymous functions: `fun x => x + 1` (also written `λ x => x + 1`).
Types of functions: `ℕ → ℕ`; with two arguments `ℕ → ℕ → ℕ` (curried: a function
returning a function).

### Pattern matching and recursion

```lean
def fact : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fact n
```

`ℕ` is defined inductively (zero, successor), so a function on it is given by cases
`0` and `n + 1`. The same style defines the repository's `traceIter`:

```lean
def traceIter (t : Trace Instr) : ℕ → Trace Instr
  | 0 => []
  | n + 1 => (traceIter t n) ++ t
```

`[]` is the empty list, `++` concatenation, `a :: l` "a in front of l" (cons).

`match` inside a body works the same:

```lean
match evalTrace interp (t ^[n]) (some s₀) with
| some s => cond s = false
| none => False
```

### Structures (records)

```lean
structure Point where
  x : Int
  y : Int

def Point.norm1 (p : Point) : Int := |p.x| + |p.y|
#eval ({ x := 3, y := -4 } : Point).norm1     -- 7
```

`p.x` is field access; `{ x := 3, y := -4 }` builds a value; a function named
`Point.norm1` can be called as `p.norm1` ("dot notation"). The repository uses
structures for program schemes: `LoopConstraint`, `LinearRecurrence`,
`FramedRecurrence`, `TreeRecurrence`, `ParametricState`.

### Inductive types (sum types / tagged unions)

```lean
inductive Shape where
  | circle (r : ℕ)
  | rect (w h : ℕ)

def Shape.area : Shape → ℕ
  | .circle r => 3 * r * r
  | .rect w h => w * h
```

Like `std::variant<Circle, Rect>` with exhaustive `std::visit`. Repository example —
binary trees with labels of type `α`:

```lean
inductive BTree (α : Type) where
  | leaf : α → BTree α
  | node : BTree α → BTree α → BTree α
```

`α` is a type parameter (like a template parameter). `BTree Unit` = tree shapes (`Unit`
has a single value `()`), used for call trees.

### `Option`, `List`, `Bool`

- `Option S` = `none | some s` (`std::optional<S>`). The project's `PointedState S` is
  `Option S`, `none` = ⊥.
- `List α` = `[] | a :: l`. `Trace Instr` is `List Instr`. `t.length`, `t.map f`,
  `l.sum`.
- `Bool` = `true | false`, a *data* type. Not the same as `Prop` (next section).

### `abbrev` vs `def`

`abbrev Trace (Instr : Type) := List Instr` is a definition that Lean unfolds
eagerly (a transparent alias, like `using Trace = std::vector<Instr>;`). A `def` is
unfolded only when asked (`unfold`, `simp [name]`, `dsimp [name]`).

## 4. Propositions, proofs and the two ways to write proofs

`Prop` is the type of propositions. `2 + 2 = 4 : Prop`, `t ⊑ w : Prop`. A proof of
`P` is a term `h : P`.

```lean
theorem two_plus_two : 2 + 2 = 4 := rfl
```

`rfl` ("reflexivity") proves `a = a`; Lean accepts it here because `2 + 2` *computes*
to `4`. `example` is an anonymous theorem (checked, not named):

```lean
example : (2 : ℕ) + 2 = 4 := by decide
```

### Term mode vs tactic mode

- **Term mode**: write the proof term directly, e.g. `⟨7, rfl⟩`, `fun x => …`,
  `le_trans h1 h2`. Short proofs in the repo are terms:

  ```lean
  theorem order_refl (t : Trace Instr) : t ⊑ t :=
    ⟨[], (List.append_nil t).symm⟩
  ```

- **Tactic mode**: `by` followed by commands that transform the goal step by step until
  nothing remains. Most proofs in the repo:

  ```lean
  example (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 := by omega
  example (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
  ```

### Bool vs Prop (important in this repository)

Loop conditions are modelled as `cond : S → Bool` (computable, like C++). Statements about
them are propositions: `cond s = true` or `cond s = false`. To turn a decidable
proposition into a `Bool`, use `decide`:

```lean
def isBig (n : ℕ) : Bool := decide (n > 10)
example : isBig 11 = true := by decide
```

In `Examples.lean`, `cond := fun s => decide (s.i < 13)`. Lemmas `decide_eq_true_eq`,
`decide_eq_false_iff_not` convert back to propositions. `decide` as a *tactic* asks Lean
to evaluate a closed decidable statement (e.g. `MinimalIter … 10 3` after unfolding).

## 5. Logic cheat sheet

| Statement | To **prove** it (goal) | To **use** a hypothesis `h` of this form |
|---|---|---|
| `P ∧ Q` | `⟨hp, hq⟩` or `constructor` | `h.1`, `h.2`, `obtain ⟨hp, hq⟩ := h` |
| `P ∨ Q` | `Or.inl hp` / `left`; `Or.inr hq` / `right` | `rcases h with hp \| hq` |
| `P → Q` | `fun hp => …` or `intro hp` | `h hp` (apply it) |
| `∀ x, P x` | `fun x => …` or `intro x` | `h a` (instantiate) |
| `∃ x, P x` | `⟨a, proof⟩` or `use a` / `refine ⟨a, ?_⟩` | `obtain ⟨x, hx⟩ := h` / `rcases h with ⟨x, hx⟩` |
| `P ↔ Q` | `constructor` then both directions; `⟨f, g⟩` | `h.mp` (→), `h.mpr` (←), `rw [h]` |
| `¬P` (= `P → False`) | `intro hp` then derive `False` | `h hp : False`; `absurd hp h` |
| `False` | derive a contradiction: `omega`, `cases` on an impossible equation | `h.elim` / `exact absurd …` — proves anything |
| `a = b` | `rfl`, `rw`, `simp`, `ring`, `omega` | `rw [h]` (replace `a` by `b`), `subst` |

Examples:

```lean
example : ∃ n : ℕ, n * n = 49 := ⟨7, rfl⟩
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩
example (P Q : Prop) (h : P ∧ Q) : Q := by
  obtain ⟨_, hq⟩ := h        -- `_` discards the unused part
  exact hq
example : ([1, 2] : Trace ℕ) ⊑ [1, 2, 3] := ⟨[3], rfl⟩   -- the prefix order is an ∃
```

The angle brackets `⟨…⟩` are the **anonymous constructor**: they build any structure-like
value (pairs, `∃`, `∧`, `↔`) from its components.

**Implicit and explicit arguments.**

```lean
theorem order_trans {u v w : Trace Instr} (h1 : u ⊑ v) (h2 : v ⊑ w) : u ⊑ w
```

`{u v w}` are *implicit*: Lean infers them from `h1`, `h2`, so one writes
`order_trans h1 h2`. `(h1 : …)` are explicit. `@order_trans` makes all arguments explicit.
`[inst : C α]` (square brackets) are *instance* arguments, found by type-class search
(section 9).

## 6. Inductive predicates

An `inductive` whose type ends in `Prop` defines a relation by **inference rules**; this
is how big-step semantics is written. Toy example:

```lean
inductive MyEven : ℕ → Prop
  | zero : MyEven 0
  | step {n : ℕ} : MyEven n → MyEven (n + 2)

example : MyEven 4 := MyEven.step (MyEven.step MyEven.zero)
```

Read each constructor as a rule: `zero` is an axiom `─── MyEven 0`; `step` is
`MyEven n ⟹ MyEven (n+2)`. A proof of `MyEven 4` is a *derivation tree*. `MyEven` is the
*least* relation closed under the rules: nothing else is in it, which is what makes
induction on derivations possible.

The repository's while-loop semantics, compared with the paper's rules
(`eq:bigstep-while`):

```lean
inductive WhileBigStep (cond : S → Bool) (f : S → Option S) : S → S → Prop
  | exit {s : S} : cond s = false → WhileBigStep cond f s s
  | step {s s' s'' : S} : cond s = true → f s = some s' →
      WhileBigStep cond f s' s'' → WhileBigStep cond f s s''
```

```
   P(s) = false              P(s) = true    f(s) = s'    s' ⇓ s''
   ────────────  exit        ──────────────────────────────────── step
      s ⇓ s                                s ⇓ s''
```

`cond` and `f` are *parameters* (fixed), the two `S` after the colon are *indices*
(they vary between rules).

**Using an inductive predicate**: `induction h with | exit hc => … | step hc hf _ ih => …`
does induction on the derivation (one case per rule; `ih` is the induction hypothesis
for the premise `s' ⇓ s''`). `cases h with …` does case analysis without induction
hypothesis. `@step s s' s'' hc hf _ ih` names the implicit arguments too.

The other inductive predicates of the project: `TreePrefix` (`⊑_tree`), `FramedBigStep`,
`TreeBigStep`.

## 7. The tactics used in this repository

Grouped by purpose. "Goal" = what remains to prove; "context" = hypotheses available.

### Structure of the proof

| Tactic | Effect | Example in repo |
|---|---|---|
| `intro x h` | move `∀ x` / `P →` from the goal into the context | `intro k hk` (`Recursion`) |
| `rintro ⟨n, hn, rfl⟩` | `intro` + destructure in one go | `framedBigStep_iff` |
| `exact e` | close the goal with term `e` | everywhere |
| `apply f` | use `f : A → B` on goal `B`, leaving goal `A` | `apply Nat.le_floor` |
| `refine ⟨n + 1, ?_, h2, ?_⟩` | give a partial term; each `?_` becomes a new goal | `WhileBigStep.minimalExit` |
| `constructor` | split `∧`, `↔` or apply the unique constructor | `parametric_loop_minimal` |
| `use v` | provide the witness of `∃` | `order_trans` |
| `have h : P := proof` | add an intermediate fact | everywhere |
| `show P` / `change P` | restate the goal (or hypothesis, `change … at h`) in a definitionally equal form — useful to unfold | `traceIter`, `Examples` |
| `calc a = b := p1 _ = c := p2` | chain of equalities/inequalities | `traceIter_succ` |
| `·` (bullet) | focus on the next goal | `iter_monotone_iff` |
| `t1 <;> t2` | run `t2` on all goals produced by `t1` | `cases c s <;> simp` |
| `by_contra h` | prove by contradiction (assume `¬goal` as `h`) | `ranking_terminates` |

### Case analysis and induction

| Tactic | Effect |
|---|---|
| `induction n with \| zero => … \| succ n ih => …` | induction on ℕ (or a list, tree, derivation) |
| `induction n generalizing s with …` | the induction hypothesis is for *all* `s`, not the fixed one — needed when the recursive call changes the argument (`runTrace_cost_le`, `evalTrace_concat`) |
| `cases h with \| … => …` | case split on a value or a hypothesis |
| `cases h : e with \| none => … \| some x => …` | split on the value of expression `e`, remembering `h : e = …` |
| `rcases h with ⟨x, hx⟩ \| h'` | destructure nested `∃`/`∧`/`∨` patterns; `rfl` in a pattern substitutes an equation |
| `obtain ⟨a, b⟩ := h` | same as `rcases`, different syntax |
| `interval_cases k` | split `k` into finitely many values given `k < 3` etc. (`linear_recursion_depth`) |
| `subst h` | eliminate a variable using `h : x = e` |

### Rewriting and simplification

| Tactic | Effect |
|---|---|
| `rw [h₁, ← h₂]` | rewrite with equations left-to-right (`←` reverses); fails if the pattern is absent |
| `rw [h] at h'` | rewrite inside a hypothesis |
| `simp` | rewrite with the large library of `@[simp]` lemmas until stuck |
| `simp [defn, lemma]` / `simp only [...]` | add lemmas / use only these (more predictable) |
| `simpa using h` | `simp` the goal and `h`, then close with `h` |
| `dsimp [f]` | only *definitional* unfolding (no lemmas): unfold `f`, beta-reduce |
| `unfold f` | unfold a definition |
| `push_cast` | move coercions (`↑n`) inward: `↑(a + b)` → `↑a + ↑b` |
| `norm_num` | evaluate numeric expressions |

### Decision procedures (the workhorses)

| Tactic | Proves | Typical use |
|---|---|---|
| `omega` | linear arithmetic over ℕ and ℤ: `+`, `−` (truncated on ℕ), `*` by constants, `/` and `%` by constants, `≤ < = ≠`, `∧ ∨ ¬`, `max`, `min`, `Int.toNat` | most numerical side conditions (`order_antisymm`, `ranking_bound`, `Examples`) |
| `linarith` | linear arithmetic over ordered fields (ℚ, ℝ) and also ℤ; uses hypotheses in context | `ranking_descent`, `Certificate`, `Arity` |
| `ring` | equalities in commutative (semi)rings: `(n+1)*W = n*W + W` | cost formulas |
| `decide` | closed decidable statements by evaluation | `Examples` |
| `rfl` | definitional equality | |
| `positivity`, `nlinarith`, `aesop` | (not used here; common elsewhere) | |

Rule of thumb when a step is "obvious arithmetic": try `omega` for ℕ/ℤ, `linarith` for
ℚ/ℝ or when it follows from hypotheses by adding them, `ring` for an identity.

## 8. Numbers

- `ℕ` (`Nat`): subtraction is **truncated**: `3 - 5 = 0`. That is why the paper's
  `2^(d+1) - 1` in Lean needs care and why many lemmas carry side conditions;
  `omega` knows truncation.
- `ℤ` (`Int`): ordinary integers. Division `/` rounds toward −∞ for positive divisors
  (`Int.ediv`), so `⌈a/b⌉ = (a + b - 1) / b` for `b > 0` — exactly `rankBound`:

  ```lean
  def rankBound (V₀ Δ : ℤ) : ℕ := Int.toNat ((V₀ + Δ - 1) / Δ)
  ```

  `Int.toNat` maps negatives to `0` (the "clipped at 0" of the paper).
- `ℚ` (`Rat`): exact rationals, used for Farkas and potentials in `Certificate`.
- **Casts / coercions**: `(n : ℤ)` or `↑n` turns a natural into an integer. Lean inserts
  them automatically; `push_cast` normalises them. In `ranking_descent` the statement
  `V (f^[k] s₀) ≤ V s₀ - k * Δ` silently casts `k : ℕ` to `ℤ`.
- **Floor**: `⌊x⌋₊` is `Nat.floor x`, the natural floor of a non-negative element of an
  ordered semiring with `FloorSemiring` (ℚ, ℝ). `Nat.le_floor : (n : α) ≤ x → n ≤ ⌊x⌋₊`.
- **Iteration**: `f^[n]` is `Nat.iterate f n` (mathlib): `f^[0] = id`,
  `f^[n+1] = f^[n] ∘ f`. Two lemmas convert: `Function.iterate_succ_apply`
  (`f^[n+1] x = f^[n] (f x)`) and `Function.iterate_succ_apply'`
  (`f^[n+1] x = f (f^[n] x)`).
  Do not confuse with the project's `t ^[n]` for traces (section 10).
- `Nat.find h` for `h : ∃ n, P n` (with `P` decidable) is the **least** such `n`
  (Kleene's μ); `Nat.find_spec h : P (Nat.find h)`; `Nat.find_min h : k < Nat.find h → ¬P k`.

## 9. Type classes and mathlib

A **type class** is like a C++ concept with an implementation found automatically
(instance resolution). Example from `Certificate`:

```lean
variable {S : Type} {α : Type} [LinearOrderedField α]
...
variable [FloorSemiring α]
theorem ranking_bound_floor (step : S → S → Prop) (V : S → α) … : n ≤ ⌊V (σ 0)⌋₊
```

reads: "for any type `α` that is a linearly ordered field and has a floor function". ℚ
and ℝ are instances, so the theorem applies to both. Other classes used:
`[Fintype ι]` (finite type, so `∑ i, f i` makes sense — the sum over all `i : ι`),
`DecidablePred P` (needed by `Nat.find`).

**mathlib** provides the number systems, `Finset.sum` (`∑`), order lemmas
(`le_trans`, `Nat.le_floor`, `Nat.floor_mono`), list lemmas (`List.length_append`,
`List.append_assoc`), and the tactics `omega`, `linarith`, `ring`, `simp` lemma sets,
`interval_cases`, `push_cast`. Finding a lemma: guess its name from mathlib's naming
convention (`List.length_append` = "length of append"), use `#check`, or `exact?`
(asks Lean to search for a closing lemma — slow but useful). The project is pinned to
mathlib `v4.16.0`; online documentation for the current version may name some lemmas
differently.

## 10. Files, namespaces, variables, notation, comments

A typical file (`Trace.lean`):

```lean
/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.      -- block comment
...
-/
import Mathlib.Tactic                     -- dependencies (other modules)

namespace ImperativeOptimization          -- like a C++ namespace; closed by `end ImperativeOptimization`

variable {Instr S : Type}                 -- auto-added as implicit arguments wherever used

/-- The free monoid of finite execution traces ... -/   -- doc comment (attached to next decl)
abbrev Trace (Instr : Type) := List Instr

notation:max t " ^[" n "]" => traceIter t n             -- new syntax: `t ^[n]`
infix:50 " ⊑ " => OrderByComposition                     -- binary operator with precedence 50
```

- `/-! … -/` is a **module doc** comment (in `WhileLoop.lean`, `Ranking.lean`…), `--` a
  line comment.
- `variable {Instr S : Type}`: every later declaration that mentions `Instr` gets it as
  an implicit parameter. The linter warns if a `variable` is included but unused — the
  reason `[FloorSemiring α]` is declared after `run_descent` in `Certificate`.
- `notation`/`infix` only add syntax; the number is the precedence (`50` like `≤`;
  `max` binds tightest).
- **Notation clash** (noted in `CLAUDE.md`): `t ^[n]` (project, traces) vs `f^[n]`
  (mathlib, function iteration). Lean picks by type; write `traceIter t n` if confused.
- `namespace BTree … end BTree` inside a file puts `size`, `graft`, … under `BTree.`;
  `t.size` works by dot notation for `t : BTree α`.
- `open X` makes names of namespace `X` usable without prefix.
- `theorem` vs `def` vs `lemma`: `theorem` for propositions (proof irrelevant), `def` for
  data. (`lemma` is a mathlib synonym of `theorem`; the project uses `theorem`.)
- `instance` declares a type-class instance (`Trace.lean` makes `ExitsAt` decidable).
- Unicode input in VS Code: type `\sqsubseteq` → `⊑`, `\to` → `→`, `\all` → `∀`,
  `\ex` → `∃`, `\N` → `ℕ`, `\Z` → `ℤ`, `\Q` → `ℚ`, `\<>`, `\le` → `≤`, `\l` → `λ`,
  `\<` `\>` → `⟨ ⟩`, `\_0` → `₀`. Hover a symbol to see how to type it.

## 11. Mutual definitions and structural recursion

`Arity.lean` needs trees with *any* number of children. Lean represents children as a
`Forest` (a list of trees), and the two types refer to each other:

```lean
mutual
inductive RTree (α : Type) : Type
  | node : α → Forest α → RTree α
inductive Forest (α : Type) : Type
  | nil : Forest α
  | cons : RTree α → Forest α → Forest α
end
```

Functions and theorems over them are also `mutual` (one for trees, one for forests),
e.g. `RTree.size`/`Forest.size`. Proofs over mutual types are written as **recursive
functions returning proofs** (pattern matching on the tree, calling the forest version
and vice versa), because the `induction` tactic does not handle mutual types directly:

```lean
theorem RTree.size_le_geom (b : ℕ) :
    ∀ (t : RTree α) (d : ℕ), t.BranchLE b → t.depth ≤ d → t.size ≤ geom b d
  | .node _ f, d, hb, hd => by
    ...   -- uses Forest.size_le_geom b f d hf hd   (a "recursive call" = induction hypothesis)
```

Lean checks that the recursion is **structural** (each call is on a sub-term), which is
what makes the "recursive call" a valid induction hypothesis.

## 12. Reading a proof state, and a full worked proof

In the Infoview, a goal looks like:

```
case succ
n : ℕ
ih : 2 * sumTo n = n * (n + 1)
⊢ 2 * sumTo (n + 1) = (n + 1) * (n + 1 + 1)
```

Above `⊢`: context (variables and hypotheses). After `⊢`: what to prove. `case succ`:
which branch of an induction you are in.

Worked example (checked):

```lean
def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

theorem sumTo_formula (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl                                  -- 2 * 0 = 0 * 1, by computation
  | succ n ih =>
    show 2 * (sumTo n + (n + 1)) = (n + 1) * (n + 1 + 1)   -- unfold sumTo (n+1)
    rw [Nat.mul_add, ih]                         -- 2*sumTo n + 2*(n+1), then use ih
    ring                                         -- n*(n+1) + 2*(n+1) = (n+1)*(n+2)
```

Now a real one from the repository, `order_antisymm` (`Trace.lean`), annotated:

```lean
theorem order_antisymm {u w : Trace Instr} (h1 : u ⊑ w) (h2 : w ⊑ u) : u = w := by
  rcases h1 with ⟨r1, hr1⟩          -- h1 : ∃ v, w = u ++ v   gives r1 and hr1 : w = u ++ r1
  rcases h2 with ⟨r2, hr2⟩          -- hr2 : u = w ++ r2
  have len1 : w.length = u.length + r1.length := by rw [hr1, List.length_append]
  have len2 : u.length = w.length + r2.length := by rw [hr2, List.length_append]
  have r1_nil : r1 = [] := List.length_eq_zero.mp (by omega)   -- len1, len2 ⟹ r1.length = 0
  rw [r1_nil] at hr1                -- hr1 : w = u ++ []
  rw [hr1]                          -- goal: u = u ++ []
  exact (List.append_nil u).symm    -- u ++ [] = u, reversed
```

This is exactly the paper's proof ("lengths force the extension to be empty").

## 13. Common errors and what they mean

| Message | Usual cause | Fix |
|---|---|---|
| `unsolved goals` | the tactic block ended with goals left | look at the Infoview at the end of the block |
| `type mismatch` | the term proves something slightly different (e.g. `a + b` vs `b + a`, a missing cast) | `show` the expected form, `rw`/`simp`/`push_cast`, or `omega` |
| `rewrite failed, did not find instance of the pattern` | `rw` needs the *syntactic* pattern; it may be hidden behind a definition | `show`/`dsimp`/`unfold` first |
| `linarith failed` | not linear, or a needed fact is not in the context, or not beta-reduced | `have` the missing fact; `show` a beta-reduced goal (this happened in `farkas_sound_affine`) |
| `omega could not prove the goal` | non-linear term (`x * y`), or a fact about a function value `omega` does not see | introduce the product as a variable with `have`, or use `nlinarith` |
| `unknown identifier` / `unknown constant` | lemma renamed in this mathlib version, or namespace not open | `#check`, `exact?`, search mathlib at tag v4.16.0 |
| `failed to synthesize instance` | a type-class assumption is missing (e.g. `Decidable`) | add `[inst]` or `classical` |
| `declaration uses 'sorry'` (warning) | an unfinished proof | **never commit**; the project policy is zero `sorry` |
| `unused variable` (linter) | hypothesis not used | prefix with `_` (`_h_dec`) or remove |

## 14. Exercises

Do them in a scratch file; each takes 5–30 minutes and uses only what is above.

1. Prove `cost (traceIter [7, 8, 9] 4) = 12` using `cost_iter`.
   *(Solution: `by rw [cost_iter]; rfl`.)*
2. Prove that the empty trace is below every trace: `([] : Trace ℕ) ⊑ t`.
   *(Hint: the extension is `t`.)*
3. State and prove `t ⊑ t ++ u` for all traces.
4. Using `ranking_bound`, prove that the loop `while (x > 0) x -= 3` (state `ℤ`,
   `cond x = decide (x > 0)`, `f x = x - 3`) runs at most `rankBound x₀ 3` times.
   *(Model on `parametric_loop_ranking` in `Examples.lean`.)*
5. Define `BTree.leftDepth` (depth along leftmost branch) and prove
   `t.leftDepth ≤ t.depth` by induction on `t`.
6. Read `exec_least` (`Recursion.lean`) with the Infoview and write in plain words what the
   goal is after `cases t' with | leaf b`.
7. Run `#print axioms` on three theorems of your choice and check only the three standard
   axioms appear.
