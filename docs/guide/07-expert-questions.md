# Part 7 — Talking to experts

Short answers to say, then point to a label or a Lean name. Where the honest answer is a
limitation, it says so.

## 1. The pitch (60 seconds)

> "Order execution traces by prefix: the run of a loop is the least power of the body
> whose final state fails the guard — a minimisation, which we prove equal to big-step
> semantics in Lean, also for recursion with trees. Exact solutions are rare, so we relax:
> ranking potentials bound iterations, the timing schema composes costs, and a cost logic
> for a small language with procedures and contracts is proved sound, including for
> diverging runs. Its linear instance has certificates that a small verified checker
> validates with integer arithmetic. A Clang plugin emits such certificates for real-time
> C/C++: on TACLeBench, 142 of 158 bounded functions are certified. The ingredients are
> classical; the contribution is the end-to-end, machine-checked chain."

## 2. Semantics and programming languages

- **"Minimal exiting trace is just the μ-operator."** Yes — the paper says so
  (Positioning). The point is the uniform formulation (loops, linear and branching
  recursion) with a proved link to big-step semantics (`while_trace_semantics`,
  `treeBigStep_iff`).
- **"What about divergence?"** In Paper I's cost logic, triples bound every *prefix*
  (`Pre`), so a derivable bound with positive test weights excludes divergence. The
  minimisation view sees divergence as infeasibility (`infinite_loop_diverges`).
- **"Is the tree order known?"** It is the prefix order on trees by leaf substitution;
  binary in Lean, any arity on paper.
- **"Expressiveness?"** Structured control flow over scalar state; no heap, no aliasing, no
  concurrency in the theory. The plugin adds calls (contexts; inlining for certificates)
  and rejects the rest.

## 3. Termination and bound analysis

- **"What is new compared with SPEED, KoAT, Loopus, COSTA, C4B?"** Not the bounds: affine
  potentials by Farkas are standard. New: certificates checked by a Lean-verified checker,
  and the evaluation against executions. On TPDB, KoAT2 and CoFloCo are clearly stronger
  (288 and 264 programs, against 165 with input ranges): say so first.
- **"Which ranking functions?"** Affine, rational, per loop, synthesised by LP.
  Lexicographic and logarithmic potentials exist as theorems (`prop:lex-log`), not yet in
  the plugin or the checker.
- **"Integers vs rationals?"** Rational potentials over integer programs are sound
  (`ranking_bound_floor`); incomplete for integer-only arguments (Ben-Amram & Genaim).
- **"Invariants?"** Houdini over simple candidates, each proved inductive by Z3; in
  certificates, re-justified for the checker.
- **"Amortisation?"** None: nested loops multiply, merge sort is quadratic.
- **"Is your cost logic new?"** No: Nielson 1987; Haslbeck & Nipkow mechanised three such
  logics, sound *and* complete, for deterministic IMP. Here: soundness only, but
  nondeterministic atoms, bounds on prefixes, and a loop rule shaped like the analyser's
  certificate.

## 4. WCET and real-time

- **"Is this a WCET tool?"** No. It gives loop bounds and path costs in abstract units.
  Time needs per-instruction worst-case durations, which exist only for simple cores
  without caches; otherwise the loop bounds should be exported to a timing analyser
  (future work).
- **"Why the timing schema and not IPET?"** Structured code and compositionality. It
  ignores infeasible paths — although certificates do exclude some (`__kernel_cosf`).
- **"Evaluation?"** TACLeBench kernels without annotations: in context, 137 of 220 loops
  bounded, 128 equal to the flow facts; no bound below an observed loop count; identical
  to oRange on all 113 loops both bound; ScalarEvolution, KoAT2, CoFloCo and Infer compared
  too. Caveats: small kernels, untuned tools, flow facts that hold for one input.
- **"oRange gives a wrong bound?"** On `filterbank` (`while (n-- > 0)` with `n = 2`, it
  reports 1): an observation to confirm with its authors, not an attack.
- **"Interrupts, preemption, multicore?"** Out of scope: CrossCheck bounds one task's
  sequential code; schedulability analysis consumes such bounds.

## 5. Formal methods and Lean

- **"What exactly is machine-checked?"** Everything in Paper I's Table `tab:lean`: the
  equivalences, orders and envelopes, the cost logic (`soundness`), the checker
  (`check_sound`), the examples. 185 theorems, no `sorry`, three standard axioms.
- **"What is not?"** General arity for the tree order; termination for relations; the
  equation rules; Farkas completeness; the parallelism paragraph; lex/log as rules; the
  translation from C/C++; the plugin.
- **"Is the checker program the verified one?"** It is the Lean definition `check`,
  compiled by Lean's compiler. The JSON parser around it is not verified, and `--print`
  shows what was checked. Trusted: Lean's compiler and runtime, the parser, and the
  lowering from C++ to the certificate's program.
- **"Is this proof-carrying code?"** For cost bounds, yes in structure: an untrusted
  producer and a small verified consumer.

## 6. C++ and compiler engineering

- **"Why a plugin?"** It sees templates, `constexpr` and inline library code, and it fails
  the build. Calls are followed into their definitions, standard library headers included.
- **"Undefined behaviour?"** Signed overflow is assumed absent; unsigned results are used
  only when proved not to wrap; certificates use only signed variables.
- **"The optimiser changes the code."** The cost is computed on the source; bounds on loop
  counts remain true for the compiled code, unit costs do not.
- **"Industrial code?"** A MISRA- or AUTOSAR-style subset is the realistic target; globals,
  structs, pointers as iterators and floats are not tracked yet.

## 7. AI use

Most code, proofs and text were written by an AI assistant at the author's request; every
prompt is in `AI_USAGE.md`; the papers carry `\authortodo` marks wherever the author must
verify, and must not be submitted while one remains.

## 8. Known weak points, ranked

1. **Translation gap**: certificates are checked; the C++ → certificate lowering is not.
2. **Coverage**: 165 of 553 TPDB programs vs 288 for KoAT2; no symbolic bounds in the
   plugin.
3. **Novelty in the packaging** for the theory; the checker and the evaluation are the
   stronger points.
4. **Precision**: affine potentials, no amortisation.
5. **Cost is not time.**
6. **Evaluation size**: small kernels; no industrial code base yet.

## 9. Phrases

| Prefer | Avoid |
|---|---|
| "sound bound under the listed assumptions" | "guaranteed WCET" |
| "cost in abstract units" | "execution time" |
| "certified: accepted by a checker proved sound in Lean" | "the plugin is verified" |
| "machine-checked, no axioms beyond Lean's three standard ones" | "fully verified", "zero axioms" |
| "the timing schema read in (max,+)" | "our tropical algebra" |
| "a time Hoare logic in the tradition of Nielson" | "a new logic" |

## 10. Glossary

| Term | Meaning |
|---|---|
| Activation | one execution of a function call |
| Affine | linear plus a constant |
| Big-step semantics | initial state ⇓ final state, by inference rules |
| Certificate | program + assertions + potentials + Farkas multipliers, checkable without search |
| Context | constraint on the initial state (e.g. argument intervals at a call site) |
| Cost envelope | the papers' term for a sound upper bound on cost |
| Cost triple | `{P} c {Q}↓B` |
| Entailment | facts ⊨ goal |
| Farkas multipliers | `(μ, λ)` with `μ·g = Σ λᵢ pᵢ + r` and a constant `r ≤ 0` |
| Flow fact | a loop bound or path constraint for a WCET analyser |
| Logical (ghost) variable | a variable of assertions that no program changes (`γⱼ`) |
| Havoc | assignment of an unknown value |
| Houdini | drop non-inductive candidates until a fixed point |
| In context / for every call | bound for the program's actual calls / for any admissible call |
| Inductive invariant | holds initially and is preserved by an iteration |
| Order-by-composition ⊑ | prefix order on traces (and trees) |
| Prefix (`Pre`) | a possibly unfinished execution |
| Ranking potential | decreases by ≥ 1 per step, and is ≥ 1 while running |
| Size potential | `U(x) ≥ 1 + Σ U(children)`: bounds the number of calls |
| Timing schema | sum / max / bound × body |
| Tropical semiring | ⊕ = max, ⊗ = + |
| Weaken | consequence rule: stronger precondition, weaker postcondition, larger bound |
