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
> C/C++: on the TACLeBench kernels, 158 of 162 bounded functions are certified. The ingredients are
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
  (288 and 264 programs, against 207 with input ranges, or 101 certified for all inputs without ranges): say so first.
- **"Which ranking functions?"** Affine, rational, per loop, synthesised by LP; and
  logarithmic ones on a single variable, decreasing (`n >>= 1`, `n /= 10`) or growing to a
  limit (`len <<= 1`), in the plugin and as checker nodes (`whileLog`, `whileGrow`, proved
  by reduction to the linear loop rule). A lexicographic pair with a bounded inner counter is one affine potential
  (`lex_potential`): the plugin finds it once the inner counter's bounds are invariants (a
  retry with more candidates), and certifies it with the ordinary `while` node. With a
  symbolic inner bound the cost is a product: not covered. Binary search (a difference of
  two variables halves) gets a linear bound.
- **"Integers vs rationals?"** Rational potentials over integer programs are sound
  (`ranking_bound_floor`); incomplete for integer-only arguments (Ben-Amram & Genaim).
- **"How do you know the analyser is sound, since it is not verified?"** We don't prove
  it; we test it against executions: benchmark runs, and random loop programs
  (`fuzz_bounds.py`: in the last campaign, no violation in 960 functions, 863 bounded
  loops and 1.23 million runs, after a first defect was fixed). Certified bounds don't
  depend on it; the checker executable is tested with mutated certificates (2,029
  mutants: 1,983 rejected, the other 46 still true on executions).
- **"Invariants?"** Houdini over simple candidates, each proved inductive by Z3; when no
  potential is found, a second set (branch tests as they are and relaxed by one, hulls of
  assigned constants, pairs left equal). In certificates they are hints, proved again for
  the checker.
- **"Amortisation?"** None: nested loops multiply, merge sort is quadratic.
- **"Is your cost logic new?"** No: Nielson 1987; Haslbeck & Nipkow mechanised three such
  logics, sound *and* complete, for deterministic IMP. Here: soundness only, but
  nondeterministic atoms, bounds on prefixes, and a loop rule shaped like the analyser's
  certificate.

## 4. WCET and real-time

- **"Is this a WCET tool?"** Not in general. It gives loop bounds and path costs in
  abstract units, and exports the loop bounds for aiT and OTAWA (OTAWA computes bounds
  for the 107 bounded functions of the Cortex-M0 binaries from them: `run_otawa.py`). For one predictable core,
  the Cortex-M0 (no cache, fixed timings), `benchmarks/cycles` turns them into cycle bounds
  of the compiled code, checked against an interpreter's cycle counts; the timing table is
  compared row by row with Table 3-1 of Arm's manual (`test_m0.py`) and not checked on
  hardware.
- **"Why the timing schema and not IPET?"** Structured code and compositionality. It
  ignores infeasible paths — although certificates do exclude some (`__kernel_cosf`).
- **"Evaluation?"** TACLeBench kernels without annotations: in context, 141 of 220 loops
  bounded, 131 equal to the flow facts; no bound below an observed loop count; identical
  to oRange on all 114 loops both bound; ScalarEvolution, KoAT2, CoFloCo and Infer compared
  too. Caveats: small kernels, untuned tools, flow facts that hold for one input.
- **"oRange gives a wrong bound?"** On `filterbank` (`while (n-- > 0)` with `n = 2`, it
  reports 1): an observation to confirm with its authors, not an attack.
- **"Interrupts, preemption, multicore?"** Interrupts: handlers annotated
  `CROSSCHECK_INTERRUPT(T)` give each other function a response time (the classical
  response-time equation, mechanized as `response_time_bound`; the checker verifies the
  claim from certified bounds). Assumptions: minimum inter-arrival times, cost = time, no
  activation pending at the start. Fork-join: Graham's bound in Lean only. Multicore
  interference (shared caches, buses): out of scope.
- **"Rust?"** A front-end translates the textual MIR of rustc 1.100 into C for the same
  analyser; checked by a differential test against Rust, not verified; bounds hold for
  executions that do not panic. The MIR text format changes between releases.

## 5. Formal methods and Lean

- **"What exactly is machine-checked?"** Everything in Paper I's Table `tab:lean`: the
  equivalences, orders and envelopes, the cost logic (`soundness`), the checker
  (`check_sound`), validation against mini-C (`validated_sound`), response times under interrupts (`response_time_bound`), Graham's
  fork-join bound (`greedy_bound`), logarithmic loops in the checker (`logloop_sound`, `growloop_sound`), the examples. 279 theorems, no `sorry`, three standard axioms.
- **"What is not?"** General arity for the tree order; termination for relations; the
  equation rules; Farkas completeness; the parallelism paragraph; lex/log as rules; the
  translation from C/C++ (to certificates, or to mini-C for validated ones); the plugin.
- **"Why should I trust the certificate generator?"** You need not, for a validated
  certificate: the checker compares the certificate's program with the function's mini-C
  export (`--opt=minic`), and `validated_sound` transfers the bound. What you trust then is
  the exporter (`MiniC.cpp`, syntactic, a few hundred lines) and the cost model.
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
verify, and must not be submitted while one remains. On 2026-11-16 the assistant did the
checks that a script or a document could settle (definitions against Lean, the Cortex-M0
timing table, the loop instrumentation, parts of 14 cited papers; `AI_USAGE.md`, prompt 45
and section 3, item 33). The marks that remain: the two statements of responsibility,
the papers that could not be obtained (Nielson 1987, Necula 1997, Joseph and Pandya 1986
and a few of Paper II), the descriptions of KoAT2, CoFloCo and oRange, and the fairness
of the TPDB harness.

## 8. Known weak points, ranked

1. **Translation gap**: certificates are checked; the C++ → certificate lowering is not.
   For the functions whose certificate is validated against their mini-C export, the
   generator is out of the trusted base, the exporter (syntactic) is in it.
2. **Coverage**: 207 of 553 TPDB programs with input ranges (101 certified for all inputs without) vs 288 for KoAT2. Certificates give summaries
   affine in the parameters; since option `symbolic` the analyser can propose potentials
   without ranges and the certificate carries the parametric bound, but only for bounds
   affine in the parameters (no products).
3. **Novelty in the packaging** for the theory; the checker and the evaluation are the
   stronger points.
4. **Precision**: affine and logarithmic potentials, lexicographic ones only with a
   constant inner bound, no amortisation.
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
