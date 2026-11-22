# Part 9 — Talking to experts

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
> C/C++: on the TACLeBench kernels, 161 of 165 bounded functions are certified. On the compiled
> binaries for a Cortex-M0, cycle bounds are certified on the machine code itself, the
> checker decoding the code and, for many loops, re-proving the loop bounds on the
> instructions. The ingredients are classical; the contribution is the end-to-end,
> machine-checked chain."

## 2. Semantics and programming languages

- **"Minimal exiting trace is just the μ-operator."** Yes — the paper says so
  (Positioning). The point is the uniform formulation (loops, linear and branching
  recursion) with a proved link to big-step semantics (`while_trace_semantics`,
  `treeBigStep_iff`).
- **"What about divergence?"** In Paper I's cost logic, triples bound every *prefix*
  (`Pre`), so a derivable bound with positive test weights excludes divergence. The
  minimisation view sees divergence as infeasibility (`infinite_loop_diverges`).
- **"Is the tree order known?"** Yes: Courcelle's order on trees (1983, Section 2.4), on
  finite trees, with the leaf in the role of the undefined tree Ω; binary in Lean, any arity
  on paper. On traces, ⊑ is the ordinary prefix order. Paper I says it *uses* them.
- **"Expressiveness?"** Structured control flow over scalar state; no heap, no aliasing, no
  concurrency in the theory. The plugin adds calls (contexts; inlining for certificates)
  and rejects the rest.

## 3. Termination and bound analysis

- **"What is new compared with SPEED, KoAT, Loopus, COSTA, C4B?"** Not the bounds: affine
  potentials by Farkas are standard. New: certificates checked by a Lean-verified checker,
  and the evaluation against executions. On TPDB, KoAT2 and CoFloCo are clearly stronger
  (288 and 264 programs, against 207 with input ranges, or 103 certified for all inputs without ranges): say so first.
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
- **"Amortisation?"** Two shapes, in certificates only: a triangular nest whose inner loop
  runs from the outer counter to a constant limit (Lean `triOk`, `valid_whileSum`) or from
  `0` to the outer counter (node `whileUp`, `valid_whileMono`) gets the sum bound (Paper I
  `prop:amortised-loop`). The analyser itself multiplies; merge sort, entry bounds in
  parameters and outer bodies with both shapes are not amortised. **"Is this new?"** No:
  Nielson's 1987 while rule already takes the loop's time as a solution of a recurrence in
  the unfoldings and derives bubble sort's triangular sum with it; summation over
  non-rectangular nests is in Healy et al. 2000 (WCET, after Sakellariou), and arithmetic
  sequences of iteration costs in Albert, Genaim, Masud 2011 (cost analysis). What is ours
  is the checker case with its Lean proof. Atkey 2010 is the closest design: amortised
  resources in a separation logic proved sound in Coq, annotations found by linear
  programming.
- **"Is your cost logic new?"** No: Nielson 1987; Haslbeck & Nipkow mechanised three such
  logics, sound *and* complete, for deterministic IMP. Here: soundness only, but
  nondeterministic atoms, bounds on prefixes, and a loop rule shaped like the analyser's
  certificate.

## 4. WCET and real-time

- **"Can I write budgets in microseconds?"** Yes, `CROSSCHECK_DEADLINE_US(n)`, but it is
  checked after compilation on the binary (`scripts/crosscheck_link.py`, `--clock-mhz`):
  time belongs to machine code on a processor, not to the source. Processors: Cortex-M0
  (our model, checked against emulated runs) or, through OTAWA, the STM32F4 (Cortex-M4)
  and STM32H7 (Cortex-M7) models of OTAWA (not checked against executions here). The
  binary may be the whole linked program, one plugin report per source file.
- **"Will it finish on real code?"** Each function has a deterministic search budget
  (`budget`, in solver work); past it the analysis is less precise, never unsound, and the
  report says so. Solver answers are cached. The slowest TACLeBench program went from
  38 to about 6 minutes (2,277 s → 376 s) with the same results.

- **"Is this a WCET tool?"** Not in general. It gives loop bounds and path costs in
  abstract units, and exports the loop bounds for aiT and OTAWA (OTAWA computes bounds
  for the 107 bounded functions of the Cortex-M0 binaries from them: `run_otawa.py`). For one predictable core,
  the Cortex-M0 (no cache, fixed timings), `benchmarks/cycles` turns them into cycle bounds
  of the compiled code, checked against an interpreter's cycle counts; the timing table is
  compared row by row with Table 3-1 of Arm's manual (`test_m0.py`) and not checked on
  hardware.
- **"Why the timing schema and not IPET?"** Structured code and compositionality. It
  ignores infeasible paths — although certificates do exclude some (`__kernel_cosf`).
- **"Evaluation?"** TACLeBench kernels without annotations: in context, 142 of 220 loops
  bounded, 131 equal to the flow facts; no bound below an observed loop count; identical
  to oRange on 114 of the 115 loops both bound; ScalarEvolution, KoAT2, CoFloCo and Infer compared
  too. Caveats: small kernels, untuned tools, flow facts that hold for one input.
- **"oRange gives a wrong bound?"** On `filterbank` (`while (n-- > 0)` with `n = 2`, it
  reports 1): an observation, stated as such in Paper II; the author chose not to contact
  oRange's authors before the paper is reviewed.
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
  fork-join bound (`greedy_bound`), logarithmic loops in the checker (`logloop_sound`, `growloop_sound`), the examples; and, for Paper III, the cycle certificates (`cycles_sound`), the machine-code graph (`binary_sound`) and the loop bounds on the code (`data_sound`). 561 theorems in all (451 for Paper I, 110 for Paper III), no `sorry`, three standard axioms.
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

## 6. Machine code (Paper III)

- **"Is your processor model validated?"** Against our own interpreter on every 16-bit
  encoding (decoder, cycles, effects, flags, conditions, stack effects: no difference) and
  against llvm-objdump for decoding; the cycle table against Arm's manual row by row. Not
  against hardware yet: a harness for an STM32F0 board exists (`benchmarks/hardware/hw.py`:
  timer around `main`, compared with the emulator and the certified bound) but has not been
  run on a board. A validated ISA model (Fox and Myreen, HOL4) is the standard to aim at.
- **"How do you know the code in the certificate is the binary?"** We don't prove it: the
  certificate carries a copy of the code region; a deployment would compare it with the
  flashed image (a hash).
- **"Your loop bounds come from the source; the compiler may change loops."** For the loops
  certified on the code, no: the bound is proved on the instructions. For the others, the
  match through debug lines is trusted and checked on emulated runs. That check only sees
  what the runs reach: on GCC's binaries, which inline less (73 calls compared instead of
  11), it found a wrong data model (64-bit `long` in the source analysis) and a wrong match
  of a rotated loop, both invisible on Clang's; both fixed.
- **"Does it work with GCC?"** The plugin reads Clang's AST, so the *source* analysis needs
  Clang. The *binary* side does not care: GCC's Cortex-M0 binaries are bounded and certified
  the same way (`run_cycles.py --gcc`; 107 functions bounded, 112 certified).
- **"Why not CompCert, like Maroneze et al.?"** Their guarantees hold for CompCert's output;
  ours for any compiler's binary, relative to a processor specification. Their analysis is
  verified; our checker is, and the analysis is not.
- **"How does this compare with seL4's WCET work (Sewell, Kam, Heiser)?"** They prove loop
  bounds of the seL4 binary with SMT solvers inside a translation-validation toolchain, with
  C-level facts; we check certificates with a small verified checker, with less of memory
  and no C-level facts. Different trade-off: theirs is more complete on seL4, ours trusts no
  SMT solver.
- **"What are `abi` and `frame`?"** Stated assumptions: callees preserve `r4`–`r7` and SP
  (the calling convention); no other code writes a function's frame (true of C without
  undefined behaviour when the function never takes an address of its frame other than the
  frame pointer r7, used only to load, which the checker verifies syntactically). Without them, fewer loops are certified, never wrong ones.
- **"Why not all loops certified on the code (143–257 of 403 kernel loops, 258 without frame pointers, plus the 116 of the division routines)?"** Counters kept in a
  frame whose address is passed to callees (26 of 265 functions), computed conditions,
  shifts, soft-float comparisons, loops over data in memory, and counters against a parameter
  (`classify_loops.py` groups them). Allowing the
  frame-pointer prologue (`add r7, sp, #i`) when r7 only serves loads raised the count from 175 to 215, exact effects of `NEGS`, `MVNS`, `STM`/`LDM` and literal loads to 229, an exact `LSLS` to 246, disjunctive invariants (an exit on a wrapped-around counter) to 250 and all 116 loops of the division routines, rounding facts on sums with the congruences (loops that count a byte offset up to zero) to 256. The rest keep their source bounds as stated
  assumptions. Congruences (Granger) raised the count from 73–107: compilers turn `i < n`
  into an exit on equality with a byte offset stepped by 4. Potentials with a different
  linear part at each instruction, found by linear programming, added 5–14 more.

## 7. C++ and compiler engineering

- **"Why a plugin?"** It sees templates, `constexpr` and inline library code, and it fails
  the build. Calls are followed into their definitions, standard library headers included.
- **"Undefined behaviour?"** Signed overflow is assumed absent; unsigned results are used
  only when proved not to wrap; certificates use only signed variables.
- **"The optimiser changes the code."** The cost is computed on the source; bounds on loop
  counts remain true for the compiled code, unit costs do not.
- **"Industrial code?"** A MISRA- or AUTOSAR-style subset is the realistic target; globals,
  structs, pointers as iterators and floats are not tracked yet.

## 8. AI use

Most code, proofs and text were written by an AI assistant at the author's request; every
prompt is in `AI_USAGE.md`; the papers carry `\authortodo` marks wherever the author must
verify, and must not be submitted while one remains. On 2026-11-16 the assistant did the
checks that a script or a document could settle (definitions against Lean, the Cortex-M0
timing table, the loop instrumentation, parts of 14 cited papers; `AI_USAGE.md`, prompt 45
and section 3, item 33). By 2026-11-18 the author had provided
copies of the papers that could not be obtained, the assistant had read them, and the author
had written the statements of responsibility of Papers I and II; Paper III still carries
one `\authortodo` (responsibility, and three attributions).

## 9. Known weak points, ranked

1. **Translation gap**: certificates are checked; the C++ → certificate lowering is not.
   For the functions whose certificate is validated against their mini-C export, the
   generator is out of the trusted base, the exporter (syntactic) is in it.
2. **Coverage**: 215 of 553 TPDB programs with input ranges (147 certified for all inputs without) vs 288 for KoAT2. Certificates give summaries
   affine in the parameters; since option `symbolic` the analyser can propose potentials
   without ranges and the certificate carries the parametric bound, affine or quadratic
   (no degree above two).
3. **Novelty in the packaging** for the theory; the checker and the evaluation are the
   stronger points.
4. **Precision**: affine and logarithmic potentials, lexicographic ones only with a
   constant inner bound, amortisation only for two triangular shapes in certificates.
5. **Cost is not time.**
6. **Evaluation size**: small kernels; no industrial code base yet.
7. **Processor model** (Paper III): ours, compared with our interpreter, not with hardware
   (board harness written, not yet run).

## 10. Phrases

| Prefer | Avoid |
|---|---|
| "sound bound under the listed assumptions" | "guaranteed WCET" |
| "cost in abstract units" | "execution time" |
| "certified: accepted by a checker proved sound in Lean" | "the plugin is verified" |
| "machine-checked, no axioms beyond Lean's three standard ones" | "fully verified", "zero axioms" |
| "the timing schema read in (max,+)" | "our tropical algebra" |
| "a time Hoare logic in the tradition of Nielson" | "a new logic" |

## 11. Glossary

| Term | Meaning |
|---|---|
| `abi`, `frame` | Paper III's assumptions on callees and on writes to a function's frame |
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
| Ghost operands | Paper III: the two operands of the last flag-setting operation, kept as variables |
| Havoc | assignment of an unknown value |
| Houdini | drop non-inductive candidates until a fixed point |
| In context / for every call | bound for the program's actual calls / for any admissible call |
| IPET | implicit path enumeration: the longest path as a linear program over edge counts |
| Inductive invariant | holds initially and is preserved by an iteration |
| Order-by-composition ⊑ | prefix order on traces (and trees) |
| Prefix (`Pre`) | a possibly unfinished execution |
| Ranking potential | decreases by ≥ 1 per step, and is ≥ 1 while running |
| Size potential | `U(x) ≥ 1 + Σ U(children)`: bounds the number of calls |
| Telescoping | a sum of differences `Σ (π(next) − π(here))` that collapses to `π(end) − π(start)` |
| Timing schema | sum / max / bound × body |
| Tropical semiring | ⊕ = max, ⊗ = + |
| Weaken | consequence rule: stronger precondition, weaker postcondition, larger bound |
| Zone | a set of difference constraints `x − y ≤ c`, closed by shortest paths |
