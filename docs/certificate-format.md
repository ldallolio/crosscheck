# Cost certificate format (versions 1 and 2)

A certificate file is read by `crosscheck-check`
(`formalization/CheckerMain.lean`), which converts it into the Lean type
`Checker.ACmd` and runs the verified function `Checker.check`
(`formalization/ImperativeOptimization/CheckerCore.lean`; soundness:
`Checker.check_sound` in `Checker.lean`, paper `thm:checker-soundness`). The Clang
plugin writes this format with `--opt=certificates=FILE` (tool) or
`-fplugin-arg-crosscheck-certificates=FILE` (plugin).

Version 2 (written by the plugin): one *program certificate* per translation unit, a list
of functions that share one variable table (Lean `FunCert`, checked by `checkProgram`,
soundness `Checker.program_sound`, paper `thm:program-soundness`):

```json
{ "format": "crosscheck-certificates", "version": 2,
  "programs": [
    { "name": "file.cpp", "variables": ["?choice", "?cost", "sum::n", "sum::i", ...],
      "functions": [
        { "name": "sum", "pre": [ <Lin>... ], "bound": {"c": 5, "co": [7]}, "post": [],
          "mods": [3, 4], "body": <node> },
        { "name": "contract hal_read", "pre": [], "bound": 25, "post": [], "mods": [],
          "contract": true } ] } ] }
```

A function may call only the functions before it (no recursion). A function with
`"contract": true` and no body is an **assumed contract**: `crosscheck-check` prints it as
`ASSUMED` and the verdict of the program (`PROGRAM … ACCEPTED (relative to the assumed
contracts)`) holds only if the contracts hold. Every function's body must modify only its
`mods` (checked).

Version 1 (still read): a list of standalone certificates without calls:

```json
{ "format": "crosscheck-certificates", "version": 1,
  "certificates": [
    { "function": "f", "variables": ["?choice", "?cost", "n", "i"],
      "pre": [ <Lin>... ], "bound": 21, "post": [ <Lin>... ],
      "program": <node> } ] }
```

`variables` only names the indices for printing (`crosscheck-check --print`). Missing
`sv`/`lv` fields mean the empty list. `test/certificates/count.json` is a complete
example (a single loop, and a loop with a conjunctive test); every certificate of
`count_rejected.json` (five) must be rejected.

## Contents

The checker's input is the Lean type `ACmd` of
`formalization/ImperativeOptimization/Checker.lean`, with a precondition, a bound and a
postcondition. Everything is integer data:

- **Variables** are numbered `0, 1, 2, …`. The emitter assigns a number to every tracked
  program variable of the function (parameters first) and keeps the table in the
  certificate for readability.
- **`PExp`** `{sv, c}`: the affine expression `Σ sv[i]·xᵢ + c` (dense coefficient list).
- **`Lin`** `{sv, lv, c}`: an affine form over program variables (`sv`) and logical
  variables (`lv`); as a constraint it means `≤ 0`. An assertion is a list of `Lin`.
- **Symbolic bound** (Lean `SB`): a natural number, or `{c, co}` meaning
  `c + Σ co[j]·max(0, γⱼ)` with natural coefficients over the logical variables. A
  function's precondition contains `x_p = γ_p` for its parameters, so its bound is a
  *summary* in its parameters. Bounds are compared coefficient by coefficient (`SB.le`).
- **Farkas certificate** `(mu, lam)`: `mu ≥ 1` and one multiplier per premise, in the
  order of the premise list, such that `mu·goal − Σ lam[i]·premise[i]` is a constant
  `≤ 0`. Z3 gives rational multipliers: multiply by the common denominator.
- **Nodes** (`ACmd`):

| Node | Fields | Accepted when |
|---|---|---|
| `skip` | – | `P = Q`, `B = 0` |
| `assign w x a` | weight, variable, `PExp` | `P = Q[a/x]` (syntactically, constraint by constraint), `B = w` |
| `havoc w x` | weight, variable | `P = Q`, `x` does not occur in `Q`, `B = w` |
| `seq c₁ mid B₁ B₂ c₂` | intermediate assertion, two bounds | both parts accepted, `B = B₁ + B₂` |
| `ite w g B₁ B₂ c₁ c₂` | test `g ≤ 0`, two bounds | `c₁` accepted from `g ≤ 0 :: P`, `c₂` from `1 − g ≤ 0 :: P`, `B = w + max B₁ B₂` |
| `while w g inv pot d k kl j posCert Wb body` | invariant, potential `pot/d`, entry bound `K = k + Σ kl[i]·γᵢ` (`kl` optional), logical variable `j`, certificate of `pot ≥ d`, body bound | `d ≥ 1`; `P = (pot − K ≤ 0) :: inv`; `Q = (1 − g ≤ 0) :: inv`; `γⱼ` neither in `inv` nor in `Wb`; `posCert` proves `d − pot ≤ 0` from `g :: inv`; body accepted from `(pot − γⱼ ≤ 0) :: g :: inv` to `(pot + d − γⱼ ≤ 0) :: inv` with bound `Wb`; either `kl = 0` and `B ≥ ⌊k/d⌋·(w + Wb) + w`, or `Wb` constant, `B.c ≥ w`, `(w+Wb)·k ≤ d·(B.c − w)` and `(w+Wb)·kl ≤ d·B.co` (`loopBoundOk`) |
| `whileAnd w gs inv pot d k j posCert Wb body` | as `while`, with a list of tests `gs` (the loop runs while every `g ≤ 0`) | as `while` with `g :: inv` replaced by `gs ++ inv` (each `g` as the constraint `g ≤ 0`), except `Q = inv`: the negation of a conjunction is not an assertion |
| `call w f inst preCerts ubs ubCerts` | callee index `f` (an earlier function), expressions `inst[j]` for the callee's `γⱼ`, certificates of its precondition, symbolic bounds `ubs[j]` of `inst[j]` in the caller's `γ` with their certificates | `preCerts` prove the callee's `pre` with `γⱼ := inst[j]` from `P`; `ubCerts` prove `inst[j] ≤ ubs[j]`; `len(callee.co) ≤ len(ubs) ≤ len(inst)`; `B ≥ w + callee.c + Σ callee.co[j]·ubs[j]`; `Q` = the constraints of `P` that do not mention the callee's `mods` |
| `weaken P' preCerts B' Q' postCerts c` | inner triple and certificates | `P ⊢ P'` and `Q' ⊢ Q` constraint by constraint, `B' ≤ B`, `c` accepted for the inner triple |
| `dead cert c` | certificate | `P ⊢ 1 ≤ 0` |

Syntactic equalities (`P = …`) are exact list equalities: the emitter must produce the
vectors the checker computes (e.g. for `assign`, apply the same substitution as
`Lin.subst`), or wrap the node in a `weaken`. `countCert` in `Checker.lean` is a complete
worked example; use it as the first test.

JSON field names: `skip`; `assign {w, x, a}`; `havoc {w, x}`; `seq {c1, mid, B1, B2, c2}`;
`ite {w, g, B1, B2, c1, c2}`; `while {w, g, inv, pot, d, k, j, posCert, Wb, body}`;
`whileAnd {w, gs, inv, pot, d, k, j, posCert, Wb, body}` (both with an optional `kl`);
`call {w, f, inst, preCerts, ubs, ubCerts}`; bounds `B1`, `B2`, `Wb`, `B`, `bound`, `ubs[j]` are
symbolic bounds;
`weaken {P, preCerts, B, Q, postCerts, c}`; `dead {cert, c}`; a Farkas certificate is
`{mu, lam}`; `PExp` is `{sv, c}`; `Lin` is `{sv, lv, c}`.


## How the plugin produces certificates

`src/analysis/Analyzer.cpp`, section "Certificates", and `src/core/Cert.{hpp,cpp}`:

- **Variables**: the tracked integer variables (signed or unsigned) that can influence control
  (those of tests and loop potentials, closed under the assignments and argument
  passing that feed them); index 0 is a variable for nondeterministic tests, index 1 a
  variable that no assertion mentions (statements that only cost are unknown values
  given to it). Other variables are not part of the certificate.
- **Assertions** are computed forwards (strongest postconditions, Fourier–Motzkin);
  every step is wrapped in `weaken` with Farkas multipliers found by Z3 and turned into
  integers. Joins after a conditional keep the constraints implied by both branches.
- **Loops** use the potential found by the analysis (scaled to integers), an invariant
  found by Houdini over the entry constraints, and the entry bound computed by Z3.
- **Calls** of a function that already has its own certificate (an earlier root of the
  translation unit) become `call` nodes: the callee's parameters (its variables) receive the
  arguments, its precondition is proved, and each argument is bounded by a symbolic bound
  of the caller's parameters (if one is no looser than a constant at the largest admissible
  arguments) or by a constant. Otherwise the callee's body is inlined in its calling
  context, as before.
- **Summaries**: in a function with parameters, the potential suggested by the loop test
  (`n − i` for `i < n`) is tried before the analysis' potential (which may use the range,
  `64 − i`); the entry bound is symbolic (`symbolicUpper`: Fourier–Motzkin projection on
  the potential and the parameters' logical variables) when the body bound is constant and
  the symbolic bound is no looser than the constant one at the largest admissible
  parameters. The report gives `certificate_summary` (e.g. `5 + 7*max(0,n)`) and
  `certificate_bound` (its value at those parameters).
- **Contracts**: `CROSSCHECK_COST(n)` functions and the functions of a contract file
  (`docs/contracts.md`) are contract entries (`"contract": true`); a contract with a cost per
  argument has variables for those arguments and `x = γ` in its precondition.
- **Early returns** are restructured: the statements after `if (c) return ...;` become
  the other branch (more generally, the rest of a list moves into the branches of any
  conditional or block that may leave it).
- **Early exits from loops**: each loop that needs them gets flag variables
  `?break<j>` and `?continue<j>`, and the function a flag `?return`; a jump sets its
  flag to 1. The rest of the body after a statement that may jump runs under `if (flag
  ≤ 0)`; the increment of a `for` runs unless `break` or `return` was taken; the loop
  test is the conjunction of the C test and `flag ≤ 0` for the `break` and `return`
  flags (node `whileAnd`), and after a loop containing a `return` the rest of the list
  is guarded by `?return ≤ 0`. The iteration that leaves through a flag does not
  decrease the C potential, so the potential becomes `pot + c·(1 − Σ flags)` for the
  first `c` in `d, 2d, …, 64d` that the checker's conditions accept; the invariant
  contains `0 ≤ flag ≤ 1`. A callee inlined inside a loop gets its own flags.
- **`switch`**: a cost atom for the test, then one conditional per group of cases,
  `havoc ?choice; if (?choice ≤ 0) group else skip` (the cases are taken
  nondeterministically, which is sound); fall-through is the sequence of groups; `break`
  in a case ends the group (the rest of the group moves into the branches). Case labels
  nested in other statements (Duff's device) are refused.
- **`&&` loop tests** become the list of a `whileAnd` node; a conjunct that is not a
  linear comparison (`||`, `!=`, a memory read) is replaced by a choice variable
  `?test<j>` havocked before the test.
- **Unsigned variables** of width w: the plugin computes an affine `a` congruent to the
  stored value modulo 2^w (sums, differences and multiples, through conversions that
  keep values or reduce modulo at least 2^w), and emits
  `if (a ≤ 2^w − 1) { if (0 ≤ a) x := a else havoc x } else havoc x` (tests of weight 0;
  `2^62` instead of `2^64 − 1` for 64-bit types, which also excludes wrap-around). The
  checker proves the wrapping branches dead where they are; nothing about wrap-around is
  trusted. Values are exact only through value-preserving conversions; a comparison of a
  signed and an unsigned operand that changes values is a nondeterministic test.
  Unsigned parameters get `0 ≤ x` (and `x ≤ 2^w − 1` for w ≤ 32) in the precondition.
- The weights are those of the plugin's cost model, so the certified bound equals the
  plugin's bound unless the certificate prunes an infeasible path (lower) or the entry
  bound of a loop is rounded up (higher).

Outside the fragment (the report says why): `do`, `goto`, case labels inside nested
statements, recursion, calls to functions without a body or contract,
`CROSSCHECK_ASSUME` / `LOOP_BOUND`, loops whose entry bound and body bound are both
symbolic (a quadratic bound) when no constant entry bound exists, globals, struct fields
and pointer counters (not tracked by the analysis either).

What a certificate does **not** say: that its program is the C/C++ function. The
lowering is unverified; the checker verifies the certificate's program.
