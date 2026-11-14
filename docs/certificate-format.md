# Cost certificate format (version 1)

A certificate file is read by `crosscheck-check`
(`formalization/CheckerMain.lean`), which converts it into the Lean type
`Checker.ACmd` and runs the verified function `Checker.check`
(`formalization/ImperativeOptimization/CheckerCore.lean`; soundness:
`Checker.check_sound` in `Checker.lean`, paper `thm:checker-soundness`). The Clang
plugin writes this format with `--opt=certificates=FILE` (tool) or
`-fplugin-arg-crosscheck-certificates=FILE` (plugin).

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
| `while w g inv pot d k j posCert Wb body` | invariant, potential `pot/d`, entry bound `k`, logical variable `j`, certificate of `pot ≥ d`, body bound | `d ≥ 1`; `P = (pot − k ≤ 0) :: inv`; `Q = (1 − g ≤ 0) :: inv`; `γⱼ` not in `inv`; `posCert` proves `d − pot ≤ 0` from `g :: inv`; body accepted from `(pot − γⱼ ≤ 0) :: g :: inv` to `(pot + d − γⱼ ≤ 0) :: inv` with bound `Wb`; `B = ⌊k/d⌋·(w + Wb) + w` |
| `whileAnd w gs inv pot d k j posCert Wb body` | as `while`, with a list of tests `gs` (the loop runs while every `g ≤ 0`) | as `while` with `g :: inv` replaced by `gs ++ inv` (each `g` as the constraint `g ≤ 0`), except `Q = inv`: the negation of a conjunction is not an assertion |
| `weaken P' preCerts B' Q' postCerts c` | inner triple and certificates | `P ⊢ P'` and `Q' ⊢ Q` constraint by constraint, `B' ≤ B`, `c` accepted for the inner triple |
| `dead cert c` | certificate | `P ⊢ 1 ≤ 0` |

Syntactic equalities (`P = …`) are exact list equalities: the emitter must produce the
vectors the checker computes (e.g. for `assign`, apply the same substitution as
`Lin.subst`), or wrap the node in a `weaken`. `countCert` in `Checker.lean` is a complete
worked example; use it as the first test.

JSON field names: `skip`; `assign {w, x, a}`; `havoc {w, x}`; `seq {c1, mid, B1, B2, c2}`;
`ite {w, g, B1, B2, c1, c2}`; `while {w, g, inv, pot, d, k, j, posCert, Wb, body}`;
`whileAnd {w, gs, inv, pot, d, k, j, posCert, Wb, body}`;
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
- **Calls** are inlined (the callee's body, in the calling context the analysis used);
  arguments are bound to the callee's parameters.
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
statements, recursion, calls to functions without an analysed body
(trusted costs), `CROSSCHECK_ASSUME` / `LOOP_BOUND`, globals, struct fields and pointer
counters (not tracked by the analysis either).

What a certificate does **not** say: that its program is the C/C++ function. The
lowering is unverified; the checker verifies the certificate's program.
