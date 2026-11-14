/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/

/-!
# The certificate checker: definitions

The executable part of `Checker`, with no dependency beyond Lean's core library, so that
the checker program (`CheckerMain.lean`) can be compiled without mathlib. The proofs about
these definitions are in `ImperativeOptimization.Checker`.

`holds` (an assertion as a proposition) is also defined here because it is the meaning
of the lists of constraints the checker manipulates; it is not used by the program.
-/

namespace ImperativeOptimization.Checker

/-- Valuations of variables. -/
abbrev Env := Nat → Int

/-! ### Dense integer vectors -/

/-- `dot l f = Σᵢ l[i] * f i`. -/
def dot : List Int → Env → Int
  | [], _ => 0
  | a :: l, f => a * f 0 + dot l (fun i => f (i + 1))

/-- Componentwise sum, the shorter vector being padded with zeros. -/
def vadd : List Int → List Int → List Int
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: vadd l m

/-- Multiplication by a scalar. -/
def vsmul (k : Int) (l : List Int) : List Int := l.map (k * ·)

/-- The `i`-th unit vector. -/
def unit : Nat → List Int
  | 0 => [1]
  | i + 1 => 0 :: unit i

/-- The `i`-th coefficient (zero beyond the end). -/
def coeff (l : List Int) (i : Nat) : Int := l.getD i 0

/-- All coefficients are zero. -/
def isZero (l : List Int) : Bool := l.all (fun a => decide (a = 0))

/-- A program expression `Σ sv[i] * xᵢ + c` over the program variables. -/
structure PExp where
  sv : List Int
  c : Int
  deriving DecidableEq, Repr

/-- An affine form over program variables (`sv`) and logical variables (`lv`). As a
    constraint it means `eval ≤ 0`. -/
structure Lin where
  sv : List Int
  lv : List Int
  c : Int
  deriving DecidableEq, Repr

def PExp.eval (a : PExp) (s : Env) : Int := dot a.sv s + a.c

def Lin.eval (e : Lin) (ρ s : Env) : Int := dot e.sv s + dot e.lv ρ + e.c

/-- The guard `a ≤ 0` as a constraint. -/
def PExp.toLin (a : PExp) : Lin := ⟨a.sv, [], a.c⟩

/-- The negation of the guard `a ≤ 0` over the integers: `1 - a ≤ 0`. -/
def PExp.negLin (a : PExp) : Lin := ⟨vsmul (-1) a.sv, [], 1 - a.c⟩

def Lin.add (e f : Lin) : Lin := ⟨vadd e.sv f.sv, vadd e.lv f.lv, e.c + f.c⟩

def Lin.smul (k : Int) (e : Lin) : Lin := ⟨vsmul k e.sv, vsmul k e.lv, k * e.c⟩

/-- Substitution of the expression `a` for the program variable `x`. -/
def Lin.subst (e : Lin) (x : Nat) (a : PExp) : Lin :=
  let k := coeff e.sv x
  ⟨vadd e.sv (vsmul k (vadd a.sv (vsmul (-1) (unit x)))), e.lv, e.c + k * a.c⟩

/-- An assertion is a conjunction of constraints. -/
def holds (A : List Lin) (ρ s : Env) : Prop := ∀ e ∈ A, e.eval ρ s ≤ 0

/-- `Σᵢ lam[i] • ps[i]` (the shorter list decides the length). -/
def comb : List Nat → List Lin → Lin
  | [], _ => ⟨[], [], 0⟩
  | _ :: _, [] => ⟨[], [], 0⟩
  | k :: lam, p :: ps => (p.smul k).add (comb lam ps)

/-- A Farkas certificate `(mu, lam)` for `ps ⊢ g`: `mu > 0` and
    `mu • g - Σ lam[i] • ps[i]` is a non-positive constant. -/
def entails1 (ps : List Lin) (g : Lin) (cert : Nat × List Nat) : Bool :=
  let r := (g.smul cert.1).add ((comb cert.2 ps).smul (-1))
  decide (0 < cert.1) && isZero r.sv && isZero r.lv && decide (r.c ≤ 0)

/-- One certificate per goal. -/
def entailsAll (ps : List Lin) : List Lin → List (Nat × List Nat) → Bool
  | [], [] => true
  | g :: gs, cert :: certs => entails1 ps g cert && entailsAll ps gs certs
  | _, _ => false

/-- An annotated program: the program together with everything the checker needs. -/
inductive ACmd where
  | skip : ACmd
  /-- `x := a`, at cost `w`. -/
  | assign (w : Nat) (x : Nat) (a : PExp) : ACmd
  /-- `x := ?` (an unknown value), at cost `w`. -/
  | havoc (w : Nat) (x : Nat) : ACmd
  /-- `c₁ ; c₂` with the intermediate assertion and the two bounds. -/
  | seq (c₁ : ACmd) (mid : List Lin) (B₁ B₂ : Nat) (c₂ : ACmd) : ACmd
  /-- `if (g ≤ 0) c₁ else c₂`, the test costing `w`, with the bounds of the branches. -/
  | ite (w : Nat) (g : PExp) (B₁ B₂ : Nat) (c₁ c₂ : ACmd) : ACmd
  /-- `while (g ≤ 0) body`, the test costing `w`, with: the invariant `inv`; the
      potential `pot / d`; an upper bound `k` of `pot` on entry; a logical variable `j`
      not used by `inv`; the Farkas certificate of `inv ∧ g ⊢ pot ≥ d`; the bound `Wb` of
      the body. -/
  | while (w : Nat) (g : PExp) (inv : List Lin) (pot : PExp) (d : Nat) (k : Int) (j : Nat)
      (posCert : Nat × List Nat) (Wb : Nat) (body : ACmd) : ACmd
  /-- Consequence: `c` is checked against `P'`, `B'`, `Q'`, and the surrounding triple
      follows by the given Farkas certificates. -/
  | weaken (P' : List Lin) (preCerts : List (Nat × List Nat)) (B' : Nat) (Q' : List Lin)
      (postCerts : List (Nat × List Nat)) (c : ACmd) : ACmd
  /-- Dead code: the precondition is contradictory, by the given certificate. -/
  | dead (cert : Nat × List Nat) (c : ACmd) : ACmd

/-- `pot - γⱼ + extra ≤ 0`, where `γⱼ` is the logical variable `j`. -/
def ghost (pot : PExp) (j : Nat) (extra : Int) : Lin :=
  ⟨pot.sv, vsmul (-1) (unit j), pot.c + extra⟩

/-- **The checker.** -/
def check (P : List Lin) : ACmd → Nat → List Lin → Bool
  | .skip, B, Q => decide (P = Q) && decide (B = 0)
  | .assign w x a, B, Q => decide (P = Q.map (fun e => e.subst x a)) && decide (B = w)
  | .havoc w x, B, Q =>
      decide (P = Q) && Q.all (fun e => decide (coeff e.sv x = 0)) && decide (B = w)
  | .seq c₁ mid B₁ B₂ c₂, B, Q =>
      check P c₁ B₁ mid && check mid c₂ B₂ Q && decide (B = B₁ + B₂)
  | .ite w g B₁ B₂ c₁ c₂, B, Q =>
      check (g.toLin :: P) c₁ B₁ Q && check (g.negLin :: P) c₂ B₂ Q &&
        decide (B = w + max B₁ B₂)
  | .while w g inv pot d k j posCert Wb body, B, Q =>
      decide (0 < d) &&
      decide (P = ⟨pot.sv, [], pot.c - k⟩ :: inv) &&
      decide (Q = g.negLin :: inv) &&
      inv.all (fun e => decide (coeff e.lv j = 0)) &&
      entails1 (g.toLin :: inv) ⟨vsmul (-1) pot.sv, [], d - pot.c⟩ posCert &&
      check (ghost pot j 0 :: g.toLin :: inv) body Wb (ghost pot j d :: inv) &&
      decide (B = (k / d).toNat * (w + Wb) + w)
  | .weaken P' preCerts B' Q' postCerts c, B, Q =>
      entailsAll P P' preCerts && check P' c B' Q' && decide (B' ≤ B) &&
        entailsAll Q' Q postCerts
  | .dead cert _, _, _ => entails1 P ⟨[], [], 1⟩ cert

end ImperativeOptimization.Checker
