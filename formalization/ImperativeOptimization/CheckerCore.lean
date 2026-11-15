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

/-! ### Symbolic bounds -/

/-- `dotN l f = Σᵢ l[i] * max 0 (f i)`. -/
def dotN : List Nat → Env → Nat
  | [], _ => 0
  | a :: l, f => a * (f 0).toNat + dotN l (fun i => f (i + 1))

/-- Componentwise sum of natural vectors, the shorter one padded with zeros. -/
def nadd : List Nat → List Nat → List Nat
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: nadd l m

def nsmul (k : Nat) (l : List Nat) : List Nat := l.map (k * ·)

/-- Componentwise `≤`, missing coefficients being zero. -/
def nle : List Nat → List Nat → Bool
  | [], _ => true
  | a :: l, [] => decide (a = 0) && nle l []
  | a :: l, b :: m => decide (a ≤ b) && nle l m

/-- A **symbolic bound** `c + Σⱼ co[j] * max 0 γⱼ` over the logical variables `γ`. A
    function certificate states `xᵢ = γᵢ` for its parameters in its precondition, so that
    its bound is a function of the parameters (a *summary*). The coefficients are natural
    numbers, so that bounds compose by sums and componentwise comparisons. -/
structure SB where
  c : Nat
  co : List Nat
  deriving DecidableEq, Repr

def SB.eval (b : SB) (ρ : Env) : Nat := b.c + dotN b.co ρ
def SB.const (w : Nat) : SB := ⟨w, []⟩
def SB.add (a b : SB) : SB := ⟨a.c + b.c, nadd a.co b.co⟩
def SB.smul (k : Nat) (a : SB) : SB := ⟨k * a.c, nsmul k a.co⟩
/-- `a ≤ b` for every valuation, by comparing coefficients. -/
def SB.le (a b : SB) : Bool := decide (a.c ≤ b.c) && nle a.co b.co

/-- `Σⱼ k[j] • bs[j]` (the shorter list decides the length). -/
def SB.comb : List Nat → List SB → SB
  | [], _ => SB.const 0
  | _ :: _, [] => SB.const 0
  | k :: ks, b :: bs => (b.smul k).add (SB.comb ks bs)

/-- The coefficient `j` of a natural vector (zero beyond the end). -/
def ncoeff (l : List Nat) (j : Nat) : Nat := l.getD j 0

/-- The bound a loop node requires. Either the entry bound `k + Σ kl[j] γⱼ` of the
    potential is symbolic and the body bound `Wb` is a constant, or the entry bound is a
    constant and the body bound may be symbolic; in both cases `B` must dominate
    `⌊K/d⌋ (w + Wb) + w`. -/
def loopBoundOk (w d : Nat) (k : Int) (kl : List Nat) (Wb B : SB) : Bool :=
  (kl.all (· = 0) &&
    SB.le ((SB.smul (k / d).toNat ((SB.const w).add Wb)).add (SB.const w)) B) ||
  (Wb.co.all (· = 0) && decide (w ≤ B.c) &&
    decide (((w + Wb.c : Nat) : Int) * k ≤ (d : Int) * ((B.c : Int) - w)) &&
    nle (nsmul (w + Wb.c) kl) (nsmul d B.co))

/-- The entry constraint of a loop: `pot - k - Σ kl[j] γⱼ ≤ 0`. -/
def entryLin (pot : PExp) (k : Int) (kl : List Nat) : Lin :=
  ⟨pot.sv, vsmul (-1) (kl.map Int.ofNat), pot.c - k⟩

/-- `Σⱼ lv[j] • inst[j]`: the logical variables replaced by program expressions. -/
def instLv : List Int → List PExp → PExp
  | [], _ => ⟨[], 0⟩
  | _ :: _, [] => ⟨[], 0⟩
  | a :: l, p :: ps =>
      let r := instLv l ps
      ⟨vadd (vsmul a p.sv) r.sv, a * p.c + r.c⟩

/-- A constraint of a callee, read at the call site: its logical variables `γⱼ` become the
    program expressions `inst[j]` (the arguments), the others become `0`. -/
def Lin.inst (e : Lin) (inst : List PExp) : Lin :=
  let r := instLv e.lv inst
  ⟨vadd e.sv r.sv, [], e.c + r.c⟩

/-- `inst[j] ≤ ub.c + Σ ub.co[i] γᵢ`: an upper bound of an argument by a symbolic bound of
    the caller. -/
def ubLin (a : PExp) (ub : SB) : Lin := ⟨a.sv, vsmul (-1) (ub.co.map Int.ofNat), a.c - ub.c⟩

/-- The goals `ubLin inst[j] ubs[j]`. -/
def ubGoals : List PExp → List SB → List Lin
  | a :: as, u :: us => ubLin a u :: ubGoals as us
  | _, _ => []

/-- An annotated program: the program together with everything the checker needs. -/
inductive ACmd where
  | skip : ACmd
  /-- `x := a`, at cost `w`. -/
  | assign (w : Nat) (x : Nat) (a : PExp) : ACmd
  /-- `x := ?` (an unknown value), at cost `w`. -/
  | havoc (w : Nat) (x : Nat) : ACmd
  /-- `x := ?` with the constraints `cs` (each `g ≤ 0`, over program variables) holding
      afterwards, at cost `w`: the value of a non-affine expression such as `y >> 2`,
      described by facts that are true of it (`4x ≤ y ≤ 4x + 3`). -/
  | havocC (w : Nat) (x : Nat) (cs : List PExp) : ACmd
  /-- `c₁ ; c₂` with the intermediate assertion and the two bounds. -/
  | seq (c₁ : ACmd) (mid : List Lin) (B₁ B₂ : SB) (c₂ : ACmd) : ACmd
  /-- `if (g ≤ 0) c₁ else c₂`, the test costing `w`, with the bounds of the branches. -/
  | ite (w : Nat) (g : PExp) (B₁ B₂ : SB) (c₁ c₂ : ACmd) : ACmd
  /-- `while (g ≤ 0) body`, the test costing `w`, with: the invariant `inv`; the
      potential `pot / d`; an upper bound `k + Σ kl[j] γⱼ` of `pot` on entry; a logical
      variable `j` not used by `inv`; the Farkas certificate of `inv ∧ g ⊢ pot ≥ d`; the
      bound `Wb` of the body. -/
  | while (w : Nat) (g : PExp) (inv : List Lin) (pot : PExp) (d : Nat) (k : Int) (kl : List Nat)
      (j : Nat) (posCert : Nat × List Nat) (Wb : SB) (body : ACmd) : ACmd
  /-- `while (gs₁ ≤ 0 ∧ … ∧ gsₙ ≤ 0) body`: a loop whose test is a conjunction, with the
      same annotations as `while`. After the loop only the invariant is known (the negation
      of a conjunction is not a conjunction). -/
  | whileAnd (w : Nat) (gs : List PExp) (inv : List Lin) (pot : PExp) (d : Nat) (k : Int)
      (kl : List Nat) (j : Nat) (posCert : Nat × List Nat) (Wb : SB) (body : ACmd) : ACmd
  /-- Consequence: `c` is checked against `P'`, `B'`, `Q'`, and the surrounding triple
      follows by the given Farkas certificates. -/
  | weaken (P' : List Lin) (preCerts : List (Nat × List Nat)) (B' : SB) (Q' : List Lin)
      (postCerts : List (Nat × List Nat)) (c : ACmd) : ACmd
  /-- Dead code: the precondition is contradictory, by the given certificate. -/
  | dead (cert : Nat × List Nat) (c : ACmd) : ACmd
  /-- A call of function `f` (an earlier entry of the program certificate), the call
      costing `w`: the callee's logical variables are instantiated by the program
      expressions `inst` (its parameters' values); `preCerts` prove the callee's
      precondition; `ubs` bound the instantiated variables by symbolic bounds of the
      caller, with the certificates `ubCerts`. -/
  | call (w : Nat) (f : Nat) (inst : List PExp) (preCerts : List (Nat × List Nat))
      (ubs : List SB) (ubCerts : List (Nat × List Nat)) : ACmd
  deriving DecidableEq

/-- A function of a program certificate: its triple, the variables it may modify, and
    its body. A function without a body is an **assumed contract** (e.g. of a library
    function): it is trusted, not checked. -/
structure FunCert where
  pre : List Lin
  bound : SB
  post : List Lin
  mods : List Nat
  body : Option ACmd

/-- `pot - γⱼ + extra ≤ 0`, where `γⱼ` is the logical variable `j`. -/
def ghost (pot : PExp) (j : Nat) (extra : Int) : Lin :=
  ⟨pot.sv, vsmul (-1) (unit j), pot.c + extra⟩

/-- The cost of a call: `w + F.c + Σⱼ F.co[j] • ubs[j]`. -/
def callBound (w : Nat) (Fb : SB) (ubs : List SB) : SB :=
  (SB.const (w + Fb.c)).add (SB.comb Fb.co ubs)

/-- The variables a command may modify (for a call: the callee's declared ones). -/
def writes (fs : List FunCert) : ACmd → List Nat
  | .skip => []
  | .assign _ x _ => [x]
  | .havoc _ x => [x]
  | .havocC _ x _ => [x]
  | .seq c₁ _ _ _ c₂ => writes fs c₁ ++ writes fs c₂
  | .ite _ _ _ _ c₁ c₂ => writes fs c₁ ++ writes fs c₂
  | .while _ _ _ _ _ _ _ _ _ _ body => writes fs body
  | .whileAnd _ _ _ _ _ _ _ _ _ _ body => writes fs body
  | .weaken _ _ _ _ _ c => writes fs c
  | .dead _ c => writes fs c
  | .call _ f _ _ _ _ => match fs[f]? with
    | some F => F.mods
    | none => []

/-- The constraints of `P` that do not mention the variables `M`. -/
def frameOf (M : List Nat) (P : List Lin) : List Lin :=
  P.filter (fun e => M.all (fun x => decide (coeff e.sv x = 0)))

/-- **The checker.** `fs` are the functions that calls may refer to. -/
def check (fs : List FunCert) (P : List Lin) : ACmd → SB → List Lin → Bool
  | .skip, _, Q => decide (P = Q)
  | .assign w x a, B, Q => decide (P = Q.map (fun e => e.subst x a)) && SB.le (SB.const w) B
  | .havoc w x, B, Q =>
      decide (P = Q) && Q.all (fun e => decide (coeff e.sv x = 0)) && SB.le (SB.const w) B
  | .havocC w x cs, B, Q =>
      decide (Q = P ++ cs.map PExp.toLin) && P.all (fun e => decide (coeff e.sv x = 0)) &&
        SB.le (SB.const w) B
  | .seq c₁ mid B₁ B₂ c₂, B, Q =>
      check fs P c₁ B₁ mid && check fs mid c₂ B₂ Q && SB.le (B₁.add B₂) B
  | .ite w g B₁ B₂ c₁ c₂, B, Q =>
      check fs (g.toLin :: P) c₁ B₁ Q && check fs (g.negLin :: P) c₂ B₂ Q &&
        SB.le ((SB.const w).add B₁) B && SB.le ((SB.const w).add B₂) B
  | .while w g inv pot d k kl j posCert Wb body, B, Q =>
      decide (0 < d) &&
      decide (P = entryLin pot k kl :: inv) &&
      decide (Q = g.negLin :: inv) &&
      inv.all (fun e => decide (coeff e.lv j = 0)) && decide (ncoeff Wb.co j = 0) &&
      entails1 (g.toLin :: inv) ⟨vsmul (-1) pot.sv, [], d - pot.c⟩ posCert &&
      check fs (ghost pot j 0 :: g.toLin :: inv) body Wb (ghost pot j d :: inv) &&
      loopBoundOk w d k kl Wb B
  | .whileAnd w gs inv pot d k kl j posCert Wb body, B, Q =>
      decide (0 < d) &&
      decide (P = entryLin pot k kl :: inv) &&
      decide (Q = inv) &&
      inv.all (fun e => decide (coeff e.lv j = 0)) && decide (ncoeff Wb.co j = 0) &&
      entails1 (gs.map PExp.toLin ++ inv) ⟨vsmul (-1) pot.sv, [], d - pot.c⟩ posCert &&
      check fs (ghost pot j 0 :: (gs.map PExp.toLin ++ inv)) body Wb (ghost pot j d :: inv) &&
      loopBoundOk w d k kl Wb B
  | .weaken P' preCerts B' Q' postCerts c, B, Q =>
      entailsAll P P' preCerts && check fs P' c B' Q' && SB.le B' B &&
        entailsAll Q' Q postCerts
  | .dead cert _, _, _ => entails1 P ⟨[], [], 1⟩ cert
  | .call w f inst preCerts ubs ubCerts, B, Q =>
      match fs[f]? with
      | none => false
      | some F =>
          entailsAll P (F.pre.map (fun e => e.inst inst)) preCerts &&
          decide (F.bound.co.length ≤ ubs.length) && decide (ubs.length ≤ inst.length) &&
          entailsAll P (ubGoals inst ubs) ubCerts &&
          SB.le (callBound w F.bound ubs) B &&
          decide (Q = frameOf F.mods P)

/-- **A program certificate** is a list of functions; each body is checked against its
    triple, may call only the functions before it (so no recursion), and may modify only
    its declared variables. Functions without a body are contracts: trusted. -/
def checkFun (fs : List FunCert) (F : FunCert) : Bool :=
  match F.body with
  | none => true
  | some b => check fs F.pre b F.bound F.post && (writes fs b).all (fun x => F.mods.contains x)

def checkProgram (fs : List FunCert) : Bool :=
  (List.range fs.length).all (fun i => match fs[i]? with
    | some F => checkFun (fs.take i) F
    | none => true)

end ImperativeOptimization.Checker
