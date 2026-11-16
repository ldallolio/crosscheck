/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic
import ImperativeOptimization.MiniC
import ImperativeOptimization.MiniCJumpCore

/-!
# Mini-C with early exits and `switch`: meaning and validation

`MiniCJumpCore` defines `JStmt` (mini-C with `break`, `continue`, `return` and `switch`)
and the elimination of its jumps with flag variables (`elim`), which produces an
`MStmt`. Here:

* `JExec`: the meaning of `JStmt`, given directly, as a big-step semantics with
  *outcomes*: a statement ends normally, by `break`, by `continue`, by `return`, or is
  interrupted (`stop`: the run so far, which gives the cost of execution prefixes, so
  that runs that do not terminate are covered). A loop stops at a `break` of its body
  and goes on at a `continue` (after its increment); a `switch` enters any one of its
  case groups, or none, and falls through the following ones up to a `break`. Jump-free
  statements mean what `lower` says (`MExec`, `MPre`);
* `Quiet`, `exec_transfer`, `pre_transfer`: a program that neither reads nor writes some
  variables runs the same from states that differ on them;
* `sim`: every run of `j` is matched by a run of the lowering of `elim r j`, from a state
  that differs only on the ghost variables, with a cost at least as large;
* `validatedJ_sound`: for a validated certificate (`validateJ`), every execution prefix
  of `j` in the direct semantics costs at most the certificate's bound.

The ghost variables (flags, the unknown tests of `switch`) and the variable of
statements that only cost are the only ones on which the two states differ; the called
functions must not read or write them (`Quiet`, checked syntactically for the functions
of a certificate file by `quietCmd`, assumed for contracts).
-/

namespace ImperativeOptimization.MiniC
open Checker

/-! ### Direct semantics -/

/-- How a statement ends. `stop`: it was interrupted (an execution prefix). -/
inductive Outcome where
  | normal | brk | cont | ret | stop
  deriving DecidableEq, Repr

def Outcome.catchBrk : Outcome → Outcome
  | .brk => .normal
  | o => o

variable {Φ : ℕ → Cmd ℕ Env}

/-- A terminating run of a jump-free statement, by its meaning `lower`. -/
def MExec (Φ : ℕ → Cmd ℕ Env) (s : MStmt) (σ τ : Env) (n : ℕ) : Prop :=
  ∃ c, lower s = some c ∧ Exec Φ c.toCmd σ τ n

/-- An execution prefix of a jump-free statement. -/
def MPre (Φ : ℕ → Cmd ℕ Env) (s : MStmt) (σ : Env) (n : ℕ) : Prop :=
  ∃ c, lower s = some c ∧ Pre Φ c.toCmd σ n

/-- The test of a conditional: its value, and the state after it (a test the fragment
    does not model picks a value of `choiceVar`, as in `lower`). -/
def CondStep (c : MCond) (σ σ' : Env) (b : Bool) : Prop :=
  (∃ g, c.test = some g ∧ σ' = σ ∧ b = decide (g.eval σ ≤ 0)) ∨
  (c.test = none ∧ ∃ v, σ' = Function.update σ choiceVar v ∧ b = decide (v ≤ 0))

/-- The value of a loop test, a conjunction of comparisons of affine values. -/
def LoopTest (cs : List MCond) (σ : Env) (b : Bool) : Prop :=
  ∃ gs, cs.mapM MCond.test = some gs ∧ b = gs.all (fun g => decide (g.eval σ ≤ 0))

/-- **The meaning of mini-C with jumps.** `JExec Φ j σ τ o n`: `j`, started in `σ`, ends
    in `τ` with outcome `o` after spending `n`. -/
inductive JExec (Φ : ℕ → Cmd ℕ Env) : JStmt → Env → Env → Outcome → ℕ → Prop where
  | stop {j σ} : JExec Φ j σ σ .stop 0
  | basic {s σ τ n} (h : MExec Φ s σ τ n) : JExec Φ (.basic s) σ τ .normal n
  | basicS {s σ n} (h : MPre Φ s σ n) : JExec Φ (.basic s) σ σ .stop n
  | seqN {a b σ υ τ o n₁ n₂} (h₁ : JExec Φ a σ υ .normal n₁) (h₂ : JExec Φ b υ τ o n₂) :
      JExec Φ (.seq a b) σ τ o (n₁ + n₂)
  | seqJ {a b σ τ o n} (h : JExec Φ a σ τ o n) (ho : o ≠ .normal) :
      JExec Φ (.seq a b) σ τ o n
  | iteT {w c a b σ σ₁ τ o n} (hc : CondStep c σ σ₁ true) (h : JExec Φ a σ₁ τ o n) :
      JExec Φ (.ite w c a b) σ τ o (w + n)
  | iteF {w c a b σ σ₁ τ o n} (hc : CondStep c σ σ₁ false) (h : JExec Φ b σ₁ τ o n) :
      JExec Φ (.ite w c a b) σ τ o (w + n)
  | loopF {w cs body inc fb fc σ} (ht : LoopTest cs σ false) :
      JExec Φ (.loop w cs body inc fb fc) σ σ .normal w
  | loopN {w cs body inc fb fc σ υ υ' τ o o₁ n₁ n₂ n₃} (ht : LoopTest cs σ true)
      (h₁ : JExec Φ body σ υ o₁ n₁) (ho : o₁ = .normal ∨ o₁ = .cont)
      (h₂ : MExec Φ (inc.getD .skip) υ υ' n₂)
      (h₃ : JExec Φ (.loop w cs body inc fb fc) υ' τ o n₃) :
      JExec Φ (.loop w cs body inc fb fc) σ τ o (w + n₁ + n₂ + n₃)
  | loopIS {w cs body inc fb fc σ υ o₁ n₁ n₂} (ht : LoopTest cs σ true)
      (h₁ : JExec Φ body σ υ o₁ n₁) (ho : o₁ = .normal ∨ o₁ = .cont)
      (h₂ : MPre Φ (inc.getD .skip) υ n₂) :
      JExec Φ (.loop w cs body inc fb fc) σ υ .stop (w + n₁ + n₂)
  | loopX {w cs body inc fb fc σ τ o n₁} (ht : LoopTest cs σ true)
      (h₁ : JExec Φ body σ τ o n₁) (ho : o = .brk ∨ o = .ret ∨ o = .stop) :
      JExec Φ (.loop w cs body inc fb fc) σ τ o.catchBrk (w + n₁)
  | brk {w σ} : JExec Φ (.brk w) σ σ .brk w
  | cont {w σ} : JExec Φ (.cont w) σ σ .cont w
  | ret {s σ τ n} (h : MExec Φ s σ τ n) : JExec Φ (.ret s) σ τ .ret n
  | retS {s σ n} (h : MPre Φ s σ n) : JExec Φ (.ret s) σ σ .stop n
  | switchS {w sc gs σ n} (h : MPre Φ (.cost w) σ n) : JExec Φ (.switch w sc gs) σ σ .stop n
  | switch {w sc gs σ σ₁ τ o n i} (h₀ : MExec Φ (.cost w) σ σ₁ w) (hi : i ≤ gs.length)
      (h : JExec Φ (.fall (gs.drop i)) σ₁ τ o n) :
      JExec Φ (.switch w sc gs) σ τ o.catchBrk (w + n)
  | fallNil {σ} : JExec Φ (.fall []) σ σ .normal 0
  | fallN {g gs σ υ τ o n₁ n₂} (h₁ : JExec Φ g σ υ .normal n₁) (h₂ : JExec Φ (.fall gs) υ τ o n₂) :
      JExec Φ (.fall (g :: gs)) σ τ o (n₁ + n₂)
  | fallJ {g gs σ τ o n} (h : JExec Φ g σ τ o n) (ho : o ≠ .normal) :
      JExec Φ (.fall (g :: gs)) σ τ o n

/-! ### Variables that a program neither reads nor writes -/

/-- `σ` and `σ'` agree outside `G`. -/
def Agree (G : List ℕ) (σ σ' : Env) : Prop := ∀ x, x ∉ G → σ x = σ' x

/-- `τ` keeps the values of `σ` on `W`. -/
def Keeps (W : List ℕ) (σ τ : Env) : Prop := ∀ x ∈ W, τ x = σ x

theorem Agree.refl (G : List ℕ) (σ : Env) : Agree G σ σ := fun _ _ => rfl

theorem Agree.update {G : List ℕ} {σ σ' : Env} (h : Agree G σ σ') (x : ℕ) (v : ℤ) :
    Agree G (Function.update σ x v) (Function.update σ' x v) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; simp
  · simp [Function.update_of_ne hyx, h y hy]

theorem Agree.update_right {G : List ℕ} {σ σ' : Env} (h : Agree G σ σ') {x : ℕ} (hx : x ∈ G)
    (v : ℤ) : Agree G σ (Function.update σ' x v) := by
  intro y hy
  have : y ≠ x := fun e => hy (e ▸ hx)
  simp [Function.update_of_ne this, h y hy]

theorem Keeps.refl (W : List ℕ) (σ : Env) : Keeps W σ σ := fun _ _ => rfl

theorem Keeps.trans {W : List ℕ} {a b c : Env} (h₁ : Keeps W a b) (h₂ : Keeps W b c) :
    Keeps W a c := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Keeps.update {W : List ℕ} (σ : Env) {x : ℕ} (hx : x ∉ W) (v : ℤ) :
    Keeps W σ (Function.update σ x v) := by
  intro y hy
  have : y ≠ x := fun e => hx (e ▸ hy)
  simp [Function.update_of_ne this]

/-- The command `c` reads no variable of `G`, writes no variable of `W` and calls only
    procedures numbered below `n` (their own behaviour is a hypothesis on them). -/
def Quiet (n : ℕ) (G W : List ℕ) : Cmd ℕ Env → Prop
  | .skip => True
  | .atom _ r => ∀ σ τ σ', r σ τ → Agree G σ σ' → ∃ τ', r σ' τ' ∧ Agree G τ τ' ∧ Keeps W σ' τ'
  | .seq a b => Quiet n G W a ∧ Quiet n G W b
  | .ite _ b c d => (∀ σ σ', Agree G σ σ' → b σ = b σ') ∧ Quiet n G W c ∧ Quiet n G W d
  | .while _ b c => (∀ σ σ', Agree G σ σ' → b σ = b σ') ∧ Quiet n G W c
  | .call _ p => p < n

section Transfer
variable {nq : ℕ} {G W : List ℕ}

theorem exec_transfer (hΦ : ∀ p, p < nq → Quiet nq G W (Φ p)) {c : Cmd ℕ Env} {σ τ : Env} {n : ℕ}
    (h : Exec Φ c σ τ n) : Quiet nq G W c → ∀ σ', Agree G σ σ' →
      ∃ τ', Exec Φ c σ' τ' n ∧ Agree G τ τ' ∧ Keeps W σ' τ' := by
  induction h with
  | skip s => intro _ σ' ha; exact ⟨σ', Exec.skip _, ha, Keeps.refl _ _⟩
  | atom hr =>
    intro hq σ' ha
    obtain ⟨τ', h1, h2, h3⟩ := hq _ _ σ' hr ha
    exact ⟨τ', Exec.atom h1, h2, h3⟩
  | seq _ _ ih₁ ih₂ =>
    intro hq σ' ha
    obtain ⟨u', e1, a1, k1⟩ := ih₁ hq.1 σ' ha
    obtain ⟨t', e2, a2, k2⟩ := ih₂ hq.2 u' a1
    exact ⟨t', Exec.seq e1 e2, a2, k1.trans k2⟩
  | iteTrue hb _ ih =>
    intro hq σ' ha
    obtain ⟨t', e, a, k⟩ := ih hq.2.1 σ' ha
    exact ⟨t', Exec.iteTrue ((hq.1 _ _ ha) ▸ hb) e, a, k⟩
  | iteFalse hb _ ih =>
    intro hq σ' ha
    obtain ⟨t', e, a, k⟩ := ih hq.2.2 σ' ha
    exact ⟨t', Exec.iteFalse ((hq.1 _ _ ha) ▸ hb) e, a, k⟩
  | whileFalse hb =>
    intro hq σ' ha
    exact ⟨σ', Exec.whileFalse ((hq.1 _ _ ha) ▸ hb), ha, Keeps.refl _ _⟩
  | whileTrue hb _ _ ih₁ ih₂ =>
    intro hq σ' ha
    obtain ⟨u', e1, a1, k1⟩ := ih₁ hq.2 σ' ha
    obtain ⟨t', e2, a2, k2⟩ := ih₂ hq u' a1
    exact ⟨t', Exec.whileTrue ((hq.1 _ _ ha) ▸ hb) e1 e2, a2, k1.trans k2⟩
  | call _ ih =>
    intro hq σ' ha
    obtain ⟨t', e, a, k⟩ := ih (hΦ _ hq) σ' ha
    exact ⟨t', Exec.call e, a, k⟩

theorem pre_transfer (hΦ : ∀ p, p < nq → Quiet nq G W (Φ p)) {c : Cmd ℕ Env} {σ : Env} {n : ℕ}
    (h : Pre Φ c σ n) : Quiet nq G W c → ∀ σ', Agree G σ σ' → Pre Φ c σ' n := by
  induction h with
  | stop => intro _ _ _; exact Pre.stop _ _
  | done h =>
    intro hq σ' ha
    obtain ⟨t', e, _, _⟩ := exec_transfer hΦ h hq σ' ha
    exact Pre.done e
  | seqLeft _ ih => intro hq σ' ha; exact Pre.seqLeft (ih hq.1 σ' ha)
  | seqRight h₁ _ ih =>
    intro hq σ' ha
    obtain ⟨u', e1, a1, _⟩ := exec_transfer hΦ h₁ hq.1 σ' ha
    exact Pre.seqRight e1 (ih hq.2 u' a1)
  | iteTrue hb _ ih =>
    intro hq σ' ha; exact Pre.iteTrue ((hq.1 _ _ ha) ▸ hb) (ih hq.2.1 σ' ha)
  | iteFalse hb _ ih =>
    intro hq σ' ha; exact Pre.iteFalse ((hq.1 _ _ ha) ▸ hb) (ih hq.2.2 σ' ha)
  | whileBody hb _ ih =>
    intro hq σ' ha; exact Pre.whileBody ((hq.1 _ _ ha) ▸ hb) (ih hq.2 σ' ha)
  | whileNext hb h₁ _ ih =>
    intro hq σ' ha
    obtain ⟨u', e1, a1, _⟩ := exec_transfer hΦ h₁ hq.2 σ' ha
    exact Pre.whileNext ((hq.1 _ _ ha) ▸ hb) e1 (ih hq u' a1)
  | call _ ih => intro hq σ' ha; exact Pre.call (ih (hΦ _ hq) σ' ha)

end Transfer

/-! ### The lowering of a statement that names no variable of `G` is quiet -/

/-- `p` has the same value on states that agree outside `G`. -/
def Indep (G : List ℕ) (p : PExp) : Prop := ∀ σ σ', Agree G σ σ' → p.eval σ = p.eval σ'

theorem PExp.eval_padd (p q : PExp) (σ : Env) : (padd p q).eval σ = p.eval σ + q.eval σ := by
  simp only [padd, PExp.eval, dot_vadd]; ring

theorem PExp.eval_pscale (k : ℤ) (p : PExp) (σ : Env) : (pscale k p).eval σ = k * p.eval σ := by
  simp only [pscale, PExp.eval, dot_vsmul]; ring

theorem Indep.padd {G : List ℕ} {p q : PExp} (hp : Indep G p) (hq : Indep G q) :
    Indep G (padd p q) := fun σ σ' h => by
  rw [PExp.eval_padd, PExp.eval_padd, hp σ σ' h, hq σ σ' h]

theorem Indep.pscale {G : List ℕ} (k : ℤ) {p : PExp} (hp : Indep G p) :
    Indep G (pscale k p) := fun σ σ' h => by
  rw [PExp.eval_pscale, PExp.eval_pscale, hp σ σ' h]

theorem Indep.const (G : List ℕ) (k : ℤ) : Indep G ⟨[], k⟩ := fun _ _ _ => by
  simp [PExp.eval, dot]

theorem Indep.var {G : List ℕ} {x : ℕ} (hx : x ∉ G) : Indep G ⟨unit x, 0⟩ := fun σ σ' h => by
  simp [PExp.eval, dot_unit, h x hx]

theorem Indep.linComb {G : List ℕ} {a b : PExp} (ha : Indep G a) (hb : Indep G b) (k c : ℤ) :
    Indep G (MiniC.linComb a k b c) := fun σ σ' h => by
  have e : ∀ s, (MiniC.linComb a k b c).eval s = k * a.eval s - b.eval s + c := by
    intro s; simp only [MiniC.linComb, PExp.eval, dot_vadd, dot_vsmul]; ring
  rw [e, e, ha σ σ' h, hb σ σ' h]

theorem Indep.smulSv {G : List ℕ} {a : PExp} (ha : Indep G a) (k c : ℤ) :
    Indep G ⟨vsmul k a.sv, c⟩ := fun σ σ' h => by
  have e : ∀ s, (⟨vsmul k a.sv, c⟩ : PExp).eval s = k * (a.eval s - a.c) + c := by
    intro s; simp only [PExp.eval, dot_vsmul]; ring
  rw [e, e, ha σ σ' h]

theorem MExp.affine_indep {G : List ℕ} (e : MExp) (he : ∀ x ∈ e.vars, x ∉ G) :
    ∀ p, e.affine = some p → Indep G p := by
  induction e with
  | var x => intro p hp; simp [MExp.affine] at hp; subst hp; exact Indep.var (he x (by simp [MExp.vars]))
  | lit k => intro p hp; simp [MExp.affine] at hp; subst hp; exact Indep.const G k
  | add a b iha ihb =>
    intro p hp
    simp only [MExp.affine, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
      Option.some.injEq] at hp
    obtain ⟨pa, ha, pb, hb, rfl⟩ := hp
    exact (iha (fun x hx => he x (by simp [MExp.vars, hx])) pa ha).padd
      (ihb (fun x hx => he x (by simp [MExp.vars, hx])) pb hb)
  | sub a b iha ihb =>
    intro p hp
    simp only [MExp.affine, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
      Option.some.injEq] at hp
    obtain ⟨pa, ha, pb, hb, rfl⟩ := hp
    exact (iha (fun x hx => he x (by simp [MExp.vars, hx])) pa ha).padd
      ((ihb (fun x hx => he x (by simp [MExp.vars, hx])) pb hb).pscale (-1))
  | neg a iha =>
    intro p hp
    simp only [MExp.affine, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
      Option.some.injEq] at hp
    obtain ⟨pa, ha, rfl⟩ := hp
    exact (iha (fun x hx => he x (by simp [MExp.vars, hx])) pa ha).pscale (-1)
  | mul a b iha ihb =>
    intro p hp
    simp only [MExp.affine, Option.bind_eq_bind, Option.bind_eq_some] at hp
    obtain ⟨pa, ha, pb, hb, hp⟩ := hp
    have ia := iha (fun x hx => he x (by simp [MExp.vars, hx])) pa ha
    have ib := ihb (fun x hx => he x (by simp [MExp.vars, hx])) pb hb
    split_ifs at hp
    · simp only [Option.pure_def, Option.some.injEq] at hp; subst hp; exact ib.pscale _
    · simp only [Option.pure_def, Option.some.injEq] at hp; subst hp; exact ia.pscale _
  | other => intro p hp; simp [MExp.affine] at hp

theorem MCond.test_indep {G : List ℕ} (c : MCond) (hc : ∀ x ∈ c.vars, x ∉ G) :
    ∀ g, c.test = some g → Indep G g := by
  induction c with
  | cmp op a b =>
    intro g hg
    simp only [MCond.test, Option.bind_eq_bind, Option.bind_eq_some] at hg
    obtain ⟨pa, ha, pb, hb, hg⟩ := hg
    have ia := a.affine_indep (fun x hx => hc x (by simp [MCond.vars, hx])) pa ha
    have ib := b.affine_indep (fun x hx => hc x (by simp [MCond.vars, hx])) pb hb
    cases op <;> simp only [Option.pure_def, Option.some.injEq] at hg <;> subst hg
    · exact (ia.padd (ib.pscale _)).padd (Indep.const _ _)
    · exact ia.padd (ib.pscale _)
    · exact (ib.padd (ia.pscale _)).padd (Indep.const _ _)
    · exact ib.padd (ia.pscale _)
  | not c ih =>
    intro g hg
    simp only [MCond.test, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
      Option.some.injEq] at hg
    obtain ⟨g', h', rfl⟩ := hg
    exact ((ih (fun x hx => hc x (by simpa [MCond.vars] using hx)) g' h').pscale _).padd
      (Indep.const _ _)
  | other => intro g hg; simp [MCond.test] at hg

theorem Indep.withConst {G : List ℕ} {a : PExp} (ha : Indep G a) (k : ℤ) :
    Indep G ⟨a.sv, k⟩ := fun σ σ' h => by
  have e : ∀ s, (⟨a.sv, k⟩ : PExp).eval s = a.eval s - a.c + k := by
    intro s; simp only [PExp.eval]; ring
  rw [e, e, ha σ σ' h]

section Quiet
variable {nq : ℕ} {G W : List ℕ}

theorem quiet_assign {w x : ℕ} {a : PExp} (hx : x ∉ W) (ha : Indep G a) :
    Quiet nq G W (ACmd.assign w x a).toCmd := by
  simp only [ACmd.toCmd, Quiet]
  intro σ τ σ' hr hag
  subst hr
  refine ⟨_, rfl, ?_, Keeps.update σ' hx _⟩
  rw [ha σ σ' hag]; exact hag.update x _

theorem quiet_havoc {w x : ℕ} (hx : x ∉ W) : Quiet nq G W (ACmd.havoc w x).toCmd := by
  simp only [ACmd.toCmd, Quiet]
  intro σ τ σ' hr hag
  obtain ⟨v, rfl⟩ := hr
  exact ⟨_, ⟨v, rfl⟩, hag.update x v, Keeps.update σ' hx v⟩

theorem quiet_havocC {w x : ℕ} {cs : List PExp} (hx : x ∉ W) (hcs : ∀ g ∈ cs, Indep G g) :
    Quiet nq G W (ACmd.havocC w x cs).toCmd := by
  simp only [ACmd.toCmd, Quiet]
  intro σ τ σ' hr hag
  obtain ⟨v, rfl, hall⟩ := hr
  have ha := hag.update x v
  refine ⟨_, ⟨v, rfl, ?_⟩, ha, Keeps.update σ' hx v⟩
  rw [List.all_eq_true] at hall ⊢
  intro g hg
  have := hall g hg
  rwa [hcs g hg _ _ ha] at this

theorem quiet_ite {w : ℕ} {g : PExp} {a b : SB} {x y : ACmd} (hg : Indep G g)
    (hx : Quiet nq G W x.toCmd) (hy : Quiet nq G W y.toCmd) :
    Quiet nq G W (ACmd.ite w g a b x y).toCmd :=
  ⟨fun σ σ' h => by simp only [hg σ σ' h], hx, hy⟩

theorem quiet_seqOf {x y : ACmd} (hx : Quiet nq G W x.toCmd) (hy : Quiet nq G W y.toCmd) :
    Quiet nq G W (seqOf x y).toCmd := ⟨hx, hy⟩

theorem all_indep {gs : List PExp} (hgs : ∀ g ∈ gs, Indep G g) {σ σ' : Env}
    (h : Agree G σ σ') :
    gs.all (fun g => decide (g.eval σ ≤ 0)) = gs.all (fun g => decide (g.eval σ' ≤ 0)) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.all_cons, hgs g (by simp) σ σ' h,
      ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))]

theorem loopOf_toCmd (w : ℕ) (gs : List PExp) (body : ACmd) :
    (loopOf w gs body).toCmd =
      Cmd.while w (fun s => gs.all (fun g => decide (g.eval s ≤ 0))) body.toCmd := by
  unfold loopOf
  split
  · simp [ACmd.toCmd]
  · simp [ACmd.toCmd]

theorem quiet_loopOf {w : ℕ} {gs : List PExp} {body : ACmd} (hgs : ∀ g ∈ gs, Indep G g)
    (hb : Quiet nq G W body.toCmd) : Quiet nq G W (loopOf w gs body).toCmd := by
  rw [loopOf_toCmd]; exact ⟨fun σ σ' h => all_indep hgs h, hb⟩

theorem mapM_test_indep {cs : List MCond} (hcs : ∀ c ∈ cs, ∀ x ∈ c.vars, x ∉ G) :
    ∀ gs, cs.mapM MCond.test = some gs → ∀ g ∈ gs, Indep G g := by
  induction cs with
  | nil =>
    intro gs h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | cons c cs ih =>
    intro gs h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨g, hg, gs', hgs', rfl⟩ := h
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hm
    · exact c.test_indep (hcs c (by simp)) _ hg
    · exact ih (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) gs' hgs' g' hm

end Quiet

section LowerQuiet
variable {nq : ℕ} {G W : List ℕ}

theorem quiet_storeArg (hW : ∀ x ∈ W, x ∈ G) (a : ℕ × Option ℤ × MExp)
    (ha : a.1 ∉ G) (he : ∀ x ∈ a.2.2.vars, x ∉ G) : Quiet nq G W (storeArg a).toCmd := by
  have hx : a.1 ∉ W := fun h => ha (hW _ h)
  obtain ⟨x, hi, e⟩ := a
  cases hi with
  | none =>
    simp only [storeArg]
    split
    · next p hp => exact quiet_assign hx (e.affine_indep he p hp)
    · exact quiet_havoc hx
  | some hi =>
    simp only [storeArg]
    split
    · next p hp =>
      have ip := e.affine_indep he p hp
      exact quiet_ite (ip.withConst _) (quiet_ite (ip.pscale _) (quiet_assign hx ip)
        (quiet_havoc hx)) (quiet_havoc hx)
    · exact quiet_havoc hx

theorem quiet_storeOf {w x : ℕ} {cs : List PExp} (hx : x ∉ W) (hcs : ∀ g ∈ cs, Indep G g) :
    Quiet nq G W (storeOf w x cs).toCmd := by
  unfold storeOf
  split
  · exact quiet_havoc hx
  · exact quiet_havocC hx hcs

theorem quiet_divOf {w x : ℕ} {op : DivOp} {y : PExp} {c : ℤ} (hxG : x ∉ G) (hx : x ∉ W)
    (hy : Indep G y) : Quiet nq G W (divOf w x op y c).toCmd := by
  have xv : Indep G ⟨unit x, 0⟩ := Indep.var hxG
  unfold divOf
  refine quiet_ite (hy.smulSv _ _) (quiet_storeOf hx ?_) (quiet_storeOf hx ?_)
  all_goals
    cases op <;> simp only [divFacts, List.mem_cons, List.mem_nil_iff, or_false] <;>
      intro g hg <;> rcases hg with rfl | rfl | rfl <;>
      first
      | exact xv.linComb hy _ _
      | exact xv.smulSv _ _
      | exact xv.withConst _
      | exact hy.linComb (xv.smulSv _ _) _ _

theorem mem_foldr_vars {cs : List MCond} {c : MCond} {x : ℕ} (hc : c ∈ cs) (hx : x ∈ c.vars) :
    x ∈ cs.foldr (fun c acc => c.vars ++ acc) [] := by
  induction cs with
  | nil => simp at hc
  | cons c' cs ih =>
    simp only [List.foldr_cons, List.mem_append]
    rcases List.mem_cons.mp hc with rfl | hc
    · left; exact hx
    · right; exact ih hc

theorem mem_call_vars {args : List (ℕ × Option ℤ × MExp)} {a : ℕ × Option ℤ × MExp}
    (ha : a ∈ args) (f : ℕ) :
    a.1 ∈ (MStmt.call f args).vars ∧ ∀ x ∈ a.2.2.vars, x ∈ (MStmt.call f args).vars := by
  induction args with
  | nil => simp at ha
  | cons b args ih =>
    simp only [MStmt.vars, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨by simp, fun x hx => by simp [hx]⟩
    · obtain ⟨h1, h2⟩ := ih ha
      exact ⟨List.mem_cons_of_mem _ (List.mem_append_right _ h1),
        fun x hx => List.mem_cons_of_mem _ (List.mem_append_right _ (h2 x hx))⟩

theorem quiet_foldr (hW : ∀ x ∈ W, x ∈ G) (args : List (ℕ × Option ℤ × MExp))
    (hargs : ∀ a ∈ args, a.1 ∉ G ∧ ∀ x ∈ a.2.2.vars, x ∉ G) (fin : ACmd)
    (hfin : Quiet nq G W fin.toCmd) :
    Quiet nq G W (args.foldr (fun a acc => seqOf (storeArg a) acc) fin).toCmd := by
  induction args with
  | nil => exact hfin
  | cons a args ih =>
    exact quiet_seqOf (quiet_storeArg hW a (hargs a (by simp)).1 (hargs a (by simp)).2)
      (ih (fun b hb => hargs b (List.mem_cons_of_mem _ hb)))

/-- **The lowering of a statement is quiet** for the variables it does not name, given
    that `choiceVar` is not among them and that `W ⊆ G` and `costVar ∉ W`. -/
theorem lower_quiet (hW : ∀ x ∈ W, x ∈ G) (h0 : choiceVar ∉ G) (h1 : costVar ∉ W) :
    ∀ (s : MStmt) (c : ACmd), (∀ x ∈ s.vars, x ∉ G) → s.callsBelow nq = true →
      lower s = some c → Quiet nq G W c.toCmd := by
  intro s
  induction s with
  | skip => intro c _ _ h; simp [lower] at h; subst h; trivial
  | assign w x e =>
    intro c hv _ h
    simp only [lower, Option.some.injEq] at h; subst h
    have hx : x ∉ G := hv x (by simp [MStmt.vars])
    have he : ∀ y ∈ e.vars, y ∉ G := fun y hy => hv y (by simp [MStmt.vars, hy])
    split
    · next p hp => exact quiet_assign (fun h => hx (hW _ h)) (e.affine_indep he p hp)
    · exact quiet_havoc (fun h => hx (hW _ h))
  | assignU w x hi e =>
    intro c hv _ h
    simp only [lower, Option.some.injEq] at h; subst h
    have hx : x ∉ G := hv x (by simp [MStmt.vars])
    have hxW : x ∉ W := fun h => hx (hW _ h)
    have he : ∀ y ∈ e.vars, y ∉ G := fun y hy => hv y (by simp [MStmt.vars, hy])
    split
    · next p hp =>
      have ip := e.affine_indep he p hp
      exact quiet_ite (ip.withConst _) (quiet_ite (ip.pscale _) (quiet_assign hxW ip)
        (quiet_havoc hxW)) (quiet_havoc hxW)
    · exact quiet_havoc hxW
  | call f args =>
    intro c hv hcb h
    simp only [lower, Option.some.injEq] at h; subst h
    exact quiet_foldr hW args (fun a ha => ⟨hv _ (mem_call_vars ha f).1,
      fun x hx => hv x ((mem_call_vars ha f).2 x hx)⟩) _ (by simpa [MStmt.callsBelow] using hcb)
  | divStore w x op y c old =>
    intro d hv _hcb h
    have hx : x ∉ G := hv x (by simp [MStmt.vars])
    have hxW : x ∉ W := fun h => hx (hW _ h)
    have hy : ∀ z ∈ y.vars, z ∉ G := fun z hz => hv z (by simp [MStmt.vars, hz])
    simp only [lower] at h
    split_ifs at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact quiet_havoc hxW
    · next p hp =>
      have ip := y.affine_indep hy p hp
      split at h
      · split_ifs at h
        simp only [Option.some.injEq] at h; subst h
        exact quiet_divOf hx hxW ip
      · next t =>
        split_ifs at h
        simp only [Option.some.injEq] at h; subst h
        have ht : t ∉ G := hv t (by simp [MStmt.vars])
        exact quiet_seqOf (quiet_assign (fun h => ht (hW _ h)) ip)
          (quiet_divOf hx hxW (Indep.var ht))
  | cost w =>
    intro c _ _ h
    simp only [lower, Option.some.injEq] at h; subst h
    exact quiet_havoc h1
  | seq a b iha ihb =>
    intro c hv hcb h
    simp only [MStmt.callsBelow, Bool.and_eq_true] at hcb
    simp only [lower, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨la, ha, lb, hb, rfl⟩ := h
    exact quiet_seqOf (iha la (fun x hx => hv x (by simp [MStmt.vars, hx])) hcb.1 ha)
      (ihb lb (fun x hx => hv x (by simp [MStmt.vars, hx])) hcb.2 hb)
  | ite w c a b iha ihb =>
    intro d hv hcb h
    simp only [MStmt.callsBelow, Bool.and_eq_true] at hcb
    simp only [lower, Option.bind_eq_bind, Option.bind_eq_some] at h
    obtain ⟨la, ha, lb, hb, h⟩ := h
    have qa := iha la (fun x hx => hv x (by simp [MStmt.vars, hx])) hcb.1 ha
    have qb := ihb lb (fun x hx => hv x (by simp [MStmt.vars, hx])) hcb.2 hb
    split at h
    · next g hg =>
      simp only [Option.pure_def, Option.some.injEq] at h; subst h
      exact quiet_ite (c.test_indep (fun x hx => hv x (by simp [MStmt.vars, hx])) g hg) qa qb
    · simp only [Option.pure_def, Option.some.injEq] at h; subst h
      exact quiet_seqOf (quiet_havoc (fun h => h0 (hW _ h))) (quiet_ite (Indep.var h0) qa qb)
  | «while» w cs body ih =>
    intro d hv hcb h
    simp only [MStmt.callsBelow] at hcb
    simp only [lower, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨gs, hgs, lb, hb, rfl⟩ := h
    have hcs : ∀ c ∈ cs, ∀ x ∈ c.vars, x ∉ G := fun c hc x hx =>
      hv x (by simp [MStmt.vars, mem_foldr_vars hc hx])
    exact quiet_loopOf (mapM_test_indep hcs gs hgs)
      (ih lb (fun x hx => hv x (by simp [MStmt.vars, hx])) hcb hb)
  | for_ init w cs inc body ihi ihc ihb =>
    intro d hv hcb h
    simp only [MStmt.callsBelow, Bool.and_eq_true] at hcb
    simp only [lower, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨li, hi, gs, hgs, lb, hb, lc, hinc, rfl⟩ := h
    have hcs : ∀ c ∈ cs, ∀ x ∈ c.vars, x ∉ G := fun c hc x hx =>
      hv x (by simp [MStmt.vars, mem_foldr_vars hc hx])
    exact quiet_seqOf (ihi li (fun x hx => hv x (by simp [MStmt.vars, hx])) hcb.1.1 hi)
      (quiet_loopOf (mapM_test_indep hcs gs hgs)
        (quiet_seqOf (ihb lb (fun x hx => hv x (by simp [MStmt.vars, hx])) hcb.2 hb)
          (ihc lc (fun x hx => hv x (by simp [MStmt.vars, hx])) hcb.1.2 hinc)))

end LowerQuiet

/-! ### Flags -/

/-- The flags that are 0 at the normal points of a context: the `break` and `continue`
    flags of its loops, and the return flag inside a construct that contains a
    `return`. -/
def okFlags (r : ℕ) : List Frame → List ℕ
  | [] => []
  | fr :: ctx => fr.fb.toList ++ fr.fc.toList ++ (if fr.rr then [r] else []) ++ okFlags r ctx

def FlagsOK (r : ℕ) (ctx : List Frame) (σ : Env) : Prop := ∀ f ∈ okFlags r ctx, σ f = 0

/-- The flag `f` is set, the other flags of the context are 0. -/
def Set1 (r : ℕ) (ctx : List Frame) (f : ℕ) (σ : Env) : Prop :=
  σ f = 1 ∧ ∀ g ∈ okFlags r ctx, g ≠ f → σ g = 0

/-- The state of the flags after an outcome. -/
def JumpOK (r : ℕ) (ctx : List Frame) : Outcome → Env → Prop
  | .normal, σ => FlagsOK r ctx σ
  | .stop, _ => True
  | .brk, σ => match ctx with
      | [] => True
      | fr :: _ => if fr.isSw then FlagsOK r ctx σ else ∃ f, fr.fb = some f ∧ Set1 r ctx f σ
  | .cont, σ => ∃ f, nearestCnt ctx = some f ∧ Set1 r ctx f σ
  | .ret, σ => ctx = [] ∨ Set1 r ctx r σ

/-- The frames of a context name their flags among their ghost variables, which are
    ghost variables of the function. -/
def WF (Gh : List ℕ) (ctx : List Frame) : Prop :=
  ∀ fr ∈ ctx, (∀ f ∈ fr.fb.toList ++ fr.fc.toList, f ∈ fr.gh) ∧ ∀ f ∈ fr.gh, f ∈ Gh

theorem nearestCnt_mem {r : ℕ} : ∀ {ctx : List Frame} {f : ℕ}, nearestCnt ctx = some f →
    f ∈ okFlags r ctx ∧ ∃ fr ∈ ctx, f ∈ fr.fc.toList
  | [], _, h => by simp [nearestCnt] at h
  | fr :: ctx, f, h => by
    simp only [nearestCnt] at h
    split_ifs at h
    · obtain ⟨h1, fr', h2, h3⟩ := nearestCnt_mem (r := r) h
      exact ⟨by simp [okFlags, h1], fr', List.mem_cons_of_mem _ h2, h3⟩
    · exact ⟨by simp [okFlags, h], fr, List.mem_cons_self _ _, by simp [h]⟩

theorem okFlags_mem {r : ℕ} {Gh : List ℕ} (hr : r ∈ Gh) :
    ∀ {ctx : List Frame}, WF Gh ctx → ∀ f ∈ okFlags r ctx, f ∈ Gh ∧ (f = r ∨ f ∈ ghostsOf ctx)
  | [], _, f, hf => by simp [okFlags] at hf
  | fr :: ctx, hw, f, hf => by
    have hfr := hw fr (List.mem_cons_self _ _)
    have hw' : WF Gh ctx := fun fr' h => hw fr' (List.mem_cons_of_mem _ h)
    simp only [okFlags, List.mem_append] at hf
    rcases hf with ((h | h) | h) | h
    · have := hfr.1 f (by simp [h]); exact ⟨hfr.2 f this, Or.inr (by simp [ghostsOf, this])⟩
    · have := hfr.1 f (by simp [h]); exact ⟨hfr.2 f this, Or.inr (by simp [ghostsOf, this])⟩
    · split_ifs at h <;> simp at h; subst h; exact ⟨hr, Or.inl rfl⟩
    · obtain ⟨h1, h2⟩ := okFlags_mem hr hw' f h
      refine ⟨h1, h2.imp_right fun h => ?_⟩
      simp only [ghostsOf, List.foldr_cons, List.mem_append]; right; exact h

/-- `JumpOK` reads only `r` and the flags of the context. -/
theorem JumpOK.congr {r : ℕ} {ctx : List Frame} {o : Outcome} {σ σ₂ : Env}
    (h : ∀ f, f = r ∨ f ∈ okFlags r ctx → σ₂ f = σ f) (hj : JumpOK r ctx o σ) :
    JumpOK r ctx o σ₂ := by
  have hok : FlagsOK r ctx σ → FlagsOK r ctx σ₂ := fun hk f hf => by
    rw [h f (Or.inr hf)]; exact hk f hf
  have hset : ∀ f, f ∈ okFlags r ctx ∨ f = r → Set1 r ctx f σ → Set1 r ctx f σ₂ := by
    intro f hf ⟨h1, h2⟩
    refine ⟨?_, fun g hg hne => ?_⟩
    · rw [h f (hf.elim Or.inr Or.inl)]; exact h1
    · rw [h g (Or.inr hg)]; exact h2 g hg hne
  cases o with
  | normal => exact hok hj
  | stop => trivial
  | brk =>
    cases ctx with
    | nil => trivial
    | cons fr ctx =>
      simp only [JumpOK] at hj ⊢
      split_ifs at hj ⊢
      · exact hok hj
      · obtain ⟨f, hf, hs⟩ := hj
        exact ⟨f, hf, hset f (Or.inl (by simp [okFlags, hf])) hs⟩
  | cont =>
    obtain ⟨f, hf, hs⟩ := hj
    exact ⟨f, hf, hset f (Or.inl (nearestCnt_mem hf).1) hs⟩
  | ret =>
    rcases hj with hj | hj
    · exact Or.inl hj
    · exact Or.inr (hset r (Or.inr rfl) hj)

/-- The context's flags are unchanged by a store into a variable that is not one of
    them nor `r`. -/
theorem JumpOK.update {r : ℕ} {ctx : List Frame} {o : Outcome} {σ : Env} {x : ℕ}
    (hx : x ≠ r) (hxf : x ∉ okFlags r ctx) (v : ℤ) (hj : JumpOK r ctx o σ) :
    JumpOK r ctx o (Function.update σ x v) := by
  refine hj.congr fun f hf => ?_
  have : f ≠ x := by
    rintro rfl
    rcases hf with hf | hf
    · exact hx hf
    · exact hxf hf
  simp [Function.update_of_ne this]

theorem JumpOK.keeps {r : ℕ} {Gh : List ℕ} {ctx : List Frame} {o : Outcome} {σ σ₂ : Env}
    (hr : r ∈ Gh) (hw : WF Gh ctx) (hk : Keeps Gh σ σ₂) (hj : JumpOK r ctx o σ) :
    JumpOK r ctx o σ₂ :=
  hj.congr fun f hf => hk f (hf.elim (fun e => e ▸ hr) fun h => (okFlags_mem hr hw f h).1)

/-! ### Lowering of the constructs that `elim` writes -/

theorem lower_seq {a b : MStmt} {c : ACmd} (h : lower (.seq a b) = some c) :
    ∃ ca cb, lower a = some ca ∧ lower b = some cb ∧ c = seqOf ca cb := by
  simp only [lower, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨ca, ha, cb, hb, rfl⟩ := h
  exact ⟨ca, cb, ha, hb, rfl⟩

theorem lower_skip : lower .skip = some .skip := rfl

theorem lower_flagSet (w f : ℕ) (k : ℤ) :
    lower (flagSet w f k) = some (.assign w f ⟨[], k⟩) := rfl

theorem lower_cost (w : ℕ) : lower (.cost w) = some (.havoc w costVar) := rfl

theorem clearTest_test (f : ℕ) : (clearTest f).test = some ⟨unit f, 0⟩ := by
  cases f <;> simp [clearTest, MCond.test, MExp.affine, padd, pscale, vsmul, unit, vadd]

theorem eval_unit (f : ℕ) (σ : Env) : (⟨unit f, 0⟩ : PExp).eval σ = σ f := by
  simp [PExp.eval, dot_unit]

theorem lower_ite_test {w : ℕ} {c : MCond} {a b : MStmt} {d : ACmd} {g : PExp}
    (hg : c.test = some g) (h : lower (.ite w c a b) = some d) :
    ∃ la lb, lower a = some la ∧ lower b = some lb ∧ d = .ite w g noSB noSB la lb := by
  simp only [lower, Option.bind_eq_bind, Option.bind_eq_some, hg, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨la, ha, lb, hb, rfl⟩ := h
  exact ⟨la, lb, ha, hb, rfl⟩

theorem lower_ite_other {w : ℕ} {c : MCond} {a b : MStmt} {d : ACmd}
    (hg : c.test = none) (h : lower (.ite w c a b) = some d) :
    ∃ la lb, lower a = some la ∧ lower b = some lb ∧
      d = seqOf (.havoc 0 choiceVar) (.ite w ⟨unit choiceVar, 0⟩ noSB noSB la lb) := by
  simp only [lower, Option.bind_eq_bind, Option.bind_eq_some, hg, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨la, ha, lb, hb, rfl⟩ := h
  exact ⟨la, lb, ha, hb, rfl⟩

theorem lower_unlessF {f : ℕ} {a : MStmt} {d : ACmd} (h : lower (unlessF f a) = some d) :
    ∃ la, lower a = some la ∧ d = .ite 0 ⟨unit f, 0⟩ noSB noSB la .skip := by
  obtain ⟨la, lb, ha, hb, rfl⟩ := lower_ite_test (clearTest_test f) h
  simp [lower] at hb; subst hb
  exact ⟨la, ha, rfl⟩

theorem mapM_append_test (l₁ l₂ : List MCond) :
    (l₁ ++ l₂).mapM MCond.test =
      (l₁.mapM MCond.test).bind fun a => (l₂.mapM MCond.test).map fun b => a ++ b := by
  induction l₁ with
  | nil => simp only [List.nil_append, List.mapM_nil, Option.pure_def, Option.some_bind,
      List.nil_append, Option.map_id']
  | cons c l ih =>
    simp only [List.cons_append, List.mapM_cons, ih, Option.pure_def, Option.bind_eq_bind]
    cases c.test <;> simp only [Option.none_bind, Option.some_bind]
    cases List.mapM MCond.test l <;> simp only [Option.none_bind, Option.some_bind, Option.map_none']
    cases List.mapM MCond.test l₂ <;> simp

theorem mapM_clearTests (fs : List ℕ) :
    (fs.map clearTest).mapM MCond.test = some (fs.map fun f => ⟨unit f, 0⟩) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons, List.mapM_cons, clearTest_test, ih, Option.pure_def,
      Option.bind_eq_bind, Option.some_bind]

theorem all_clear (fs : List ℕ) (σ : Env) :
    (fs.map fun f => (⟨unit f, 0⟩ : PExp)).all (fun g => decide (g.eval σ ≤ 0)) =
      fs.all (fun f => decide (σ f ≤ 0)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [eval_unit, ih]


/-! ### Which outcomes a statement can have -/

theorem escL_drop (i : ℕ) : ∀ gs : List JStmt,
    (JStmt.escCL (gs.drop i) = true → JStmt.escCL gs = true) ∧
    (JStmt.hasRetL (gs.drop i) = true → JStmt.hasRetL gs = true) := by
  induction i with
  | zero => intro gs; simp
  | succ i ih =>
    intro gs
    cases gs with
    | nil => simp [JStmt.escCL, JStmt.hasRetL]
    | cons g gs =>
      simp only [List.drop_succ_cons]
      obtain ⟨h1, h2⟩ := ih gs
      exact ⟨fun h => by simp [JStmt.escCL, h1 h], fun h => by simp [JStmt.hasRetL, h2 h]⟩

theorem outcome_esc {j : JStmt} {σ τ : Env} {o : Outcome} {n : ℕ} (h : JExec Φ j σ τ o n) :
    (o = .brk → j.escB = true) ∧ (o = .cont → j.escC = true) ∧ (o = .ret → j.hasRet = true) := by
  induction h with
  | stop => simp
  | basic => simp
  | basicS => simp
  | seqN _ _ _ ih₂ =>
    exact ⟨fun h => by simp [JStmt.escB, ih₂.1 h], fun h => by simp [JStmt.escC, ih₂.2.1 h],
      fun h => by simp [JStmt.hasRet, ih₂.2.2 h]⟩
  | seqJ _ _ ih =>
    exact ⟨fun h => by simp [JStmt.escB, ih.1 h], fun h => by simp [JStmt.escC, ih.2.1 h],
      fun h => by simp [JStmt.hasRet, ih.2.2 h]⟩
  | iteT _ _ ih =>
    exact ⟨fun h => by simp [JStmt.escB, ih.1 h], fun h => by simp [JStmt.escC, ih.2.1 h],
      fun h => by simp [JStmt.hasRet, ih.2.2 h]⟩
  | iteF _ _ ih =>
    exact ⟨fun h => by simp [JStmt.escB, ih.1 h], fun h => by simp [JStmt.escC, ih.2.1 h],
      fun h => by simp [JStmt.hasRet, ih.2.2 h]⟩
  | loopF => simp
  | loopN _ _ _ _ _ _ ih₃ =>
    exact ⟨fun h => by simpa [JStmt.escB] using ih₃.1 h,
      fun h => by simpa [JStmt.escC] using ih₃.2.1 h, fun h => ih₃.2.2 h⟩
  | loopIS => simp
  | loopX _ _ ho ih =>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rcases ho with rfl | rfl | rfl <;> simp [Outcome.catchBrk] at h
    · rcases ho with rfl | rfl | rfl <;> simp [Outcome.catchBrk] at h
    · rcases ho with rfl | rfl | rfl <;> simp [Outcome.catchBrk] at h
      simp [JStmt.hasRet, ih.2.2 rfl]
  | brk => simp [JStmt.escB]
  | cont => simp [JStmt.escC]
  | ret => simp [JStmt.hasRet]
  | retS => simp
  | switchS => simp
  | @switch w sc gs σ σ₁ τ o n i _ _ _ ih =>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · cases o <;> simp [Outcome.catchBrk] at h
    · cases o <;> simp [Outcome.catchBrk] at h
      have := ih.2.1 rfl
      simp only [JStmt.escC] at this ⊢
      exact (escL_drop i gs).1 this
    · cases o <;> simp [Outcome.catchBrk] at h
      have := ih.2.2 rfl
      simp only [JStmt.hasRet] at this ⊢
      exact (escL_drop i gs).2 this
  | fallNil => simp
  | fallN _ _ _ ih₂ =>
    exact ⟨fun h => by simpa [JStmt.escB, JStmt.escBL] using Or.inr (ih₂.1 h),
      fun h => by simpa [JStmt.escC, JStmt.escCL] using Or.inr (ih₂.2.1 h),
      fun h => by simpa [JStmt.hasRet, JStmt.hasRetL] using Or.inr (ih₂.2.2 h)⟩
  | fallJ _ _ ih =>
    exact ⟨fun h => by simpa [JStmt.escB, JStmt.escBL] using Or.inl (ih.1 h),
      fun h => by simpa [JStmt.escC, JStmt.escCL] using Or.inl (ih.2.1 h),
      fun h => by simpa [JStmt.hasRet, JStmt.hasRetL] using Or.inl (ih.2.2 h)⟩

/-! ### Runs of the guards, clears and case chains that `elim` writes -/

/-- `unlessF fₙ (… (unlessF f₁ u))` runs `u` when no flag is positive, and nothing when
    one is. -/
theorem foldl_unless (σ : Env) (fs : List ℕ) : ∀ (u : MStmt) (d : ACmd),
    lower (fs.foldl (fun u f => unlessF f u) u) = some d →
    ∃ cu, lower u = some cu ∧
      ((∀ f ∈ fs, σ f ≤ 0) → (∀ τ n, Exec Φ cu.toCmd σ τ n → Exec Φ d.toCmd σ τ n) ∧
        (∀ n, Pre Φ cu.toCmd σ n → Pre Φ d.toCmd σ n)) ∧
      ((∃ f ∈ fs, 0 < σ f) → Exec Φ d.toCmd σ σ 0) := by
  induction fs with
  | nil =>
    intro u d h
    exact ⟨d, h, fun _ => ⟨fun _ _ e => e, fun _ e => e⟩, fun ⟨f, hf, _⟩ => by simp at hf⟩
  | cons f fs ih =>
    intro u d h
    simp only [List.foldl_cons] at h
    obtain ⟨cu', hu', h0, hpos⟩ := ih (unlessF f u) d h
    obtain ⟨cu, hu, rfl⟩ := lower_unlessF hu'
    refine ⟨cu, hu, fun hz => ⟨fun τ n e => ?_, fun n e => ?_⟩, fun ⟨g, hg, hgp⟩ => ?_⟩
    · have hfz : σ f ≤ 0 := hz f (by simp)
      have := (h0 fun g hg => hz g (List.mem_cons_of_mem _ hg)).1 τ (0 + n)
        (Exec.iteTrue (by simp [eval_unit, hfz]) e)
      simpa using this
    · have hfz : σ f ≤ 0 := hz f (by simp)
      have := (h0 fun g hg => hz g (List.mem_cons_of_mem _ hg)).2 (0 + n)
        (Pre.iteTrue (by simp [eval_unit, hfz]) e)
      simpa using this
    · by_cases hrest : ∃ g ∈ fs, 0 < σ g
      · exact hpos hrest
      · push_neg at hrest
        rcases List.mem_cons.mp hg with rfl | hg
        · have e := Exec.iteFalse (Φ := Φ) (w := 0)
            (b := fun s => decide ((⟨unit g, 0⟩ : PExp).eval s ≤ 0))
            (c₁ := cu.toCmd) (by simp [eval_unit]; omega) (Exec.skip σ)
          simpa using (h0 hrest).1 σ 0 e
        · exact absurd (hrest g hg) (by omega)

/-- Clearing flags: `f := 0` for each. -/
theorem seqs_clears (fs : List ℕ) : ∀ (d : ACmd), lower (seqs (fs.map fun f => flagSet 0 f 0)) = some d →
    ∀ σ, ∃ σ₁, Exec Φ d.toCmd σ σ₁ 0 ∧ (∀ f ∈ fs, σ₁ f = 0) ∧ (∀ x, x ∉ fs → σ₁ x = σ x) := by
  induction fs with
  | nil =>
    intro d h σ
    simp [seqs, lower] at h; subst h
    exact ⟨σ, Exec.skip σ, by simp, fun _ _ => rfl⟩
  | cons f fs ih =>
    intro d h σ
    cases fs with
    | nil =>
      simp only [List.map_cons, List.map_nil, seqs, lower_flagSet, Option.some.injEq] at h
      subst h
      refine ⟨Function.update σ f 0, ?_, by simp, fun x hx => by simp at hx; simp [hx]⟩
      have := Exec.atom (Φ := Φ) (w := 0)
        (r := fun s t => t = Function.update s f ((⟨[], 0⟩ : PExp).eval s)) (s := σ) rfl
      simpa [ACmd.toCmd, PExp.eval, dot] using this
    | cons f' fs =>
      simp only [List.map_cons, seqs] at h
      obtain ⟨ca, cb, ha, hb, rfl⟩ := lower_seq h
      simp only [lower_flagSet, Option.some.injEq] at ha; subst ha
      obtain ⟨σ₁, e, hz, hk⟩ := ih cb (by simpa [List.map_cons] using hb) (Function.update σ f 0)
      refine ⟨σ₁, ?_, ?_, ?_⟩
      · have e0 := Exec.atom (Φ := Φ) (w := 0)
          (r := fun s t => t = Function.update s f ((⟨[], 0⟩ : PExp).eval s)) (s := σ) rfl
        have := Exec.seq e0 e
        simpa [seqOf, ACmd.toCmd, PExp.eval, dot] using this
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · by_cases hgf : g ∈ f' :: fs
          · exact hz g hgf
          · rw [hk g hgf]; simp
        · exact hz g hg
      · intro x hx
        rw [hk x (fun h => hx (List.mem_cons_of_mem _ h))]
        have hxf : x ≠ f := fun h => hx (by simp [h])
        simp [Function.update_of_ne hxf]

theorem lower_groupOf {sc : ℕ} {g : MStmt} {d : ACmd} (h : lower (groupOf sc g) = some d) :
    ∃ cg, lower g = some cg ∧
      d = seqOf (.havoc 0 sc) (.ite 0 ⟨unit sc, 0⟩ noSB noSB cg .skip) := by
  obtain ⟨ca, cb, ha, hb, rfl⟩ := lower_seq h
  simp [lower, MExp.affine] at ha; subst ha
  obtain ⟨cg, hg, rfl⟩ := lower_unlessF hb
  exact ⟨cg, hg, rfl⟩

theorem exec_havoc (w x : ℕ) (σ : Env) (v : ℤ) :
    Exec Φ (ACmd.havoc w x).toCmd σ (Function.update σ x v) w :=
  Exec.atom ⟨v, rfl⟩

/-- A case group entered (`sc := 0`) or skipped (`sc := 1`). -/
theorem group_enter {sc : ℕ} {g : MStmt} {d : ACmd} (h : lower (groupOf sc g) = some d) :
    ∃ cg, lower g = some cg ∧
      (∀ σ τ n, Exec Φ cg.toCmd (Function.update σ sc 0) τ n → Exec Φ d.toCmd σ τ n) ∧
      (∀ σ n, Pre Φ cg.toCmd (Function.update σ sc 0) n → Pre Φ d.toCmd σ n) ∧
      (∀ σ, Exec Φ d.toCmd σ (Function.update σ sc 1) 0) := by
  obtain ⟨cg, hg, rfl⟩ := lower_groupOf h
  refine ⟨cg, hg, fun σ τ n e => ?_, fun σ n e => ?_, fun σ => ?_⟩
  · have := Exec.seq (exec_havoc (Φ := Φ) 0 sc σ 0)
      (Exec.iteTrue (w := 0) (b := fun s => decide ((⟨unit sc, 0⟩ : PExp).eval s ≤ 0)) (c₂ := ACmd.skip.toCmd) (by simp [eval_unit]) e)
    simpa [seqOf, ACmd.toCmd] using this
  · have := Pre.seqRight (exec_havoc (Φ := Φ) 0 sc σ 0)
      (Pre.iteTrue (w := 0) (b := fun s => decide ((⟨unit sc, 0⟩ : PExp).eval s ≤ 0)) (c₂ := ACmd.skip.toCmd) (by simp [eval_unit]) e)
    simpa [seqOf, ACmd.toCmd] using this
  · have := Exec.seq (exec_havoc (Φ := Φ) 0 sc σ 1)
      (Exec.iteFalse (w := 0) (b := fun s => decide ((⟨unit sc, 0⟩ : PExp).eval s ≤ 0)) (c₁ := cg.toCmd) (by simp [eval_unit]) (Exec.skip _))
    simpa [seqOf, ACmd.toCmd] using this

theorem lower_chain_cons {sc : ℕ} {g : MStmt} {gs : List MStmt} {d : ACmd}
    (h : lower (chainOf sc (g :: gs)) = some d) :
    ∃ dg dr, lower (groupOf sc g) = some dg ∧ lower (chainOf sc gs) = some dr ∧ d = seqOf dg dr := by
  simp only [chainOf] at h
  exact lower_seq h

/-- Skipping every group of a chain costs nothing and changes only `sc`. -/
theorem chain_skip (sc : ℕ) : ∀ (gs : List MStmt) (d : ACmd), lower (chainOf sc gs) = some d →
    ∀ σ, ∃ σ₁, Exec Φ d.toCmd σ σ₁ 0 ∧ ∀ x, x ≠ sc → σ₁ x = σ x := by
  intro gs
  induction gs with
  | nil => intro d h σ; simp [chainOf, lower] at h; subst h; exact ⟨σ, Exec.skip σ, fun _ _ => rfl⟩
  | cons g gs ih =>
    intro d h σ
    obtain ⟨dg, dr, hg, hr, rfl⟩ := lower_chain_cons h
    obtain ⟨_, _, _, _, hskip⟩ := group_enter (Φ := Φ) hg
    obtain ⟨σ₁, e, hk⟩ := ih dr hr (Function.update σ sc 1)
    refine ⟨σ₁, by simpa [seqOf, ACmd.toCmd] using Exec.seq (hskip σ) e, fun x hx => ?_⟩
    rw [hk x hx, Function.update_of_ne hx]

/-- The groups before the one entered are skipped. -/
theorem chain_drop (sc : ℕ) : ∀ (i : ℕ) (gs : List MStmt) (d : ACmd),
    lower (chainOf sc gs) = some d →
    ∃ dr, lower (chainOf sc (gs.drop i)) = some dr ∧ ∀ σ, ∃ σ₁, (∀ x, x ≠ sc → σ₁ x = σ x) ∧
      (∀ τ n, Exec Φ dr.toCmd σ₁ τ n → Exec Φ d.toCmd σ τ n) ∧
      (∀ n, Pre Φ dr.toCmd σ₁ n → Pre Φ d.toCmd σ n) := by
  intro i
  induction i with
  | zero => intro gs d h; exact ⟨d, h, fun σ => ⟨σ, fun _ _ => rfl, fun _ _ e => e, fun _ e => e⟩⟩
  | succ i ih =>
    intro gs d h
    cases gs with
    | nil =>
      simp [chainOf, lower] at h; subst h
      exact ⟨.skip, by simp [chainOf, lower], fun σ => ⟨σ, fun _ _ => rfl, fun _ _ e => e,
        fun _ e => e⟩⟩
    | cons g gs =>
      obtain ⟨dg, dr, hg, hr, rfl⟩ := lower_chain_cons h
      obtain ⟨_, _, _, _, hskip⟩ := group_enter (Φ := Φ) hg
      obtain ⟨dr', hr', hrun⟩ := ih gs dr hr
      refine ⟨dr', by simpa using hr', fun σ => ?_⟩
      obtain ⟨σ₁, hk, he, hp⟩ := hrun (Function.update σ sc 1)
      refine ⟨σ₁, fun x hx => by rw [hk x hx, Function.update_of_ne hx], fun τ n e => ?_,
        fun n e => ?_⟩
      · simpa [seqOf, ACmd.toCmd] using Exec.seq (hskip σ) (he τ n e)
      · simpa [seqOf, ACmd.toCmd] using Pre.seqRight (hskip σ) (hp n e)

theorem trL_drop {r : ℕ} {Gh : List ℕ} {ctx : List Frame} : ∀ (i : ℕ) (gs : List JStmt)
    (groups : List MStmt), trL r nb Gh ctx gs = some groups →
    trL r nb Gh ctx (gs.drop i) = some (groups.drop i) := by
  intro i
  induction i with
  | zero => intro gs groups h; simpa using h
  | succ i ih =>
    intro gs groups h
    cases gs with
    | nil => simp [trL] at h; subst h; simp [trL]
    | cons g gs =>
      simp only [trL, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨g', _, gs', hgs', rfl⟩ := h
      simpa using ih gs gs' hgs'

/-! ### The simulation: statements of the induction -/

/-- What follows: a run of the continuation `k` from `τ'` extends a run of `cm` from `σ'`
    that has spent `n'`. -/
def Cont (Φ : ℕ → Cmd ℕ Env) (k : MStmt) (cm : ACmd) (σ' τ' : Env) (n' : ℕ) : Prop :=
  ∃ ck, lower k = some ck ∧
    (∀ υ n₂, Exec Φ ck.toCmd τ' υ n₂ → Exec Φ cm.toCmd σ' υ (n' + n₂)) ∧
    (∀ n₂, Pre Φ ck.toCmd τ' n₂ → Pre Φ cm.toCmd σ' (n' + n₂))

/-- The run of `cm` from `σ'` that matches a direct run ending in `τ` with outcome `o`
    after `n`: it costs at least `n`; it ends in a state that agrees with `τ` outside
    `G`, with the flags set as the outcome says, and, after a normal end, it goes on
    with the continuation. -/
def Res (Φ : ℕ → Cmd ℕ Env) (G : List ℕ) (r : ℕ) (ctx : List Frame) (k : MStmt) (cm : ACmd)
    (σ' τ : Env) : Outcome → ℕ → Prop
  | .normal, n => ∃ τ' n', n ≤ n' ∧ Agree G τ τ' ∧ FlagsOK r ctx τ' ∧ Cont Φ k cm σ' τ' n'
  | .stop, n => ∃ n', n ≤ n' ∧ Pre Φ cm.toCmd σ' n'
  | o, n => ∃ τ' n', n ≤ n' ∧ Agree G τ τ' ∧ JumpOK r ctx o τ' ∧ Exec Φ cm.toCmd σ' τ' n'

/-- The same for the loop command of a `loop` node (after its flags are cleared). -/
def LRes (Φ : ℕ → Cmd ℕ Env) (G : List ℕ) (r : ℕ) (ctx : List Frame) (rets : Bool) (cw : ACmd)
    (σ' τ : Env) : Outcome → ℕ → Prop
  | .normal, n => ∃ τ' n', n ≤ n' ∧ Agree G τ τ' ∧ FlagsOK r ctx τ' ∧ (rets = true → τ' r = 0) ∧
      Exec Φ cw.toCmd σ' τ' n'
  | .stop, n => ∃ n', n ≤ n' ∧ Pre Φ cw.toCmd σ' n'
  | .ret, n => ∃ τ' n', n ≤ n' ∧ Agree G τ τ' ∧ τ' r = 1 ∧ JumpOK r ctx .ret τ' ∧
      Exec Φ cw.toCmd σ' τ' n'
  | _, _ => True

/-- The same for the chain of case groups of a `switch` (`fall`). -/
def FRes (Φ : ℕ → Cmd ℕ Env) (G : List ℕ) (r : ℕ) (ctx : List Frame) (cc : ACmd)
    (σ' τ : Env) : Outcome → ℕ → Prop
  | .stop, n => ∃ n', n ≤ n' ∧ Pre Φ cc.toCmd σ' n'
  | o, n => ∃ τ' n', n ≤ n' ∧ Agree G τ τ' ∧ JumpOK r ctx o τ' ∧ Exec Φ cc.toCmd σ' τ' n'

def MainP (Φ : ℕ → Cmd ℕ Env) (r nb : ℕ) (Gh : List ℕ) (j : JStmt) (σ τ : Env) (o : Outcome)
    (n : ℕ) : Prop :=
  ∀ ctx k m cm, WF Gh ctx → (∀ x ∈ j.ghosts, x ∈ Gh) → tr r nb Gh ctx j k = some m →
    lower m = some cm → ∀ σ', Agree (costVar :: Gh) σ σ' → FlagsOK r ctx σ' →
      Res Φ (costVar :: Gh) r ctx k cm σ' τ o n

/-- The frame of a loop node, as `tr` builds it. -/
def loopFrame (body : JStmt) (fb fc : Option ℕ) : Frame :=
  ⟨false, if body.escB then fb else none, if body.escC then fc else none, body.hasRet,
    (if body.escB then fb else none).toList ++ (if body.escC then fc else none).toList⟩

def loopExits (r : ℕ) (body : JStmt) (fb : Option ℕ) : List ℕ :=
  (if body.escB then fb else none).toList ++ (if body.hasRet then [r] else [])

def incClean (nb : ℕ) (Gh : List ℕ) : Option MStmt → Bool
  | some u => cleanS nb Gh u
  | none => true

def LoopP (Φ : ℕ → Cmd ℕ Env) (r nb : ℕ) (Gh : List ℕ) (j : JStmt) (σ τ : Env) (o : Outcome)
    (n : ℕ) : Prop :=
  ∀ w cs body inc fb fc, j = .loop w cs body inc fb fc →
  ∀ ctx bd cw, WF Gh ctx → (∀ x ∈ j.ghosts, x ∈ Gh) →
    (body.escB = true → fb.isSome) → (body.escC = true → fc.isSome) →
    freshGh r ctx (loopFrame body fb fc).gh = true →
    cs.all (cleanC Gh) = true → incClean nb Gh inc = true →
    tr r nb Gh (loopFrame body fb fc :: ctx) body .skip = some bd →
    lower (whileOf w cs (loopExits r body fb) (loopFrame body fb fc).fc bd inc) = some cw →
    ∀ σ', Agree (costVar :: Gh) σ σ' → FlagsOK r ctx σ' → (∀ f ∈ loopExits r body fb, σ' f = 0) →
      LRes Φ (costVar :: Gh) r ctx body.hasRet cw σ' τ o n

def swFrame (rets : Bool) (sc : ℕ) : Frame := ⟨true, none, none, rets, [sc]⟩

def FallP (Φ : ℕ → Cmd ℕ Env) (r nb : ℕ) (Gh : List ℕ) (j : JStmt) (σ τ : Env) (o : Outcome)
    (n : ℕ) : Prop :=
  ∀ gs, j = .fall gs → ∀ ctx0 rets sc groups cc, WF Gh (swFrame rets sc :: ctx0) →
    (∀ x ∈ j.ghosts, x ∈ Gh) → sc ∈ Gh → sc ≠ r → sc ∉ okFlags r ctx0 →
    trL r nb Gh (swFrame rets sc :: ctx0) gs = some groups → lower (chainOf sc groups) = some cc →
    ∀ σ', Agree (costVar :: Gh) σ σ' → FlagsOK r (swFrame rets sc :: ctx0) σ' →
      FRes Φ (costVar :: Gh) r (swFrame rets sc :: ctx0) cc σ' τ o n

theorem disjoint_spec {l m : List ℕ} (h : disjoint l m = true) : ∀ x ∈ l, x ∉ m := by
  intro x hx hm
  simp [disjoint] at h
  exact h x hx hm

theorem nodup_spec : ∀ {l : List ℕ}, nodup l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    simp [nodup] at h
    exact List.nodup_cons.mpr ⟨h.1, nodup_spec h.2⟩

theorem okFlags_cons_sub {r : ℕ} {fr : Frame} {ctx : List Frame} {f : ℕ}
    (h : f ∈ okFlags r ctx) : f ∈ okFlags r (fr :: ctx) := by
  simp [okFlags, h]

theorem isSkip_eq {k : MStmt} (h : k.isSkip = true) : k = .skip := by
  cases k <;> simp_all [MStmt.isSkip]

/-- The continuation after a construct, guarded by the return flag `r` (if `rr`) and the
    `continue` flag `c`. -/
theorem guardTail_run {rr : Option ℕ} {c : Option ℕ} {k : MStmt} {cg : ACmd}
    (h : lower (guardTail rr c k) = some cg) :
    (∀ σ, (∀ f ∈ rr.toList ++ c.toList, σ f ≤ 0) → ∃ ck, lower k = some ck ∧
        (∀ υ n, Exec Φ ck.toCmd σ υ n → Exec Φ cg.toCmd σ υ n) ∧
        (∀ n, Pre Φ ck.toCmd σ n → Pre Φ cg.toCmd σ n)) ∧
    (∀ σ, (∃ f ∈ rr.toList ++ c.toList, 0 < σ f) → Exec Φ cg.toCmd σ σ 0) := by
  by_cases hk : k.isSkip = true
  · have hk' := isSkip_eq hk; subst hk'
    simp [guardTail, MStmt.isSkip, lower] at h; subst h
    exact ⟨fun σ _ => ⟨.skip, rfl, fun _ _ e => e, fun _ e => e⟩, fun σ _ => Exec.skip σ⟩
  · have e : guardTail rr c k = (c.toList ++ rr.toList).foldl (fun u f => unlessF f u) k := by
      cases rr <;> cases c <;> simp [guardTail, hk]
    rw [e] at h
    refine ⟨fun σ hz => ?_, fun σ hp => ?_⟩
    · obtain ⟨ck, hk, h0, _⟩ := foldl_unless (Φ := Φ) σ _ k cg h
      exact ⟨ck, hk, h0 fun f hf => hz f (by simp at hf ⊢; tauto)⟩
    · obtain ⟨ck, hk, _, hpos⟩ := foldl_unless (Φ := Φ) σ _ k cg h
      obtain ⟨f, hf, hfp⟩ := hp
      exact hpos ⟨f, by simp at hf ⊢; tauto, hfp⟩

/-- The increment of a loop, guarded by the exit flags. -/
def incG (exits : List ℕ) : Option MStmt → MStmt
  | some u => exits.foldl (fun u f => unlessF f u) u
  | none => .skip

theorem lower_whileOf {w : ℕ} {cs : List MCond} {exits : List ℕ} {fc : Option ℕ} {bd : MStmt}
    {inc : Option MStmt} {cw : ACmd} (h : lower (whileOf w cs exits fc bd inc) = some cw) :
    ∃ gsC lcc lbd lig, cs.mapM MCond.test = some gsC ∧
      lower (match fc with | some f => flagSet 0 f 0 | none => .skip) = some lcc ∧
      lower bd = some lbd ∧
      lower (incG exits inc) = some lig ∧
      cw.toCmd = Cmd.while w (fun s => gsC.all (fun g => decide (g.eval s ≤ 0)) &&
        exits.all (fun f => decide (s f ≤ 0))) (Cmd.seq lcc.toCmd (Cmd.seq lbd.toCmd lig.toCmd)) := by
  simp only [whileOf, lower, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨gs, hgs, lb, hlb, rfl⟩ := h
  obtain ⟨lcc, hcc, lr, ⟨lbd, hbd, lig, hig, rfl⟩, rfl⟩ := hlb
  rw [mapM_append_test, mapM_clearTests] at hgs
  simp only [Option.bind_eq_some, Option.map_some', Option.some.injEq] at hgs
  obtain ⟨gsC, hC, rfl⟩ := hgs
  refine ⟨gsC, lcc, lbd, lig, hC, hcc, hbd, by cases inc <;> exact hig, ?_⟩
  rw [loopOf_toCmd]
  simp only [List.all_append, all_clear, seqOf, ACmd.toCmd]

theorem flagsOK_sub {r : ℕ} {ctx : List Frame} {σ σ₂ : Env} (fs : List ℕ)
    (hz : ∀ f ∈ fs, σ₂ f = 0) (hk : ∀ x, x ∉ fs → σ₂ x = σ x) (h : FlagsOK r ctx σ) :
    FlagsOK r ctx σ₂ := by
  intro f hf
  by_cases hfs : f ∈ fs
  · exact hz f hfs
  · rw [hk f hfs]; exact h f hf

theorem agree_sub {G : List ℕ} {σ σ' σ₂ : Env} (fs : List ℕ) (hfs : ∀ f ∈ fs, f ∈ G)
    (hk : ∀ x, x ∉ fs → σ₂ x = σ' x) (h : Agree G σ σ') : Agree G σ σ₂ := by
  intro x hx
  rw [hk x (fun h => hx (hfs x h))]; exact h x hx

theorem tr_loop_inv {r : ℕ} {Gh : List ℕ} {ctx : List Frame} {w : ℕ} {cs : List MCond}
    {body : JStmt} {inc : Option MStmt} {fb fc : Option ℕ} {k m : MStmt}
    (h : tr r nb Gh ctx (.loop w cs body inc fb fc) k = some m) :
    (body.escB = true → fb.isSome) ∧ (body.escC = true → fc.isSome) ∧
    freshGh r ctx (loopFrame body fb fc).gh = true ∧ cs.all (cleanC Gh) = true ∧
    incClean nb Gh inc = true ∧
    ∃ bd, tr r nb Gh (loopFrame body fb fc :: ctx) body .skip = some bd ∧
      m = .seq (seqs ((loopExits r body fb).map fun f => flagSet 0 f 0))
        (.seq (whileOf w cs (loopExits r body fb) (loopFrame body fb fc).fc bd inc)
          (guardTail (if body.hasRet then some r else none) none k)) := by
  simp only [tr] at h
  simp only [loopFrame, loopExits]
  generalize body.escB = B at h ⊢
  generalize body.escC = C at h ⊢
  generalize body.hasRet = R at h ⊢
  cases B <;> cases C <;> cases R <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;>
    split_ifs at h with h1 h2 h3 h4 <;> simp_all
  all_goals
    obtain ⟨bd, hbd, hm⟩ := Option.bind_eq_some.mp h
    cases hm
    cases inc <;> simp_all [Option.isSome_iff_ne_none, incClean]

theorem loop_main {r : ℕ} {Gh : List ℕ} (hr : r ∈ Gh) {w : ℕ} {cs : List MCond} {body : JStmt}
    {inc : Option MStmt} {fb fc : Option ℕ} {σ τ : Env} {o : Outcome} {n : ℕ}
    (hL : LoopP Φ r nb Gh (.loop w cs body inc fb fc) σ τ o n)
    (hb : o ≠ .brk) (hc : o ≠ .cont) (hret : o = .ret → body.hasRet = true) :
    MainP Φ r nb Gh (.loop w cs body inc fb fc) σ τ o n := by
  intro ctx k m cm hw hg htr hl σ' ha hok
  obtain ⟨hB, hC, hF, hcs, hinc, bd, hbd, rfl⟩ := tr_loop_inv htr
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := lower_seq hl
  obtain ⟨cw, cg, hcw, hcg, rfl⟩ := lower_seq hc2
  have hexG : ∀ f ∈ loopExits r body fb, f ∈ costVar :: Gh := by
    intro f hf
    simp only [loopExits, List.mem_append] at hf
    rcases hf with hf | hf
    · apply List.mem_cons_of_mem
      apply hg
      simp only [JStmt.ghosts, List.mem_append]
      left; left
      split_ifs at hf <;> simp_all
    · split_ifs at hf <;> simp_all
  obtain ⟨σ₁, e1, hz1, hk1⟩ := seqs_clears (Φ := Φ) _ c1 hc1 σ'
  have ha1 := agree_sub _ hexG hk1 ha
  have hok1 := flagsOK_sub _ hz1 hk1 hok
  have hres := hL w cs body inc fb fc rfl ctx bd cw hw hg hB hC hF hcs hinc hbd hcw σ₁ ha1 hok1 hz1
  have hgt := guardTail_run (Φ := Φ) hcg
  cases o with
  | brk => exact absurd rfl hb
  | cont => exact absurd rfl hc
  | stop =>
    obtain ⟨n', hn, hp⟩ := hres
    refine ⟨0 + n', by omega, ?_⟩
    exact Pre.seqRight e1 (Pre.seqLeft hp)
  | normal =>
    obtain ⟨τ', n', hn, ha', hok', hr0, he⟩ := hres
    refine ⟨τ', 0 + (n' + 0), by omega, ha', hok', ?_⟩
    obtain ⟨ck, hck, hrun, hpre⟩ := hgt.1 τ' (by
      intro f hf
      split_ifs at hf with hrr
      · simp at hf; rw [hf, hr0 hrr]
      · simp at hf)
    refine ⟨ck, hck, fun υ n₂ e => ?_, fun n₂ e => ?_⟩
    · have := Exec.seq e1 (Exec.seq he (hrun υ n₂ e))
      simpa [seqOf, ACmd.toCmd, Nat.add_assoc] using this
    · have := Pre.seqRight e1 (Pre.seqRight he (hpre n₂ e))
      simpa [seqOf, ACmd.toCmd, Nat.add_assoc] using this
  | ret =>
    obtain ⟨τ', n', hn, ha', hr1, hj, he⟩ := hres
    have hrr := hret rfl
    refine ⟨τ', 0 + (n' + 0), by omega, ha', hj, ?_⟩
    have := Exec.seq e1 (Exec.seq he (hgt.2 τ' ⟨r, by simp [hrr], by rw [hr1]; norm_num⟩))
    simpa [seqOf, ACmd.toCmd] using this

/-! ### The simulation: helpers -/

section Sim
variable {r nb : ℕ} {Gh : List ℕ}

theorem choice_notin (h0 : choiceVar ∉ Gh) : choiceVar ∉ costVar :: Gh :=
  List.not_mem_cons_of_ne_of_not_mem (by decide) h0

theorem basic_exec (hΦ : ∀ p, p < nb → Quiet nb (costVar :: Gh) Gh (Φ p)) (h0 : choiceVar ∉ Gh)
    (h1 : costVar ∉ Gh) {s : MStmt} {c : ACmd} {σ τ σ' : Env} {n : ℕ}
    (hs : cleanS nb Gh s = true) (hl : lower s = some c) (he : Exec Φ c.toCmd σ τ n)
    (ha : Agree (costVar :: Gh) σ σ') :
    ∃ τ', Exec Φ c.toCmd σ' τ' n ∧ Agree (costVar :: Gh) τ τ' ∧ Keeps Gh σ' τ' :=
  exec_transfer hΦ he (lower_quiet (fun _ hx => List.mem_cons_of_mem _ hx) (choice_notin h0) h1
    s c (disjoint_spec (Bool.and_eq_true .. |>.mp hs).1) (Bool.and_eq_true .. |>.mp hs).2 hl) σ' ha

theorem basic_pre (hΦ : ∀ p, p < nb → Quiet nb (costVar :: Gh) Gh (Φ p)) (h0 : choiceVar ∉ Gh)
    (h1 : costVar ∉ Gh) {s : MStmt} {c : ACmd} {σ σ' : Env} {n : ℕ}
    (hs : cleanS nb Gh s = true) (hl : lower s = some c) (he : Pre Φ c.toCmd σ n)
    (ha : Agree (costVar :: Gh) σ σ') : Pre Φ c.toCmd σ' n :=
  pre_transfer hΦ he (lower_quiet (fun _ hx => List.mem_cons_of_mem _ hx) (choice_notin h0) h1
    s c (disjoint_spec (Bool.and_eq_true .. |>.mp hs).1) (Bool.and_eq_true .. |>.mp hs).2 hl) σ' ha

theorem FlagsOK.keeps (hr : r ∈ Gh) {ctx : List Frame} {σ σ₂ : Env} (hw : WF Gh ctx)
    (hk : Keeps Gh σ σ₂) (h : FlagsOK r ctx σ) : FlagsOK r ctx σ₂ :=
  JumpOK.keeps (o := .normal) hr hw hk h

theorem notin_okFlags (hr : r ∈ Gh) {ctx : List Frame} (hw : WF Gh ctx) {x : ℕ} (hx : x ∉ Gh) :
    x ∉ okFlags r ctx := fun h => hx (okFlags_mem hr hw x h).1

/-- Entering a branch of a conditional. -/
theorem ite_entry (h0 : choiceVar ∉ Gh) (hr : r ∈ Gh) {ctx : List Frame} (hw : WF Gh ctx)
    {w : ℕ} {c : MCond} {ta tb : MStmt} {d : ACmd} {σ σ₁ σ' : Env} {bv : Bool}
    (hd : lower (.ite w c ta tb) = some d) (hcl : cleanC Gh c = true) (hc : CondStep c σ σ₁ bv)
    (ha : Agree (costVar :: Gh) σ σ') (hok : FlagsOK r ctx σ') :
    ∃ σ₁' la lb, lower ta = some la ∧ lower tb = some lb ∧ Agree (costVar :: Gh) σ₁ σ₁' ∧
      FlagsOK r ctx σ₁' ∧
      (∀ τ n, Exec Φ (if bv then la else lb).toCmd σ₁' τ n → Exec Φ d.toCmd σ' τ (w + n)) ∧
      (∀ n, Pre Φ (if bv then la else lb).toCmd σ₁' n → Pre Φ d.toCmd σ' (w + n)) := by
  rcases hc with ⟨g, hg, hσ, hb⟩ | ⟨hg, v, hσ, hb⟩
  · subst hσ
    obtain ⟨la, lb, hla, hlb, rfl⟩ := lower_ite_test hg hd
    have hind := c.test_indep (disjoint_spec hcl) g hg
    have hb' : decide (g.eval σ' ≤ 0) = bv := by rw [← hind _ σ' ha]; exact hb.symm
    refine ⟨σ', la, lb, hla, hlb, ha, hok, fun τ n e => ?_, fun n e => ?_⟩
    · cases bv
      · exact Exec.iteFalse (b := fun s => decide (g.eval s ≤ 0)) hb' e
      · exact Exec.iteTrue (b := fun s => decide (g.eval s ≤ 0)) hb' e
    · cases bv
      · exact Pre.iteFalse (b := fun s => decide (g.eval s ≤ 0)) hb' e
      · exact Pre.iteTrue (b := fun s => decide (g.eval s ≤ 0)) hb' e
  · subst hσ
    obtain ⟨la, lb, hla, hlb, rfl⟩ := lower_ite_other hg hd
    have hne : choiceVar ≠ r := fun e => h0 (e ▸ hr)
    refine ⟨Function.update σ' choiceVar v, la, lb, hla, hlb, ha.update _ _,
      JumpOK.update (o := .normal) hne (notin_okFlags hr hw h0) v hok, fun τ n e => ?_,
      fun n e => ?_⟩
    · have hb' : decide ((⟨unit choiceVar, 0⟩ : PExp).eval (Function.update σ' choiceVar v) ≤ 0)
          = bv := by rw [eval_unit]; simpa using hb.symm
      have e2 : Exec Φ (ACmd.ite w ⟨unit choiceVar, 0⟩ noSB noSB la lb).toCmd
          (Function.update σ' choiceVar v) τ (w + n) := by
        cases bv
        · exact Exec.iteFalse (b := fun s => decide ((⟨unit choiceVar, 0⟩ : PExp).eval s ≤ 0)) hb' e
        · exact Exec.iteTrue (b := fun s => decide ((⟨unit choiceVar, 0⟩ : PExp).eval s ≤ 0)) hb' e
      simpa [seqOf, ACmd.toCmd] using Exec.seq (exec_havoc (Φ := Φ) 0 choiceVar σ' v) e2
    · have hb' : decide ((⟨unit choiceVar, 0⟩ : PExp).eval (Function.update σ' choiceVar v) ≤ 0)
          = bv := by rw [eval_unit]; simpa using hb.symm
      have e2 : Pre Φ (ACmd.ite w ⟨unit choiceVar, 0⟩ noSB noSB la lb).toCmd
          (Function.update σ' choiceVar v) (w + n) := by
        cases bv
        · exact Pre.iteFalse (b := fun s => decide ((⟨unit choiceVar, 0⟩ : PExp).eval s ≤ 0)) hb' e
        · exact Pre.iteTrue (b := fun s => decide ((⟨unit choiceVar, 0⟩ : PExp).eval s ≤ 0)) hb' e
      simpa [seqOf, ACmd.toCmd] using Pre.seqRight (exec_havoc (Φ := Φ) 0 choiceVar σ' v) e2

/-- The result of a branch, carried to the conditional (the continuation is inside the
    branches). -/
theorem ite_res {G : List ℕ} {ctx : List Frame} {k : MStmt} {d cx : ACmd} {σ' σ₁' τ : Env}
    {o : Outcome} {n w : ℕ}
    (hrun : ∀ τ n, Exec Φ cx.toCmd σ₁' τ n → Exec Φ d.toCmd σ' τ (w + n))
    (hpre : ∀ n, Pre Φ cx.toCmd σ₁' n → Pre Φ d.toCmd σ' (w + n))
    (h : Res Φ G r ctx k cx σ₁' τ o n) : Res Φ G r ctx k d σ' τ o (w + n) := by
  cases o with
  | normal =>
    obtain ⟨τ', n', hn, ha, hok, ck, hck, h1, h2⟩ := h
    refine ⟨τ', w + n', by omega, ha, hok, ck, hck, fun υ n₂ e => ?_, fun n₂ e => ?_⟩
    · simpa [Nat.add_assoc] using hrun _ _ (h1 υ n₂ e)
    · simpa [Nat.add_assoc] using hpre _ (h2 n₂ e)
  | stop => obtain ⟨n', hn, hp⟩ := h; exact ⟨w + n', by omega, hpre _ hp⟩
  | brk => obtain ⟨τ', n', hn, ha, hj, he⟩ := h; exact ⟨τ', w + n', by omega, ha, hj, hrun _ _ he⟩
  | cont => obtain ⟨τ', n', hn, ha, hj, he⟩ := h; exact ⟨τ', w + n', by omega, ha, hj, hrun _ _ he⟩
  | ret => obtain ⟨τ', n', hn, ha, hj, he⟩ := h; exact ⟨τ', w + n', by omega, ha, hj, hrun _ _ he⟩

/-- The same when the branch was translated alone and the continuation follows the
    conditional. -/
theorem ite_res_seq {G : List ℕ} {ctx : List Frame} {k : MStmt} {d cx ck : ACmd}
    {σ' σ₁' τ : Env} {o : Outcome} {n w : ℕ} (hck : lower k = some ck)
    (hrun : ∀ τ n, Exec Φ cx.toCmd σ₁' τ n → Exec Φ d.toCmd σ' τ (w + n))
    (hpre : ∀ n, Pre Φ cx.toCmd σ₁' n → Pre Φ d.toCmd σ' (w + n))
    (ho : o = .normal ∨ o = .stop) (h : Res Φ G r ctx .skip cx σ₁' τ o n) :
    Res Φ G r ctx k (seqOf d ck) σ' τ o (w + n) := by
  rcases ho with rfl | rfl
  · obtain ⟨τ', n', hn, ha, hok, cs, hcs, h1, _⟩ := h
    simp [lower] at hcs; subst hcs
    have e := hrun _ _ (h1 τ' 0 (Exec.skip τ'))
    refine ⟨τ', w + n', by omega, ha, hok, ck, hck, fun υ n₂ e2 => ?_, fun n₂ p2 => ?_⟩
    · simpa [seqOf, ACmd.toCmd] using Exec.seq e e2
    · simpa [seqOf, ACmd.toCmd] using Pre.seqRight e p2
  · obtain ⟨n', hn, hp⟩ := h
    exact ⟨w + n', by omega, Pre.seqLeft (hpre _ hp)⟩

theorem fresh_spec (hr : r ∈ Gh) {ctx : List Frame} (hw : WF Gh ctx) {gh : List ℕ}
    (hF : freshGh r ctx gh = true) :
    gh.Nodup ∧ ∀ f ∈ gh, f ≠ r ∧ f ≠ choiceVar ∧ f ≠ costVar ∧ f ∉ okFlags r ctx := by
  simp only [freshGh, Bool.and_eq_true] at hF
  refine ⟨nodup_spec hF.1, fun f hf => ?_⟩
  have hd := disjoint_spec hF.2 f hf
  simp only [List.mem_cons, not_or] at hd
  refine ⟨hd.1, hd.2.1, hd.2.2.1, fun h => ?_⟩
  rcases (okFlags_mem hr hw f h).2 with h | h
  · exact hd.1 h
  · exact hd.2.2.2 h

theorem loopFrame_wf {ctx : List Frame} (hw : WF Gh ctx) {w : ℕ} {cs : List MCond} {body : JStmt}
    {inc : Option MStmt} {fb fc : Option ℕ}
    (hg : ∀ x ∈ (JStmt.loop w cs body inc fb fc).ghosts, x ∈ Gh) :
    WF Gh (loopFrame body fb fc :: ctx) := by
  intro fr hfr
  rcases List.mem_cons.mp hfr with rfl | hfr
  · refine ⟨fun f hf => by simpa [loopFrame] using hf, fun f hf => hg f ?_⟩
    simp only [loopFrame, List.mem_append] at hf
    simp only [JStmt.ghosts, List.mem_append]
    left
    rcases hf with hf | hf
    · left; split_ifs at hf <;> simp_all
    · right; split_ifs at hf <;> simp_all
  · exact hw fr hfr

theorem loop_ghosts_body {w : ℕ} {cs : List MCond} {body : JStmt} {inc : Option MStmt}
    {fb fc : Option ℕ} (hg : ∀ x ∈ (JStmt.loop w cs body inc fb fc).ghosts, x ∈ Gh) :
    ∀ x ∈ body.ghosts, x ∈ Gh := fun x hx => hg x (by simp [JStmt.ghosts, hx])

theorem loopExits_mem (hr : r ∈ Gh) {w : ℕ} {cs : List MCond} {body : JStmt}
    {inc : Option MStmt} {fb fc : Option ℕ}
    (hg : ∀ x ∈ (JStmt.loop w cs body inc fb fc).ghosts, x ∈ Gh) :
    ∀ f ∈ loopExits r body fb, f ∈ Gh := by
  intro f hf
  simp only [loopExits, List.mem_append] at hf
  rcases hf with hf | hf
  · apply hg; simp only [JStmt.ghosts, List.mem_append]; left; left
    split_ifs at hf <;> simp_all
  · split_ifs at hf <;> simp_all

/-- One iteration of the loop command: the test, then the `continue` flag cleared. -/
theorem loop_setup {ctx : List Frame} {w : ℕ} {cs : List MCond}
    {body : JStmt} {inc : Option MStmt} {fb fc : Option ℕ} {bd : MStmt} {cw : ACmd} {σ σ' : Env}
    (hg : ∀ x ∈ (JStmt.loop w cs body inc fb fc).ghosts, x ∈ Gh)
    (hcs : cs.all (cleanC Gh) = true)
    (hcw : lower (whileOf w cs (loopExits r body fb) (loopFrame body fb fc).fc bd inc) = some cw)
    (ha : Agree (costVar :: Gh) σ σ') (hok : FlagsOK r ctx σ')
    (hz : ∀ f ∈ loopExits r body fb, σ' f = 0) :
    ∃ (gsC : List PExp) (lcc lbd lig : ACmd), cs.mapM MCond.test = some gsC ∧ lower bd = some lbd ∧
      lower (incG (loopExits r body fb) inc) = some lig ∧
      cw.toCmd = Cmd.while w (fun s => gsC.all (fun g => decide (g.eval s ≤ 0)) &&
        (loopExits r body fb).all (fun f => decide (s f ≤ 0)))
        (Cmd.seq lcc.toCmd (Cmd.seq lbd.toCmd lig.toCmd)) ∧
      (∀ s s', Agree (costVar :: Gh) s s' → gsC.all (fun g => decide (g.eval s ≤ 0)) =
        gsC.all (fun g => decide (g.eval s' ≤ 0))) ∧
      ∃ σ₁', Exec Φ lcc.toCmd σ' σ₁' 0 ∧ Agree (costVar :: Gh) σ σ₁' ∧
        FlagsOK r (loopFrame body fb fc :: ctx) σ₁' ∧ (∀ f ∈ loopExits r body fb, σ₁' f = 0) ∧
        (∀ x, x ∉ (loopFrame body fb fc).fc.toList → σ₁' x = σ' x) := by
  obtain ⟨gsC, lcc, lbd, lig, hC, hcc, hbd, hig, heq⟩ := lower_whileOf hcw
  have hind : ∀ g ∈ gsC, Indep (costVar :: Gh) g :=
    mapM_test_indep (fun c hc => disjoint_spec (List.all_eq_true.mp hcs c hc)) gsC hC
  refine ⟨gsC, lcc, lbd, lig, hC, hbd, hig, heq, fun s s' h => all_indep hind h, ?_⟩
  have hfcG : ∀ f ∈ (loopFrame body fb fc).fc.toList, f ∈ costVar :: Gh := by
    intro f hf
    apply List.mem_cons_of_mem
    apply hg
    simp only [JStmt.ghosts, List.mem_append]; left; right
    simp only [loopFrame] at hf; split_ifs at hf <;> simp_all
  -- the `continue` flag cleared
  have hcl : ∃ σ₁', Exec Φ lcc.toCmd σ' σ₁' 0 ∧ (∀ f ∈ (loopFrame body fb fc).fc.toList, σ₁' f = 0) ∧
      (∀ x, x ∉ (loopFrame body fb fc).fc.toList → σ₁' x = σ' x) := by
    revert hcc
    cases (loopFrame body fb fc).fc with
    | none =>
      intro hcc; simp [lower] at hcc; subst hcc
      exact ⟨σ', Exec.skip σ', by simp, fun _ _ => rfl⟩
    | some f =>
      intro hcc; simp only [lower_flagSet, Option.some.injEq] at hcc; subst hcc
      refine ⟨Function.update σ' f 0, ?_, by simp, fun x hx => by
        simp at hx; simp [Function.update_of_ne hx]⟩
      have := Exec.atom (Φ := Φ) (w := 0)
        (r := fun s t => t = Function.update s f ((⟨[], 0⟩ : PExp).eval s)) (s := σ') rfl
      simpa [ACmd.toCmd, PExp.eval, dot] using this
  obtain ⟨σ₁', e, hz1, hk1⟩ := hcl
  refine ⟨σ₁', e, agree_sub _ hfcG hk1 ha, ?_, ?_, hk1⟩
  · intro f hf
    simp only [okFlags, List.mem_append] at hf
    rcases hf with ((hf | hf) | hf) | hf
    · by_cases hfc : f ∈ (loopFrame body fb fc).fc.toList
      · exact hz1 f hfc
      · rw [hk1 f hfc]; exact hz f (by simp only [loopExits, List.mem_append]; left; simpa [loopFrame] using hf)
    · exact hz1 f hf
    · by_cases hfc : f ∈ (loopFrame body fb fc).fc.toList
      · exact hz1 f hfc
      · rw [hk1 f hfc]
        apply hz f
        simp only [loopExits, List.mem_append]; right
        simp only [loopFrame] at hf; split_ifs at hf <;> simp_all
    · by_cases hfc : f ∈ (loopFrame body fb fc).fc.toList
      · exact hz1 f hfc
      · rw [hk1 f hfc]; exact hok f hf
  · intro f hf
    by_cases hfc : f ∈ (loopFrame body fb fc).fc.toList
    · exact hz1 f hfc
    · rw [hk1 f hfc]; exact hz f hf

theorem exec_flagSet (w f : ℕ) (k : ℤ) (σ : Env) :
    Exec Φ (ACmd.assign w f ⟨[], k⟩).toCmd σ (Function.update σ f k) w := by
  have := Exec.atom (Φ := Φ) (w := w)
    (r := fun s t => t = Function.update s f ((⟨[], k⟩ : PExp).eval s)) (s := σ) rfl
  simpa [ACmd.toCmd, PExp.eval, dot] using this

theorem set1_update {ctx : List Frame} {σ : Env} {f : ℕ} (hok : FlagsOK r ctx σ) :
    Set1 r ctx f (Function.update σ f 1) :=
  ⟨by simp, fun g hg hne => by rw [Function.update_of_ne hne]; exact hok g hg⟩

theorem cost_ne_r (hr : r ∈ Gh) (h1 : costVar ∉ Gh) : costVar ≠ r := fun e => h1 (e ▸ hr)

theorem loop_outcomes {w : ℕ} {cs : List MCond} {body : JStmt} {inc : Option MStmt}
    {fb fc : Option ℕ} {σ τ : Env} {o : Outcome} {n : ℕ}
    (h : JExec Φ (.loop w cs body inc fb fc) σ τ o n) :
    o ≠ .brk ∧ o ≠ .cont ∧ (o = .ret → body.hasRet = true) := by
  have := outcome_esc h
  exact ⟨fun e => by simpa [JStmt.escB] using this.1 e, fun e => by simpa [JStmt.escC] using this.2.1 e,
    fun e => by simpa [JStmt.hasRet] using this.2.2 e⟩

theorem exits_sub_ok {ctx : List Frame} {body : JStmt} {fb fc : Option ℕ} {f : ℕ}
    (hf : f ∈ loopExits r body fb) : f ∈ okFlags r (loopFrame body fb fc :: ctx) := by
  simp only [loopExits, List.mem_append] at hf
  simp only [okFlags, loopFrame, List.mem_append]
  rcases hf with hf | hf
  · left; left; left; exact hf
  · left; right; exact hf

theorem nearestCnt_loopFrame {ctx : List Frame} {body : JStmt} {fb fc : Option ℕ} :
    nearestCnt (loopFrame body fb fc :: ctx) = (loopFrame body fb fc).fc := by
  simp [nearestCnt, loopFrame]

/-- After a `continue`: the loop's other flags and the context's are 0. -/
theorem cont_flags (hr : r ∈ Gh) {ctx : List Frame} (hw : WF Gh ctx) {body : JStmt}
    {fb fc : Option ℕ} (hF : freshGh r ctx (loopFrame body fb fc).gh = true) {f : ℕ} {τ : Env}
    (hf : (loopFrame body fb fc).fc = some f) (hs : Set1 r (loopFrame body fb fc :: ctx) f τ) :
    FlagsOK r ctx τ ∧ ∀ g ∈ loopExits r body fb, τ g = 0 := by
  obtain ⟨hnd, hfr⟩ := fresh_spec hr hw hF
  have hfgh : f ∈ (loopFrame body fb fc).gh := by simp [loopFrame] at hf ⊢; simp [hf]
  obtain ⟨hfr', _, _, hfok⟩ := hfr f hfgh
  refine ⟨fun g hg => hs.2 g (okFlags_cons_sub hg) (fun e => hfok (e ▸ hg)), fun g hg => ?_⟩
  refine hs.2 g (exits_sub_ok hg) ?_
  rintro rfl
  simp only [loopExits, List.mem_append] at hg
  rcases hg with hg | hg
  · simp only [loopFrame] at hnd hf
    rw [List.nodup_append] at hnd
    exact hnd.2.2 hg (by simp [hf])
  · split_ifs at hg <;> simp at hg; exact hfr' hg

/-- After a `break` of the loop. -/
theorem brk_flags (hr : r ∈ Gh) {ctx : List Frame} (hw : WF Gh ctx) {body : JStmt}
    {fb fc : Option ℕ} (hF : freshGh r ctx (loopFrame body fb fc).gh = true) {f : ℕ} {τ : Env}
    (hf : (loopFrame body fb fc).fb = some f) (hs : Set1 r (loopFrame body fb fc :: ctx) f τ) :
    FlagsOK r ctx τ ∧ (body.hasRet = true → τ r = 0) ∧ f ∈ loopExits r body fb := by
  obtain ⟨_, hfr⟩ := fresh_spec hr hw hF
  have hfgh : f ∈ (loopFrame body fb fc).gh := by simp [loopFrame] at hf ⊢; simp [hf]
  obtain ⟨hfr', _, _, hfok⟩ := hfr f hfgh
  refine ⟨fun g hg => hs.2 g (okFlags_cons_sub hg) (fun e => hfok (e ▸ hg)), fun hrr => ?_, ?_⟩
  · exact hs.2 r (by simp [okFlags, loopFrame, hrr]) (fun e => hfr' e.symm)
  · simp only [loopFrame] at hf; simp [loopExits, hf]

/-- After a `return` in the loop's body. -/
theorem ret_flags {ctx : List Frame} {fr : Frame} {τ : Env} (hs : Set1 r (fr :: ctx) r τ) :
    τ r = 1 ∧ JumpOK r ctx .ret τ := by
  refine ⟨hs.1, ?_⟩
  cases ctx with
  | nil => exact Or.inl rfl
  | cons fr' ctx => exact Or.inr ⟨hs.1, fun g hg hne => hs.2 g (okFlags_cons_sub hg) hne⟩

/-- The body of a loop ended normally or by `continue`: the exit flags are 0. -/
theorem body_end (hr : r ∈ Gh) {ctx : List Frame} (hw : WF Gh ctx) {body : JStmt}
    {fb fc : Option ℕ} (hF : freshGh r ctx (loopFrame body fb fc).gh = true) {lbd : ACmd}
    {σ₁' υ : Env} {o₁ : Outcome} {n₁ : ℕ} (ho₁ : o₁ = .normal ∨ o₁ = .cont)
    (hres : Res Φ (costVar :: Gh) r (loopFrame body fb fc :: ctx) .skip lbd σ₁' υ o₁ n₁) :
    ∃ τ₁' n₁', n₁ ≤ n₁' ∧ Agree (costVar :: Gh) υ τ₁' ∧ FlagsOK r ctx τ₁' ∧
      (∀ f ∈ loopExits r body fb, τ₁' f = 0) ∧ Exec Φ lbd.toCmd σ₁' τ₁' n₁' := by
  rcases ho₁ with rfl | rfl
  · obtain ⟨τ₁', n₁', hn, ha', hok', cs, hcs, hrun, _⟩ := hres
    simp [lower] at hcs; subst hcs
    exact ⟨τ₁', n₁', hn, ha', fun f hf => hok' f (okFlags_cons_sub hf),
      fun f hf => hok' f (exits_sub_ok hf), by simpa using hrun τ₁' 0 (Exec.skip _)⟩
  · obtain ⟨τ₁', n₁', hn, ha', ⟨f, hf, hset⟩, eb⟩ := hres
    rw [nearestCnt_loopFrame] at hf
    obtain ⟨h1', h2'⟩ := cont_flags hr hw hF hf hset
    exact ⟨τ₁', n₁', hn, ha', h1', h2', eb⟩

/-- The increment, run when the exit flags are 0. -/
theorem inc_run (hΦ : ∀ p, p < nb → Quiet nb (costVar :: Gh) Gh (Φ p)) (h0 : choiceVar ∉ Gh) (h1 : costVar ∉ Gh)
    {exits : List ℕ} {inc : Option MStmt} {lig : ACmd} {υ υ' τ₁' : Env} {n₂ : ℕ}
    (hinc : incClean nb Gh inc = true) (hig : lower (incG exits inc) = some lig)
    (hm : MExec Φ (inc.getD .skip) υ υ' n₂) (ha : Agree (costVar :: Gh) υ τ₁')
    (hz : ∀ f ∈ exits, τ₁' f = 0) :
    ∃ υ'', Exec Φ lig.toCmd τ₁' υ'' n₂ ∧ Agree (costVar :: Gh) υ' υ'' ∧ Keeps Gh τ₁' υ'' := by
  cases inc with
  | none =>
    obtain ⟨c, hc, he⟩ := hm
    simp [lower] at hc; subst hc
    simp [incG, lower] at hig; subst hig
    cases he
    exact ⟨τ₁', Exec.skip _, ha, Keeps.refl _ _⟩
  | some u =>
    obtain ⟨c, hc, he⟩ := hm
    simp only [Option.getD_some] at hc
    obtain ⟨cu, hcu, h0', _⟩ := foldl_unless (Φ := Φ) τ₁' exits u lig hig
    rw [hc] at hcu; cases hcu
    obtain ⟨υ'', e, ha', hk⟩ := basic_exec hΦ h0 h1 hinc hc he ha
    exact ⟨υ'', (h0' fun f hf => by rw [hz f hf]).1 _ _ e, ha', hk⟩

theorem inc_pre (hΦ : ∀ p, p < nb → Quiet nb (costVar :: Gh) Gh (Φ p)) (h0 : choiceVar ∉ Gh) (h1 : costVar ∉ Gh)
    {exits : List ℕ} {inc : Option MStmt} {lig : ACmd} {υ τ₁' : Env} {n₂ : ℕ}
    (hinc : incClean nb Gh inc = true) (hig : lower (incG exits inc) = some lig)
    (hm : MPre Φ (inc.getD .skip) υ n₂) (ha : Agree (costVar :: Gh) υ τ₁')
    (hz : ∀ f ∈ exits, τ₁' f = 0) : Pre Φ lig.toCmd τ₁' n₂ := by
  cases inc with
  | none =>
    obtain ⟨c, hc, he⟩ := hm
    simp [lower] at hc; subst hc
    simp [incG, lower] at hig; subst hig
    rw [pre_skip he]; exact Pre.stop _ _
  | some u =>
    obtain ⟨c, hc, he⟩ := hm
    simp only [Option.getD_some] at hc
    obtain ⟨cu, hcu, h0', _⟩ := foldl_unless (Φ := Φ) τ₁' exits u lig hig
    rw [hc] at hcu; cases hcu
    exact (h0' fun f hf => by rw [hz f hf]).2 _ (basic_pre hΦ h0 h1 hinc hc he ha)

theorem tr_switch_inv {ctx : List Frame} {w sc : ℕ} {gs : List JStmt} {k m : MStmt}
    (h : tr r nb Gh ctx (.switch w sc gs) k = some m) :
    freshGh r ctx [sc] = true ∧ (JStmt.escCL gs = true → (nearestCnt ctx).isSome) ∧
    ∃ groups, trL r nb Gh (swFrame (JStmt.hasRetL gs) sc :: ctx) gs = some groups ∧
      m = .seq (if JStmt.hasRetL gs then flagSet 0 r 0 else .skip)
        (.seq (.seq (.cost w) (chainOf sc groups))
          (guardTail (if JStmt.hasRetL gs then some r else none)
            (if JStmt.escCL gs then nearestCnt ctx else none) k)) := by
  simp only [tr] at h
  generalize JStmt.hasRetL gs = R at h ⊢
  generalize JStmt.escCL gs = E at h ⊢
  cases R <;> cases E <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;>
    split_ifs at h with h1 h2 <;> simp_all
  all_goals
    obtain ⟨groups, hg, hm⟩ := Option.bind_eq_some.mp h
    cases hm
    simp_all [Option.isSome_iff_ne_none]
    exact ⟨groups, hg, rfl⟩

theorem rclear_run {rets : Bool} {c : ACmd} (h : lower (if rets then flagSet 0 r 0 else .skip) = some c)
    (σ : Env) : ∃ σ₁, Exec Φ c.toCmd σ σ₁ 0 ∧ (∀ x, x ≠ r → σ₁ x = σ x) ∧ (rets = true → σ₁ r = 0) ∧
      (rets = false → σ₁ = σ) := by
  cases rets with
  | false => simp [lower] at h; subst h; exact ⟨σ, Exec.skip σ, fun _ _ => rfl, by simp, fun _ => rfl⟩
  | true =>
    simp only [ite_true, lower_flagSet, Option.some.injEq] at h; subst h
    exact ⟨Function.update σ r 0, exec_flagSet 0 r 0 σ, fun x hx => by simp [Function.update_of_ne hx],
      fun _ => by simp, by simp⟩

theorem okFlags_swFrame {rets : Bool} {sc : ℕ} {ctx : List Frame} :
    okFlags r (swFrame rets sc :: ctx) = (if rets then [r] else []) ++ okFlags r ctx := by
  simp [okFlags, swFrame]

theorem sc_fresh (hr : r ∈ Gh) {ctx : List Frame} (hw : WF Gh ctx) {sc : ℕ}
    (hF : freshGh r ctx [sc] = true) {rets : Bool} :
    sc ≠ r ∧ sc ∉ okFlags r ctx ∧ sc ∉ okFlags r (swFrame rets sc :: ctx) := by
  obtain ⟨_, hfr⟩ := fresh_spec hr hw hF
  obtain ⟨h1, _, _, h4⟩ := hfr sc (by simp)
  refine ⟨h1, h4, ?_⟩
  rw [okFlags_swFrame]
  simp only [List.mem_append, not_or]
  refine ⟨?_, h4⟩
  split_ifs <;> simp [h1]

theorem ghostsL_drop (i : ℕ) : ∀ (gs : List JStmt) (x : ℕ), x ∈ JStmt.ghostsL (gs.drop i) →
    x ∈ JStmt.ghostsL gs := by
  induction i with
  | zero => intro gs x h; simpa using h
  | succ i ih =>
    intro gs x h
    cases gs with
    | nil => simpa using h
    | cons g gs => simp only [List.drop_succ_cons] at h; simp [JStmt.ghostsL, ih gs x h]

/-! ### The simulation -/

theorem notLoop {j : JStmt} (hj : ∀ w cs body inc fb fc, j ≠ .loop w cs body inc fb fc)
    {σ τ : Env} {o : Outcome} {n : ℕ} : LoopP Φ r nb Gh j σ τ o n :=
  fun w cs body inc fb fc heq => absurd heq (hj w cs body inc fb fc)

theorem notFall {j : JStmt} (hj : ∀ gs, j ≠ .fall gs) {σ τ : Env} {o : Outcome} {n : ℕ} :
    FallP Φ r nb Gh j σ τ o n :=
  fun gs heq => absurd heq (hj gs)

/-- **Simulation.** Every run of `j` in the direct semantics (`JExec`) is matched, from any
    state that agrees with its start outside the ghost variables and the cost variable
    and whose flags are 0, by a run of the lowering of `j`'s translation that costs at
    least as much and ends in a state that agrees with the end of the direct run outside
    those variables. -/
theorem sim (hΦ : ∀ p, p < nb → Quiet nb (costVar :: Gh) Gh (Φ p)) (hr : r ∈ Gh) (h0 : choiceVar ∉ Gh)
    (h1 : costVar ∉ Gh) {j : JStmt} {σ τ : Env} {o : Outcome} {n : ℕ}
    (h : JExec Φ j σ τ o n) :
    MainP Φ r nb Gh j σ τ o n ∧ LoopP Φ r nb Gh j σ τ o n ∧ FallP Φ r nb Gh j σ τ o n := by
  induction h with
  | stop =>
    refine ⟨?_, ?_, ?_⟩
    · intro _ _ _ _ _ _ _ _ σ' _ _; exact ⟨0, le_refl _, Pre.stop _ _⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ' _ _ _; exact ⟨0, le_refl _, Pre.stop _ _⟩
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ' _ _; exact ⟨0, le_refl _, Pre.stop _ _⟩
  | @basic s σ τ n hm =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    simp only [tr] at htr
    split_ifs at htr with hs
    cases htr
    obtain ⟨cs, ck, hcs, hck, rfl⟩ := lower_seq hl
    obtain ⟨c, hc, he⟩ := hm
    rw [hc] at hcs; cases hcs
    obtain ⟨τ', e, ha', hk⟩ := basic_exec hΦ h0 h1 hs hc he ha
    exact ⟨τ', n, le_refl _, ha', hok.keeps hr hw hk, ck, hck, fun υ n₂ e2 => Exec.seq e e2,
      fun n₂ p2 => Pre.seqRight e p2⟩
  | @basicS s σ n hm =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    simp only [tr] at htr
    split_ifs at htr with hs
    cases htr
    obtain ⟨cs, ck, hcs, hck, rfl⟩ := lower_seq hl
    obtain ⟨c, hc, he⟩ := hm
    rw [hc] at hcs; cases hcs
    exact ⟨n, le_refl _, Pre.seqLeft (basic_pre hΦ h0 h1 hs hc he ha)⟩
  | @seqN a b σ υ τ o n₁ n₂ _ _ ih₁ ih₂ =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    simp only [tr, Option.bind_eq_bind, Option.bind_eq_some] at htr
    obtain ⟨kb, hkb, hta⟩ := htr
    have hga : ∀ x ∈ a.ghosts, x ∈ Gh := fun x hx => hg x (by simp [JStmt.ghosts, hx])
    have hgb : ∀ x ∈ b.ghosts, x ∈ Gh := fun x hx => hg x (by simp [JStmt.ghosts, hx])
    obtain ⟨υ', n₁', hn₁, haυ, hokυ, ckb, hckb, hrun₁, hpre₁⟩ :=
      ih₁.1 ctx kb m cm hw hga hta hl σ' ha hok
    have hres := ih₂.1 ctx k kb ckb hw hgb hkb hckb υ' haυ hokυ
    cases o with
    | normal =>
      obtain ⟨τ', n₂', hn₂, ha', hok', ck, hck, hrun₂, hpre₂⟩ := hres
      refine ⟨τ', n₁' + n₂', by omega, ha', hok', ck, hck, fun υ n₃ e => ?_, fun n₃ e => ?_⟩
      · simpa [Nat.add_assoc] using hrun₁ _ _ (hrun₂ υ n₃ e)
      · simpa [Nat.add_assoc] using hpre₁ _ (hpre₂ n₃ e)
    | stop =>
      obtain ⟨n₂', hn₂, hp⟩ := hres
      exact ⟨n₁' + n₂', by omega, hpre₁ _ hp⟩
    | brk =>
      obtain ⟨τ', n₂', hn₂, ha', hj, he⟩ := hres
      exact ⟨τ', n₁' + n₂', by omega, ha', hj, hrun₁ _ _ he⟩
    | cont =>
      obtain ⟨τ', n₂', hn₂, ha', hj, he⟩ := hres
      exact ⟨τ', n₁' + n₂', by omega, ha', hj, hrun₁ _ _ he⟩
    | ret =>
      obtain ⟨τ', n₂', hn₂, ha', hj, he⟩ := hres
      exact ⟨τ', n₁' + n₂', by omega, ha', hj, hrun₁ _ _ he⟩
  | @seqJ a b σ τ o n _ ho ih =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    simp only [tr, Option.bind_eq_bind, Option.bind_eq_some] at htr
    obtain ⟨kb, hkb, hta⟩ := htr
    have hga : ∀ x ∈ a.ghosts, x ∈ Gh := fun x hx => hg x (by simp [JStmt.ghosts, hx])
    have hres := ih.1 ctx kb m cm hw hga hta hl σ' ha hok
    cases o with
    | normal => exact absurd rfl ho
    | stop => exact hres
    | brk => exact hres
    | cont => exact hres
    | ret => exact hres
  | @iteT w c a b σ σ₁ τ o n hc hx ih =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    have hgx : ∀ x ∈ a.ghosts, x ∈ Gh := fun x hx => hg x (by simp [JStmt.ghosts, hx])
    simp only [tr] at htr
    split_ifs at htr with hcl hend
    · simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
        Option.some.injEq] at htr
      obtain ⟨ta, hta, tb, htb, rfl⟩ := htr
      obtain ⟨σ₁', la, lb, hla, hlb, ha₁, hok₁, hrun, hpre⟩ :=
        ite_entry (Φ := Φ) h0 hr hw hl (by simpa using hcl) hc ha hok
      simp only [↓reduceIte, Bool.false_eq_true] at hrun hpre
      exact ite_res hrun hpre (ih.1 ctx k _ _ hw hgx hta hla σ₁' ha₁ hok₁)
    · simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
        Option.some.injEq] at htr
      obtain ⟨ta, hta, tb, htb, rfl⟩ := htr
      obtain ⟨d, ck, hd, hck, rfl⟩ := lower_seq hl
      obtain ⟨σ₁', la, lb, hla, hlb, ha₁, hok₁, hrun, hpre⟩ :=
        ite_entry (Φ := Φ) h0 hr hw hd (by simpa using hcl) hc ha hok
      simp only [↓reduceIte, Bool.false_eq_true] at hrun hpre
      have hesc := outcome_esc hx
      have ho : o = .normal ∨ o = .stop := by
        simp only [JStmt.ends, JStmt.hasRet, JStmt.escB, JStmt.escC, Bool.or_eq_true,
          not_or] at hend
        cases o with
        | normal => exact Or.inl rfl
        | stop => exact Or.inr rfl
        | brk => exact absurd (hesc.1 rfl) (by simp_all)
        | cont => exact absurd (hesc.2.1 rfl) (by simp_all)
        | ret => exact absurd (hesc.2.2 rfl) (by simp_all)
      exact ite_res_seq hck hrun hpre ho
        (ih.1 ctx .skip _ _ hw hgx hta hla σ₁' ha₁ hok₁)
  | @iteF w c a b σ σ₁ τ o n hc hx ih =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    have hgx : ∀ x ∈ b.ghosts, x ∈ Gh := fun x hx => hg x (by simp [JStmt.ghosts, hx])
    simp only [tr] at htr
    split_ifs at htr with hcl hend
    · simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
        Option.some.injEq] at htr
      obtain ⟨ta, hta, tb, htb, rfl⟩ := htr
      obtain ⟨σ₁', la, lb, hla, hlb, ha₁, hok₁, hrun, hpre⟩ :=
        ite_entry (Φ := Φ) h0 hr hw hl (by simpa using hcl) hc ha hok
      simp only [↓reduceIte, Bool.false_eq_true] at hrun hpre
      exact ite_res hrun hpre (ih.1 ctx k _ _ hw hgx htb hlb σ₁' ha₁ hok₁)
    · simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
        Option.some.injEq] at htr
      obtain ⟨ta, hta, tb, htb, rfl⟩ := htr
      obtain ⟨d, ck, hd, hck, rfl⟩ := lower_seq hl
      obtain ⟨σ₁', la, lb, hla, hlb, ha₁, hok₁, hrun, hpre⟩ :=
        ite_entry (Φ := Φ) h0 hr hw hd (by simpa using hcl) hc ha hok
      simp only [↓reduceIte, Bool.false_eq_true] at hrun hpre
      have hesc := outcome_esc hx
      have ho : o = .normal ∨ o = .stop := by
        simp only [JStmt.ends, JStmt.hasRet, JStmt.escB, JStmt.escC, Bool.or_eq_true,
          not_or] at hend
        cases o with
        | normal => exact Or.inl rfl
        | stop => exact Or.inr rfl
        | brk => exact absurd (hesc.1 rfl) (by simp_all)
        | cont => exact absurd (hesc.2.1 rfl) (by simp_all)
        | ret => exact absurd (hesc.2.2 rfl) (by simp_all)
      exact ite_res_seq hck hrun hpre ho
        (ih.1 ctx .skip _ _ hw hgx htb hlb σ₁' ha₁ hok₁)
  | @loopF w cs body inc fb fc σ ht =>
    have hL : LoopP Φ r nb Gh (.loop w cs body inc fb fc) σ σ .normal w := by
      intro w' cs' body' inc' fb' fc' heq ctx bd cw hw hg hB hC hF hcs hinc hbd hcw σ' ha hok hz
      cases heq
      obtain ⟨gsC, lcc, lbd, lig, hC', _, _, heq, hind, _⟩ := loop_setup (Φ := Φ) hg hcs hcw ha hok hz
      obtain ⟨gs, hgs, hf⟩ := ht
      rw [hC'] at hgs; cases hgs
      have hf' : gsC.all (fun g => decide (g.eval σ' ≤ 0)) = false := by
        rw [← hind _ σ' ha]; exact hf.symm
      refine ⟨σ', w, le_refl _, ha, hok, fun hrr => hz r (by simp [loopExits, hrr]), ?_⟩
      rw [heq]; exact Exec.whileFalse (by simp [hf'])
    exact ⟨loop_main hr hL (by simp) (by simp) (by simp), hL, notFall (by intros; simp)⟩
  | @loopN w cs body inc fb fc σ υ υ' τ o o₁ n₁ n₂ n₃ ht hb₁ ho₁ hinc₁ h₃ ih₁ ih₃ =>
    have hL : LoopP Φ r nb Gh (.loop w cs body inc fb fc) σ τ o (w + n₁ + n₂ + n₃) := by
      intro w' cs' body' inc' fb' fc' heq ctx bd cw hw hg hB hC hF hcs hinc hbd hcw σ' ha hok hz
      cases heq
      obtain ⟨gsC, lcc, lbd, lig, hC', hbd', hig, heq, hind, σ₁', e₁, ha₁, hok₁, _, _⟩ :=
        loop_setup (Φ := Φ) hg hcs hcw ha hok hz
      obtain ⟨gs, hgs, htv⟩ := ht
      rw [hC'] at hgs; cases hgs
      have htest : (gsC.all (fun g => decide (g.eval σ' ≤ 0)) &&
          (loopExits r body fb).all (fun f => decide (σ' f ≤ 0))) = true := by
        rw [← hind _ σ' ha, ← htv]; simp only [Bool.true_and, List.all_eq_true, decide_eq_true_eq]
        intro f hf; rw [hz f hf]
      obtain ⟨τ₁', n₁', hn₁, haτ, hokτ, hzτ, eb⟩ := body_end hr hw hF ho₁
        (ih₁.1 _ .skip bd lbd (loopFrame_wf hw hg) (loop_ghosts_body hg) hbd hbd' σ₁' ha₁ hok₁)
      obtain ⟨υ'', eu, haυ, hkυ⟩ := inc_run hΦ h0 h1 hinc hig hinc₁ haτ hzτ
      have hexG := loopExits_mem hr hg
      have hokυ := hokτ.keeps hr hw hkυ
      have hzυ : ∀ f ∈ loopExits r body fb, υ'' f = 0 := fun f hf => by
        rw [hkυ f (hexG f hf)]; exact hzτ f hf
      have hiter := Exec.seq e₁ (Exec.seq eb eu)
      have htail := ih₃.2.1 w cs body inc fb fc rfl ctx bd cw hw hg hB hC hF hcs hinc hbd hcw υ''
        haυ hokυ hzυ
      cases o with
      | normal =>
        obtain ⟨τ', n₃', hn₃, ha', hok', hr', e3⟩ := htail
        rw [heq] at e3
        refine ⟨τ', w + (0 + (n₁' + n₂)) + n₃', by omega, ha', hok', hr', ?_⟩
        rw [heq]; exact Exec.whileTrue htest hiter e3
      | stop =>
        obtain ⟨n₃', hn₃, p3⟩ := htail
        rw [heq] at p3
        refine ⟨w + (0 + (n₁' + n₂)) + n₃', by omega, ?_⟩
        rw [heq]; exact Pre.whileNext htest hiter p3
      | ret =>
        obtain ⟨τ', n₃', hn₃, ha', hr1, hj, e3⟩ := htail
        rw [heq] at e3
        refine ⟨τ', w + (0 + (n₁' + n₂)) + n₃', by omega, ha', hr1, hj, ?_⟩
        rw [heq]; exact Exec.whileTrue htest hiter e3
      | brk => trivial
      | cont => trivial
    have hlo := loop_outcomes (JExec.loopN (Φ := Φ) ⟨_, ht.choose_spec.1, ht.choose_spec.2⟩ hb₁ ho₁ hinc₁ h₃)
    exact ⟨loop_main hr hL hlo.1 hlo.2.1 hlo.2.2, hL, notFall (by intros; simp)⟩
  | @loopIS w cs body inc fb fc σ υ o₁ n₁ n₂ ht hb₁ ho₁ hinc₁ ih₁ =>
    have hL : LoopP Φ r nb Gh (.loop w cs body inc fb fc) σ υ .stop (w + n₁ + n₂) := by
      intro w' cs' body' inc' fb' fc' heq ctx bd cw hw hg hB hC hF hcs hinc hbd hcw σ' ha hok hz
      cases heq
      obtain ⟨gsC, lcc, lbd, lig, hC', hbd', hig, heq, hind, σ₁', e₁, ha₁, hok₁, _, _⟩ :=
        loop_setup (Φ := Φ) hg hcs hcw ha hok hz
      obtain ⟨gs, hgs, htv⟩ := ht
      rw [hC'] at hgs; cases hgs
      have htest : (gsC.all (fun g => decide (g.eval σ' ≤ 0)) &&
          (loopExits r body fb).all (fun f => decide (σ' f ≤ 0))) = true := by
        rw [← hind _ σ' ha, ← htv]; simp only [Bool.true_and, List.all_eq_true, decide_eq_true_eq]
        intro f hf; rw [hz f hf]
      obtain ⟨τ₁', n₁', hn₁, haτ, _, hzτ, eb⟩ := body_end hr hw hF ho₁
        (ih₁.1 _ .skip bd lbd (loopFrame_wf hw hg) (loop_ghosts_body hg) hbd hbd' σ₁' ha₁ hok₁)
      have pu := inc_pre hΦ h0 h1 hinc hig hinc₁ haτ hzτ
      refine ⟨w + (0 + (n₁' + n₂)), by omega, ?_⟩
      rw [heq]; exact Pre.whileBody htest (Pre.seqRight e₁ (Pre.seqRight eb pu))
    exact ⟨loop_main hr hL (by simp) (by simp) (by simp), hL, notFall (by intros; simp)⟩
  | @loopX w cs body inc fb fc σ τ o n₁ ht hb₁ ho ih₁ =>
    have hL : LoopP Φ r nb Gh (.loop w cs body inc fb fc) σ τ o.catchBrk (w + n₁) := by
      intro w' cs' body' inc' fb' fc' heq ctx bd cw hw hg hB hC hF hcs hinc hbd hcw σ' ha hok hz
      cases heq
      obtain ⟨gsC, lcc, lbd, lig, hC', hbd', hig, heq, hind, σ₁', e₁, ha₁, hok₁, _, _⟩ :=
        loop_setup (Φ := Φ) hg hcs hcw ha hok hz
      obtain ⟨gs, hgs, htv⟩ := ht
      rw [hC'] at hgs; cases hgs
      have htest : (gsC.all (fun g => decide (g.eval σ' ≤ 0)) &&
          (loopExits r body fb).all (fun f => decide (σ' f ≤ 0))) = true := by
        rw [← hind _ σ' ha, ← htv]; simp only [Bool.true_and, List.all_eq_true, decide_eq_true_eq]
        intro f hf; rw [hz f hf]
      have hres := ih₁.1 _ .skip bd lbd (loopFrame_wf hw hg) (loop_ghosts_body hg) hbd hbd' σ₁' ha₁ hok₁
      -- a set exit flag: the increment and the next test do nothing
      have hexit : ∀ τ₁', (∃ f ∈ loopExits r body fb, τ₁' f = 1) →
          Exec Φ lig.toCmd τ₁' τ₁' 0 ∧ Exec Φ cw.toCmd τ₁' τ₁' w := by
        intro τ₁' ⟨f, hf, hf1⟩
        refine ⟨?_, ?_⟩
        · cases inc with
          | none => simp [incG, lower] at hig; subst hig; exact Exec.skip _
          | some u =>
            obtain ⟨_, _, _, hpos⟩ := foldl_unless (Φ := Φ) τ₁' _ u lig hig
            exact hpos ⟨f, hf, by rw [hf1]; norm_num⟩
        · rw [heq]
          apply Exec.whileFalse
          simp only [Bool.and_eq_false_iff]
          right
          simp only [List.all_eq_false, decide_eq_false_iff_not, not_le]
          exact ⟨f, hf, by rw [hf1]; norm_num⟩
      rcases ho with rfl | rfl | rfl
      · obtain ⟨τ₁', n₁', hn, ha', hj, eb⟩ := hres
        simp only [JumpOK, loopFrame, Bool.false_eq_true, ite_false] at hj
        obtain ⟨f, hf, hset⟩ := hj
        obtain ⟨hok', hr0, hfe⟩ := brk_flags hr hw hF (by simpa [loopFrame] using hf) hset
        obtain ⟨ei, ew⟩ := hexit τ₁' ⟨f, hfe, hset.1⟩
        rw [heq] at ew
        refine ⟨τ₁', w + (0 + (n₁' + 0)) + w, by omega, ha', hok', hr0, ?_⟩
        rw [heq]; exact Exec.whileTrue htest (Exec.seq e₁ (Exec.seq eb ei)) ew
      · obtain ⟨τ₁', n₁', hn, ha', hj, eb⟩ := hres
        rcases hj with hj | hj
        · simp at hj
        · obtain ⟨hr1, hj'⟩ := ret_flags hj
          have hrr := (outcome_esc hb₁).2.2 rfl
          obtain ⟨ei, ew⟩ := hexit τ₁' ⟨r, by simp [loopExits, hrr], hr1⟩
          rw [heq] at ew
          refine ⟨τ₁', w + (0 + (n₁' + 0)) + w, by omega, ha', hr1, hj', ?_⟩
          rw [heq]; exact Exec.whileTrue htest (Exec.seq e₁ (Exec.seq eb ei)) ew
      · obtain ⟨n₁', hn, pb⟩ := hres
        refine ⟨w + (0 + n₁'), by omega, ?_⟩
        rw [heq]; exact Pre.whileBody htest (Pre.seqRight e₁ (Pre.seqLeft pb))
    have hlo := loop_outcomes (JExec.loopX (Φ := Φ) (w := w) (inc := inc) (fb := fb) (fc := fc) ht hb₁ ho)
    exact ⟨loop_main hr hL hlo.1 hlo.2.1 hlo.2.2, hL, notFall (by intros; simp)⟩
  | @brk w σ =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    cases ctx with
    | nil => simp [tr] at htr
    | cons fr ctx =>
      simp only [tr] at htr
      split_ifs at htr with hsw
      · cases htr
        simp only [lower_cost, Option.some.injEq] at hl; subst hl
        refine ⟨Function.update σ' costVar 0, w, le_refl _,
          ha.update_right (List.mem_cons_self _ _) 0, ?_, exec_havoc w costVar σ' 0⟩
        simp only [JumpOK, hsw, ite_true]
        exact JumpOK.update (o := .normal) (cost_ne_r hr h1) (notin_okFlags hr hw h1) 0 hok
      · obtain ⟨f, hf, rfl⟩ := Option.map_eq_some'.mp htr
        simp only [lower_flagSet, Option.some.injEq] at hl; subst hl
        have hfG : f ∈ Gh :=
          (hw fr (List.mem_cons_self _ _)).2 f ((hw fr (List.mem_cons_self _ _)).1 f (by simp [hf]))
        refine ⟨Function.update σ' f 1, w, le_refl _,
          ha.update_right (List.mem_cons_of_mem _ hfG) 1, ?_, exec_flagSet w f 1 σ'⟩
        simp only [JumpOK, hsw]
        exact ⟨f, hf, set1_update hok⟩
  | @cont w σ =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    simp only [tr] at htr
    obtain ⟨f, hf, rfl⟩ := Option.map_eq_some'.mp htr
    simp only [lower_flagSet, Option.some.injEq] at hl; subst hl
    obtain ⟨_, fr, hfr, hffc⟩ := nearestCnt_mem (r := r) hf
    have hfG : f ∈ Gh := (hw fr hfr).2 f ((hw fr hfr).1 f (by simp at hffc ⊢; simp [hffc]))
    exact ⟨Function.update σ' f 1, w, le_refl _, ha.update_right (List.mem_cons_of_mem _ hfG) 1,
      ⟨f, hf, set1_update hok⟩, exec_flagSet w f 1 σ'⟩
  | @ret s σ τ n hm =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    simp only [tr] at htr
    split_ifs at htr with hs
    obtain ⟨c, hc, he⟩ := hm
    have hs' : cleanS nb Gh s = true := by simpa using hs
    cases ctx with
    | nil =>
      cases htr
      rw [hc] at hl; cases hl
      obtain ⟨τ', e, ha', _⟩ := basic_exec hΦ h0 h1 hs' hc he ha
      exact ⟨τ', n, le_refl _, ha', Or.inl rfl, e⟩
    | cons fr ctx =>
      cases htr
      obtain ⟨cs, cf, hcs, hcf, rfl⟩ := lower_seq hl
      rw [hc] at hcs; cases hcs
      simp only [lower_flagSet, Option.some.injEq] at hcf; subst hcf
      obtain ⟨τ', e, ha', hk⟩ := basic_exec hΦ h0 h1 hs' hc he ha
      refine ⟨Function.update τ' r 1, n + 0, by omega, ha'.update_right (List.mem_cons_of_mem _ hr) 1,
        Or.inr (set1_update (hok.keeps hr hw hk)), Exec.seq e (exec_flagSet 0 r 1 τ')⟩
  | @retS s σ n hm =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    simp only [tr] at htr
    split_ifs at htr with hs
    obtain ⟨c, hc, he⟩ := hm
    have hs' : cleanS nb Gh s = true := by simpa using hs
    cases ctx with
    | nil =>
      cases htr
      rw [hc] at hl; cases hl
      exact ⟨n, le_refl _, basic_pre hΦ h0 h1 hs' hc he ha⟩
    | cons fr ctx =>
      cases htr
      obtain ⟨cs, cf, hcs, hcf, rfl⟩ := lower_seq hl
      rw [hc] at hcs; cases hcs
      exact ⟨n, le_refl _, Pre.seqLeft (basic_pre hΦ h0 h1 hs' hc he ha)⟩
  | @switchS w sc gs σ n hm =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    obtain ⟨_, _, groups, _, rfl⟩ := tr_switch_inv htr
    obtain ⟨c1, c2, hc1, hc2, rfl⟩ := lower_seq hl
    obtain ⟨c3, _, hc3, _, rfl⟩ := lower_seq hc2
    obtain ⟨c4, _, hc4, _, rfl⟩ := lower_seq hc3
    obtain ⟨σ₁, e1, hk1, _, _⟩ := rclear_run (Φ := Φ) hc1 σ'
    have ha1 : Agree (costVar :: Gh) σ σ₁ := fun x hx => by
      rw [hk1 x (fun e => hx (e ▸ List.mem_cons_of_mem _ hr))]; exact ha x hx
    obtain ⟨c, hc, he⟩ := hm
    rw [hc] at hc4; cases hc4
    exact ⟨0 + n, by omega, Pre.seqRight e1 (Pre.seqLeft (Pre.seqLeft
      (basic_pre hΦ h0 h1 (by simp [cleanS, MStmt.vars, MStmt.callsBelow, disjoint]) hc he ha1)))⟩
  | @switch w sc gs σ σ₁ τ o n i h₀ hi hf ih =>
    refine ⟨?_, notLoop (by intros; simp), notFall (by intros; simp)⟩
    intro ctx k m cm hw hg htr hl σ' ha hok
    obtain ⟨hF, hnc, groups, hgr, rfl⟩ := tr_switch_inv htr
    obtain ⟨c1, c2, hc1, hc2, rfl⟩ := lower_seq hl
    obtain ⟨c3, cg, hc3, hcg, rfl⟩ := lower_seq hc2
    obtain ⟨c4, cch, hc4, hcch, rfl⟩ := lower_seq hc3
    have hscG : sc ∈ Gh := hg sc (by simp [JStmt.ghosts])
    obtain ⟨hscr, hsc0, hsc1⟩ := sc_fresh (rets := JStmt.hasRetL gs) hr hw hF
    have hw' : WF Gh (swFrame (JStmt.hasRetL gs) sc :: ctx) := by
      intro fr hfr
      rcases List.mem_cons.mp hfr with rfl | hfr
      · exact ⟨by simp [swFrame], fun f hf => by simp [swFrame] at hf; subst hf; exact hscG⟩
      · exact hw fr hfr
    -- the return flag cleared, the test's cost, the groups before the one entered skipped
    obtain ⟨σ₁', e1, hk1, hz1, hs1⟩ := rclear_run (Φ := Φ) hc1 σ'
    have ha1 : Agree (costVar :: Gh) σ σ₁' := fun x hx => by
      rw [hk1 x (fun e => hx (e ▸ List.mem_cons_of_mem _ hr))]; exact ha x hx
    have hok1 : FlagsOK r ctx σ₁' := by
      cases hrr : JStmt.hasRetL gs
      · rw [hs1 hrr]; exact hok
      · intro f hf
        by_cases hfr : f = r
        · subst hfr; exact hz1 hrr
        · rw [hk1 f hfr]; exact hok f hf
    obtain ⟨c, hc, he⟩ := h₀
    have hcc : c = c4 := Option.some.inj (hc.symm.trans hc4)
    subst hcc
    obtain ⟨σ₂', e2, ha2, hk2⟩ :=
      basic_exec hΦ h0 h1 (by simp [cleanS, MStmt.vars, MStmt.callsBelow, disjoint]) hc he ha1
    obtain ⟨dr, hdr, hrun⟩ := chain_drop (Φ := Φ) sc i groups cch hcch
    obtain ⟨σ₃, hk3, hE, hP⟩ := hrun σ₂'
    have ha3 : Agree (costVar :: Gh) σ₁ σ₃ := fun x hx => by
      have : x ≠ sc := fun e => hx (e ▸ List.mem_cons_of_mem _ hscG)
      rw [hk3 x this]; exact ha2 x hx
    have hok3 : FlagsOK r (swFrame (JStmt.hasRetL gs) sc :: ctx) σ₃ := by
      intro f hf
      have hfsc : f ≠ sc := fun e => hsc1 (e ▸ hf)
      rw [hk3 f hfsc]
      rw [okFlags_swFrame, List.mem_append] at hf
      rcases hf with hf | hf
      · split_ifs at hf with hrr
        · simp at hf; subst hf; rw [hk2 _ hr]; exact hz1 hrr
        · simp at hf
      · rw [hk2 f (okFlags_mem hr hw f hf).1]; exact hok1 f hf
    have hgf : ∀ x ∈ (JStmt.fall (gs.drop i)).ghosts, x ∈ Gh := fun x hx =>
      hg x (by simp only [JStmt.ghosts] at hx ⊢; exact List.mem_cons_of_mem _ (ghostsL_drop i gs x hx))
    have hres := ih.2.2 (gs.drop i) rfl ctx (JStmt.hasRetL gs) sc (groups.drop i) dr hw' hgf hscG
      hscr hsc0 (trL_drop i gs groups hgr) hdr σ₃ ha3 hok3
    have hgt := guardTail_run (Φ := Φ) hcg
    have hesc := outcome_esc hf
    have hzero : ∀ τ', FlagsOK r (swFrame (JStmt.hasRetL gs) sc :: ctx) τ' →
        ∀ f ∈ (if JStmt.hasRetL gs then some r else none).toList ++
          (if JStmt.escCL gs then nearestCnt ctx else none).toList, τ' f ≤ 0 := by
      intro τ' hj f hf
      simp only [List.mem_append] at hf
      rcases hf with hf | hf
      · split_ifs at hf with hrr
        · simp at hf; subst hf; rw [hj _ (by rw [okFlags_swFrame]; simp [hrr])]
        · simp at hf
      · split_ifs at hf with hec
        · rw [hj f (okFlags_cons_sub (nearestCnt_mem (by simpa using hf)).1)]
        · simp at hf
    have hnorm : ∀ τ' n', Exec Φ dr.toCmd σ₃ τ' n' → Agree (costVar :: Gh) τ τ' →
        FlagsOK r (swFrame (JStmt.hasRetL gs) sc :: ctx) τ' →
        Res Φ (costVar :: Gh) r ctx k (seqOf c1 (seqOf (seqOf c cch) cg)) σ' τ .normal (w + n) ∨
          n' < n := by
      intro τ' n' ed ha' hj
      by_cases hn : n' < n
      · exact Or.inr hn
      left
      have eb := Exec.seq e2 (hE τ' n' ed)
      obtain ⟨ck, hck, hrun, hpre⟩ := hgt.1 τ' (hzero τ' hj)
      refine ⟨τ', 0 + (w + n'), by omega, ha', fun f hf => hj f (okFlags_cons_sub hf), ck, hck,
        fun υ n₂ e3 => ?_, fun n₂ p3 => ?_⟩
      · have := Exec.seq e1 (Exec.seq eb (hrun υ n₂ e3))
        simpa [seqOf, ACmd.toCmd, Nat.add_assoc] using this
      · have := Pre.seqRight e1 (Pre.seqRight eb (hpre n₂ p3))
        simpa [seqOf, ACmd.toCmd, Nat.add_assoc] using this
    cases o with
    | normal =>
      obtain ⟨τ', n', hn, ha', hj, ed⟩ := hres
      rcases hnorm τ' n' ed ha' hj with h | h
      · exact h
      · omega
    | brk =>
      obtain ⟨τ', n', hn, ha', hj, ed⟩ := hres
      simp only [JumpOK, swFrame, ite_true] at hj
      rcases hnorm τ' n' ed ha' hj with h | h
      · exact h
      · omega
    | stop =>
      obtain ⟨n', hn, pd⟩ := hres
      refine ⟨0 + (w + n'), by omega, ?_⟩
      exact Pre.seqRight e1 (Pre.seqLeft (Pre.seqRight e2 (hP n' pd)))
    | cont =>
      obtain ⟨τ', n', hn, ha', ⟨f, hf, hset⟩, ed⟩ := hres
      have hf' : nearestCnt ctx = some f := by simpa [nearestCnt, swFrame] using hf
      have hec : JStmt.escCL gs = true := by
        have := hesc.2.1 rfl
        simp only [JStmt.escC] at this
        exact (escL_drop i gs).1 this
      have eg := hgt.2 τ' ⟨f, by simp [hec, hf'], by rw [hset.1]; norm_num⟩
      refine ⟨τ', 0 + (w + n' + 0), by omega, ha',
        ⟨f, hf', hset.1, fun g hg hne => hset.2 g (okFlags_cons_sub hg) hne⟩, ?_⟩
      have := Exec.seq e1 (Exec.seq (Exec.seq e2 (hE τ' n' ed)) eg)
      simpa [seqOf, ACmd.toCmd, Nat.add_assoc] using this
    | ret =>
      obtain ⟨τ', n', hn, ha', hj, ed⟩ := hres
      rcases hj with hj | hj
      · simp at hj
      obtain ⟨hr1, hj'⟩ := ret_flags hj
      have hrr : JStmt.hasRetL gs = true := by
        have := hesc.2.2 rfl
        simp only [JStmt.hasRet] at this
        exact (escL_drop i gs).2 this
      have eg := hgt.2 τ' ⟨r, by simp [hrr], by rw [hr1]; norm_num⟩
      refine ⟨τ', 0 + (w + n' + 0), by omega, ha', hj', ?_⟩
      have := Exec.seq e1 (Exec.seq (Exec.seq e2 (hE τ' n' ed)) eg)
      simpa [seqOf, ACmd.toCmd, Nat.add_assoc] using this
  | @fallNil σ =>
    refine ⟨fun ctx k m cm _ _ htr => by simp [tr] at htr, notLoop (by intros; simp), ?_⟩
    intro gs heq ctx0 rets sc groups cc hw hg hsc hscr hsc0 htrL hcc σ' ha hok
    cases heq
    simp [trL] at htrL; subst htrL
    simp [chainOf, lower] at hcc; subst hcc
    exact ⟨σ', 0, le_refl _, ha, hok, Exec.skip σ'⟩
  | @fallN g gs σ υ τ o n₁ n₂ _ _ ih₁ ih₂ =>
    refine ⟨fun ctx k m cm _ _ htr => by simp [tr] at htr, notLoop (by intros; simp), ?_⟩
    intro gs' heq ctx0 rets sc groups cc hw hg hsc hscr hsc0 htrL hcc σ' ha hok
    cases heq
    simp only [trL, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
      Option.some.injEq] at htrL
    obtain ⟨g', hg', gs'', hgs'', rfl⟩ := htrL
    obtain ⟨dg, dr, hdg, hdr, rfl⟩ := lower_chain_cons hcc
    obtain ⟨cg, hcg, henter, _, _⟩ := group_enter (Φ := Φ) hdg
    have hsc1 : sc ∉ okFlags r (swFrame rets sc :: ctx0) := by
      rw [okFlags_swFrame]; simp only [List.mem_append, not_or]
      exact ⟨by split_ifs <;> simp [hscr], hsc0⟩
    have hgg : ∀ x ∈ g.ghosts, x ∈ Gh := fun x hx => hg x (by simp [JStmt.ghosts, JStmt.ghostsL, hx])
    have hgr : ∀ x ∈ (JStmt.fall gs).ghosts, x ∈ Gh :=
      fun x hx => hg x (by simp only [JStmt.ghosts, JStmt.ghostsL] at hx ⊢; simp [hx])
    have ha1 : Agree (costVar :: Gh) σ (Function.update σ' sc 0) :=
      ha.update_right (List.mem_cons_of_mem _ hsc) 0
    have hok1 : FlagsOK r (swFrame rets sc :: ctx0) (Function.update σ' sc 0) :=
      JumpOK.update (o := .normal) hscr hsc1 0 hok
    obtain ⟨τ₁', n₁', hn₁, haτ, hokτ, cs, hcs, hrun, _⟩ :=
      ih₁.1 _ .skip g' cg hw hgg hg' hcg _ ha1 hok1
    simp [lower] at hcs; subst hcs
    have eg := henter σ' τ₁' (n₁' + 0) (hrun τ₁' 0 (Exec.skip _))
    have hres := ih₂.2.2 gs rfl ctx0 rets sc gs'' dr hw hgr hsc hscr hsc0 hgs'' hdr τ₁' haτ hokτ
    cases o with
    | stop =>
      obtain ⟨n₂', hn₂, p2⟩ := hres
      exact ⟨n₁' + 0 + n₂', by omega, Pre.seqRight eg p2⟩
    | normal =>
      obtain ⟨τ', n₂', hn₂, ha', hj, e2⟩ := hres
      exact ⟨τ', n₁' + 0 + n₂', by omega, ha', hj, Exec.seq eg e2⟩
    | brk =>
      obtain ⟨τ', n₂', hn₂, ha', hj, e2⟩ := hres
      exact ⟨τ', n₁' + 0 + n₂', by omega, ha', hj, Exec.seq eg e2⟩
    | cont =>
      obtain ⟨τ', n₂', hn₂, ha', hj, e2⟩ := hres
      exact ⟨τ', n₁' + 0 + n₂', by omega, ha', hj, Exec.seq eg e2⟩
    | ret =>
      obtain ⟨τ', n₂', hn₂, ha', hj, e2⟩ := hres
      exact ⟨τ', n₁' + 0 + n₂', by omega, ha', hj, Exec.seq eg e2⟩
  | @fallJ g gs σ τ o n _ ho ih =>
    refine ⟨fun ctx k m cm _ _ htr => by simp [tr] at htr, notLoop (by intros; simp), ?_⟩
    intro gs' heq ctx0 rets sc groups cc hw hg hsc hscr hsc0 htrL hcc σ' ha hok
    cases heq
    simp only [trL, Option.bind_eq_bind, Option.bind_eq_some, Option.pure_def,
      Option.some.injEq] at htrL
    obtain ⟨g', hg', gs'', hgs'', rfl⟩ := htrL
    obtain ⟨dg, dr, hdg, hdr, rfl⟩ := lower_chain_cons hcc
    obtain ⟨cg, hcg, henter, hpenter, _⟩ := group_enter (Φ := Φ) hdg
    have hsc1 : sc ∉ okFlags r (swFrame rets sc :: ctx0) := by
      rw [okFlags_swFrame]; simp only [List.mem_append, not_or]
      exact ⟨by split_ifs <;> simp [hscr], hsc0⟩
    have hgg : ∀ x ∈ g.ghosts, x ∈ Gh := fun x hx => hg x (by simp [JStmt.ghosts, JStmt.ghostsL, hx])
    have ha1 : Agree (costVar :: Gh) σ (Function.update σ' sc 0) :=
      ha.update_right (List.mem_cons_of_mem _ hsc) 0
    have hok1 : FlagsOK r (swFrame rets sc :: ctx0) (Function.update σ' sc 0) :=
      JumpOK.update (o := .normal) hscr hsc1 0 hok
    have hres := ih.1 _ .skip g' cg hw hgg hg' hcg _ ha1 hok1
    -- the groups after a jump are skipped
    have hskip : ∀ (τ' : Env) (o' : Outcome), Agree (costVar :: Gh) τ τ' →
        JumpOK r (swFrame rets sc :: ctx0) o' τ' →
        ∃ τ₂, Exec Φ dr.toCmd τ' τ₂ 0 ∧ Agree (costVar :: Gh) τ τ₂ ∧
          JumpOK r (swFrame rets sc :: ctx0) o' τ₂ := by
      intro τ' o' ha' hj
      obtain ⟨τ₂, e, hk⟩ := chain_skip (Φ := Φ) sc gs'' dr hdr τ'
      refine ⟨τ₂, e, fun x hx => ?_, hj.congr fun f hf => hk f ?_⟩
      · rw [hk x (fun e => hx (e ▸ List.mem_cons_of_mem _ hsc))]; exact ha' x hx
      · rintro rfl
        rcases hf with hf | hf
        · exact hscr hf
        · exact hsc1 hf
    cases o with
    | normal => exact absurd rfl ho
    | stop =>
      obtain ⟨n', hn, p⟩ := hres
      exact ⟨n', hn, Pre.seqLeft (hpenter σ' n' p)⟩
    | brk =>
      obtain ⟨τ', n', hn, ha', hj, e⟩ := hres
      obtain ⟨τ₂, e2, ha2, hj2⟩ := hskip τ' _ ha' hj
      exact ⟨τ₂, n' + 0, by omega, ha2, hj2, Exec.seq (henter σ' τ' n' e) e2⟩
    | cont =>
      obtain ⟨τ', n', hn, ha', hj, e⟩ := hres
      obtain ⟨τ₂, e2, ha2, hj2⟩ := hskip τ' _ ha' hj
      exact ⟨τ₂, n' + 0, by omega, ha2, hj2, Exec.seq (henter σ' τ' n' e) e2⟩
    | ret =>
      obtain ⟨τ', n', hn, ha', hj, e⟩ := hres
      obtain ⟨τ₂, e2, ha2, hj2⟩ := hskip τ' _ ha' hj
      exact ⟨τ₂, n' + 0, by omega, ha2, hj2, Exec.seq (henter σ' τ' n' e) e2⟩

end Sim

/-! ### Called functions that do not touch the ghost variables -/

theorem indep_of_zeroOn {G : List ℕ} {p : PExp} (h : zeroOn G p.sv = true) : Indep G p := by
  intro σ σ' ha
  simp only [PExp.eval]
  congr 1
  apply dot_congr
  intro i
  by_cases hi : i ∈ G
  · left
    simp only [zeroOn, List.all_eq_true, beq_iff_eq] at h
    exact h i hi
  · right; exact ha i hi

theorem quiet_of_quietB {nq : ℕ} {G W : List ℕ} : ∀ c : ACmd, quietCmd nq G W c = true →
    Quiet nq G W c.toCmd := by
  intro c
  induction c with
  | skip => intro _; trivial
  | assign w x a =>
    intro h; simp only [quietCmd, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact quiet_assign (by simpa using h.1) (indep_of_zeroOn h.2)
  | havoc w x =>
    intro h; simp only [quietCmd, Bool.not_eq_true'] at h
    exact quiet_havoc (by simpa using h)
  | havocC w x cs =>
    intro h; simp only [quietCmd, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    exact quiet_havocC (by simpa using h.1) fun g hg => indep_of_zeroOn (h.2 g hg)
  | seq a _ _ _ b iha ihb =>
    intro h; simp only [quietCmd, Bool.and_eq_true] at h
    exact ⟨iha h.1, ihb h.2⟩
  | ite w g _ _ a b iha ihb =>
    intro h; simp only [quietCmd, Bool.and_eq_true] at h
    exact quiet_ite (indep_of_zeroOn h.1.1) (iha h.1.2) (ihb h.2)
  | «while» w g _ _ _ _ _ _ _ _ b ih =>
    intro h; simp only [quietCmd, Bool.and_eq_true] at h
    have ig := indep_of_zeroOn h.1
    exact ⟨fun σ σ' ha => by simp only [ig σ σ' ha], ih h.2⟩
  | whileAnd w gs _ _ _ _ _ _ _ _ b ih =>
    intro h; simp only [quietCmd, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨fun σ σ' ha => all_indep (fun g hg => indep_of_zeroOn (h.1 g hg)) ha, ih h.2⟩
  | whileLog w gs _ _ _ _ _ _ _ b ih =>
    intro h; simp only [quietCmd, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨fun σ σ' ha => all_indep (fun g hg => indep_of_zeroOn (h.1 g hg)) ha, ih h.2⟩
  | whileGrow w gs _ _ _ _ _ _ _ b ih =>
    intro h; simp only [quietCmd, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨fun σ σ' ha => all_indep (fun g hg => indep_of_zeroOn (h.1 g hg)) ha, ih h.2⟩
  | whileUp w gs _ _ _ _ _ _ _ b ih =>
    intro h; simp only [quietCmd, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨fun σ σ' ha => all_indep (fun g hg => indep_of_zeroOn (h.1 g hg)) ha, ih h.2⟩
  | weaken _ _ _ _ _ c ih => intro h; exact ih h
  | dead _ c ih => intro h; exact ih h
  | call _ _ _ _ _ _ => intro h; simpa [quietCmd] using h

/-! ### `do` loops -/

/-- **The meaning of mini-C with jumps and `do` loops**: the rules of `JExec`, and for
    `do { body } while (cs)`: the body runs first; after a normal end or a `continue` the
    test is evaluated, and the loop goes on while it holds; a `break` ends the loop
    normally, a `return` ends it with `return`. -/
inductive JExecD (Φ : ℕ → Cmd ℕ Env) : JStmt → Env → Env → Outcome → ℕ → Prop where
  | stop {j σ} : JExecD Φ j σ σ .stop 0
  | basic {s σ τ n} (h : MExec Φ s σ τ n) : JExecD Φ (.basic s) σ τ .normal n
  | basicS {s σ n} (h : MPre Φ s σ n) : JExecD Φ (.basic s) σ σ .stop n
  | seqN {a b σ υ τ o n₁ n₂} (h₁ : JExecD Φ a σ υ .normal n₁) (h₂ : JExecD Φ b υ τ o n₂) :
      JExecD Φ (.seq a b) σ τ o (n₁ + n₂)
  | seqJ {a b σ τ o n} (h : JExecD Φ a σ τ o n) (ho : o ≠ .normal) :
      JExecD Φ (.seq a b) σ τ o n
  | iteT {w c a b σ σ₁ τ o n} (hc : CondStep c σ σ₁ true) (h : JExecD Φ a σ₁ τ o n) :
      JExecD Φ (.ite w c a b) σ τ o (w + n)
  | iteF {w c a b σ σ₁ τ o n} (hc : CondStep c σ σ₁ false) (h : JExecD Φ b σ₁ τ o n) :
      JExecD Φ (.ite w c a b) σ τ o (w + n)
  | loopF {w cs body inc fb fc σ} (ht : LoopTest cs σ false) :
      JExecD Φ (.loop w cs body inc fb fc) σ σ .normal w
  | loopN {w cs body inc fb fc σ υ υ' τ o o₁ n₁ n₂ n₃} (ht : LoopTest cs σ true)
      (h₁ : JExecD Φ body σ υ o₁ n₁) (ho : o₁ = .normal ∨ o₁ = .cont)
      (h₂ : MExec Φ (inc.getD .skip) υ υ' n₂)
      (h₃ : JExecD Φ (.loop w cs body inc fb fc) υ' τ o n₃) :
      JExecD Φ (.loop w cs body inc fb fc) σ τ o (w + n₁ + n₂ + n₃)
  | loopIS {w cs body inc fb fc σ υ o₁ n₁ n₂} (ht : LoopTest cs σ true)
      (h₁ : JExecD Φ body σ υ o₁ n₁) (ho : o₁ = .normal ∨ o₁ = .cont)
      (h₂ : MPre Φ (inc.getD .skip) υ n₂) :
      JExecD Φ (.loop w cs body inc fb fc) σ υ .stop (w + n₁ + n₂)
  | loopX {w cs body inc fb fc σ τ o n₁} (ht : LoopTest cs σ true)
      (h₁ : JExecD Φ body σ τ o n₁) (ho : o = .brk ∨ o = .ret ∨ o = .stop) :
      JExecD Φ (.loop w cs body inc fb fc) σ τ o.catchBrk (w + n₁)
  | brk {w σ} : JExecD Φ (.brk w) σ σ .brk w
  | cont {w σ} : JExecD Φ (.cont w) σ σ .cont w
  | ret {s σ τ n} (h : MExec Φ s σ τ n) : JExecD Φ (.ret s) σ τ .ret n
  | retS {s σ n} (h : MPre Φ s σ n) : JExecD Φ (.ret s) σ σ .stop n
  | switchS {w sc gs σ n} (h : MPre Φ (.cost w) σ n) : JExecD Φ (.switch w sc gs) σ σ .stop n
  | switch {w sc gs σ σ₁ τ o n i} (h₀ : MExec Φ (.cost w) σ σ₁ w) (hi : i ≤ gs.length)
      (h : JExecD Φ (.fall (gs.drop i)) σ₁ τ o n) :
      JExecD Φ (.switch w sc gs) σ τ o.catchBrk (w + n)
  | fallNil {σ} : JExecD Φ (.fall []) σ σ .normal 0
  | fallN {g gs σ υ τ o n₁ n₂} (h₁ : JExecD Φ g σ υ .normal n₁)
      (h₂ : JExecD Φ (.fall gs) υ τ o n₂) : JExecD Φ (.fall (g :: gs)) σ τ o (n₁ + n₂)
  | fallJ {g gs σ τ o n} (h : JExecD Φ g σ τ o n) (ho : o ≠ .normal) :
      JExecD Φ (.fall (g :: gs)) σ τ o n
  | doN {w cs body fb fc σ υ τ o o₁ n₁ n₂} (h₁ : JExecD Φ body σ υ o₁ n₁)
      (ho : o₁ = .normal ∨ o₁ = .cont) (ht : LoopTest cs υ true)
      (h₂ : JExecD Φ (.doLoop w cs body fb fc) υ τ o n₂) :
      JExecD Φ (.doLoop w cs body fb fc) σ τ o (n₁ + w + n₂)
  | doF {w cs body fb fc σ υ o₁ n₁} (h₁ : JExecD Φ body σ υ o₁ n₁)
      (ho : o₁ = .normal ∨ o₁ = .cont) (ht : LoopTest cs υ false) :
      JExecD Φ (.doLoop w cs body fb fc) σ υ .normal (n₁ + w)
  | doX {w cs body fb fc σ τ o n₁} (h₁ : JExecD Φ body σ τ o n₁)
      (ho : o = .brk ∨ o = .ret ∨ o = .stop) :
      JExecD Φ (.doLoop w cs body fb fc) σ τ o.catchBrk n₁

mutual
/-- `do { b } while (cs)` replaced by `b; while (cs) b`. -/
def JStmt.desugar : JStmt → JStmt
  | .basic s => .basic s
  | .seq a b => .seq a.desugar b.desugar
  | .ite w c a b => .ite w c a.desugar b.desugar
  | .loop w cs body inc fb fc => .loop w cs body.desugar inc fb fc
  | .brk w => .brk w
  | .cont w => .cont w
  | .ret s => .ret s
  | .switch w sc gs => .switch w sc (JStmt.desugarL gs)
  | .fall gs => .fall (JStmt.desugarL gs)
  | .doLoop w cs body fb fc => .seq body.desugar (.loop w cs body.desugar none fb fc)
def JStmt.desugarL : List JStmt → List JStmt
  | [] => []
  | g :: gs => g.desugar :: JStmt.desugarL gs
end

mutual
/-- The bodies of the `do` loops of `j` have no `break` or `continue` of their own. -/
def JStmt.okDo : JStmt → Bool
  | .basic _ => true
  | .seq a b => a.okDo && b.okDo
  | .ite _ _ a b => a.okDo && b.okDo
  | .loop _ _ body _ _ _ => body.okDo
  | .brk _ => true
  | .cont _ => true
  | .ret _ => true
  | .switch _ _ gs => JStmt.okDoL gs
  | .fall gs => JStmt.okDoL gs
  | .doLoop _ _ body _ _ => !body.escB && !body.escC && body.okDo
def JStmt.okDoL : List JStmt → Bool
  | [] => true
  | g :: gs => g.okDo && JStmt.okDoL gs
end

theorem desugarL_drop : ∀ (i : ℕ) (gs : List JStmt),
    JStmt.desugarL (gs.drop i) = (JStmt.desugarL gs).drop i := by
  intro i
  induction i with
  | zero => intro gs; rfl
  | succ i ih =>
    intro gs
    cases gs with
    | nil => rfl
    | cons g gs => simp only [List.drop_succ_cons, JStmt.desugarL]; exact ih gs

theorem desugarL_length : ∀ gs : List JStmt, (JStmt.desugarL gs).length = gs.length
  | [] => rfl
  | _ :: gs => by simp [JStmt.desugarL, desugarL_length gs]

theorem okDoL_drop : ∀ (i : ℕ) (gs : List JStmt), JStmt.okDoL gs = true →
    JStmt.okDoL (gs.drop i) = true := by
  intro i
  induction i with
  | zero => intro gs h; simpa using h
  | succ i ih =>
    intro gs h
    cases gs with
    | nil => rfl
    | cons g gs =>
      simp only [JStmt.okDoL, Bool.and_eq_true] at h
      simpa using ih gs h.2

mutual
theorem desugar_esc : ∀ j : JStmt, j.okDo = true →
    j.desugar.escB = j.escB ∧ j.desugar.escC = j.escC ∧ j.desugar.hasRet = j.hasRet
  | .basic _, _ => ⟨rfl, rfl, rfl⟩
  | .seq a b, h => by
    simp only [JStmt.okDo, Bool.and_eq_true] at h
    obtain ⟨a1, a2, a3⟩ := desugar_esc a h.1
    obtain ⟨b1, b2, b3⟩ := desugar_esc b h.2
    simp [JStmt.desugar, JStmt.escB, JStmt.escC, JStmt.hasRet, a1, a2, a3, b1, b2, b3]
  | .ite _ _ a b, h => by
    simp only [JStmt.okDo, Bool.and_eq_true] at h
    obtain ⟨a1, a2, a3⟩ := desugar_esc a h.1
    obtain ⟨b1, b2, b3⟩ := desugar_esc b h.2
    simp [JStmt.desugar, JStmt.escB, JStmt.escC, JStmt.hasRet, a1, a2, a3, b1, b2, b3]
  | .loop _ _ body _ _ _, h => by
    obtain ⟨_, _, a3⟩ := desugar_esc body (by simpa [JStmt.okDo] using h)
    simp [JStmt.desugar, JStmt.escB, JStmt.escC, JStmt.hasRet, a3]
  | .brk _, _ => ⟨rfl, rfl, rfl⟩
  | .cont _, _ => ⟨rfl, rfl, rfl⟩
  | .ret _, _ => ⟨rfl, rfl, rfl⟩
  | .switch _ _ gs, h => by
    obtain ⟨_, a2, a3⟩ := desugar_escL gs (by simpa [JStmt.okDo] using h)
    simp [JStmt.desugar, JStmt.escB, JStmt.escC, JStmt.hasRet, a2, a3]
  | .fall gs, h => by
    obtain ⟨a1, a2, a3⟩ := desugar_escL gs (by simpa [JStmt.okDo] using h)
    simp [JStmt.desugar, JStmt.escB, JStmt.escC, JStmt.hasRet, a1, a2, a3]
  | .doLoop _ _ body _ _, h => by
    simp only [JStmt.okDo, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨a1, a2, a3⟩ := desugar_esc body h.2
    simp [JStmt.desugar, JStmt.escB, JStmt.escC, JStmt.hasRet, a1, a2, a3, h.1.1, h.1.2]
theorem desugar_escL : ∀ gs : List JStmt, JStmt.okDoL gs = true →
    JStmt.escBL (JStmt.desugarL gs) = JStmt.escBL gs ∧
      JStmt.escCL (JStmt.desugarL gs) = JStmt.escCL gs ∧
      JStmt.hasRetL (JStmt.desugarL gs) = JStmt.hasRetL gs
  | [], _ => ⟨rfl, rfl, rfl⟩
  | g :: gs, h => by
    simp only [JStmt.okDoL, Bool.and_eq_true] at h
    obtain ⟨a1, a2, a3⟩ := desugar_esc g h.1
    obtain ⟨b1, b2, b3⟩ := desugar_escL gs h.2
    simp [JStmt.desugarL, JStmt.escBL, JStmt.escCL, JStmt.hasRetL, a1, a2, a3, b1, b2, b3]
end

theorem no_brk_cont {j : JStmt} {σ τ : Env} {o : Outcome} {n : ℕ} (h : JExec Φ j σ τ o n)
    (hb : j.escB = false) (hc : j.escC = false) : o ≠ .brk ∧ o ≠ .cont := by
  have := outcome_esc h
  exact ⟨fun e => by simpa [hb] using this.1 e, fun e => by simpa [hc] using this.2.1 e⟩

/-- After the body and a test that holds, the rest of a desugared `do` loop is the loop. -/
theorem loop_step {w : ℕ} {cs : List MCond} {b : JStmt} {fb fc : Option ℕ} {υ τ : Env}
    {o : Outcome} {n : ℕ} (hb : b.escB = false) (hc : b.escC = false) (ht : LoopTest cs υ true)
    (h : JExec Φ (.seq b (.loop w cs b none fb fc)) υ τ o n) :
    JExec Φ (.loop w cs b none fb fc) υ τ o (w + n) := by
  cases h with
  | stop =>
    have := JExec.loopX (Φ := Φ) (w := w) (inc := none) (fb := fb) (fc := fc) ht
      (JExec.stop (j := b) (σ := υ)) (Or.inr (Or.inr rfl))
    simpa [Outcome.catchBrk] using this
  | seqN e1 e2 =>
    have := JExec.loopN (inc := none) ht e1 (Or.inl rfl) ⟨.skip, rfl, Exec.skip _⟩ e2
    simpa [Nat.add_assoc] using this
  | seqJ e ho =>
    obtain ⟨nb, nc⟩ := no_brk_cont e hb hc
    have ho' : o = .brk ∨ o = .ret ∨ o = .stop := by
      cases o <;> simp_all
    have := JExec.loopX (inc := none) (fb := fb) (fc := fc) (w := w) ht e ho'
    have hc' : o.catchBrk = o := by cases o <;> simp_all [Outcome.catchBrk]
    rwa [hc'] at this

/-- A run of `j` is a run of `j` with its `do` loops desugared. -/
theorem desugar_exec {j : JStmt} {σ τ : Env} {o : Outcome} {n : ℕ} (h : JExecD Φ j σ τ o n) :
    j.okDo = true → JExec Φ j.desugar σ τ o n := by
  induction h with
  | stop => intro _; exact JExec.stop
  | basic hm => intro _; exact JExec.basic hm
  | basicS hm => intro _; exact JExec.basicS hm
  | seqN _ _ ih₁ ih₂ =>
    intro hk; simp only [JStmt.okDo, Bool.and_eq_true] at hk
    exact JExec.seqN (ih₁ hk.1) (ih₂ hk.2)
  | seqJ _ ho ih =>
    intro hk; simp only [JStmt.okDo, Bool.and_eq_true] at hk
    exact JExec.seqJ (ih hk.1) ho
  | iteT hc _ ih =>
    intro hk; simp only [JStmt.okDo, Bool.and_eq_true] at hk
    exact JExec.iteT hc (ih hk.1)
  | iteF hc _ ih =>
    intro hk; simp only [JStmt.okDo, Bool.and_eq_true] at hk
    exact JExec.iteF hc (ih hk.2)
  | loopF ht => intro _; exact JExec.loopF ht
  | loopN ht _ ho h₂ _ ih₁ ih₃ =>
    intro hk
    exact JExec.loopN ht (ih₁ (by simpa [JStmt.okDo] using hk)) ho h₂ (ih₃ hk)
  | loopIS ht _ ho h₂ ih₁ =>
    intro hk
    exact JExec.loopIS ht (ih₁ (by simpa [JStmt.okDo] using hk)) ho h₂
  | loopX ht _ ho ih₁ =>
    intro hk
    exact JExec.loopX ht (ih₁ (by simpa [JStmt.okDo] using hk)) ho
  | brk => intro _; exact JExec.brk
  | cont => intro _; exact JExec.cont
  | ret hm => intro _; exact JExec.ret hm
  | retS hm => intro _; exact JExec.retS hm
  | switchS hm => intro _; exact JExec.switchS hm
  | @switch w sc gs σ σ₁ τ o n i h₀ hi _ ih =>
    intro hk
    have := ih (by simpa [JStmt.okDo] using okDoL_drop i gs (by simpa [JStmt.okDo] using hk))
    simp only [JStmt.desugar] at this ⊢
    rw [desugarL_drop] at this
    exact JExec.switch h₀ (by rw [desugarL_length]; exact hi) this
  | fallNil => intro _; exact JExec.fallNil
  | fallN _ _ ih₁ ih₂ =>
    intro hk; simp only [JStmt.okDo, JStmt.okDoL, Bool.and_eq_true] at hk
    exact JExec.fallN (ih₁ hk.1) (ih₂ (by simpa [JStmt.okDo] using hk.2))
  | fallJ _ ho ih =>
    intro hk; simp only [JStmt.okDo, JStmt.okDoL, Bool.and_eq_true] at hk
    exact JExec.fallJ (ih hk.1) ho
  | @doN w cs body fb fc σ υ τ o o₁ n₁ n₂ _ ho ht _ ihb ih₂ =>
    intro hk
    have hk' := hk
    simp only [JStmt.okDo, Bool.and_eq_true, Bool.not_eq_true'] at hk'
    obtain ⟨⟨hB, hC⟩, hkb⟩ := hk'
    obtain ⟨dB, dC, _⟩ := desugar_esc body hkb
    have hb' := ihb hkb
    have h2 := ih₂ hk
    simp only [JStmt.desugar] at h2 ⊢
    have ho₁ : o₁ = .normal := by
      rcases ho with rfl | rfl
      · rfl
      · exact absurd rfl (no_brk_cont hb' (dB.trans hB) (dC.trans hC)).2
    subst ho₁
    have := JExec.seqN hb' (loop_step (dB.trans hB) (dC.trans hC) ht h2)
    simpa [Nat.add_assoc] using this
  | @doF w cs body fb fc σ υ o₁ n₁ _ ho ht ihb =>
    intro hk
    have hk' := hk
    simp only [JStmt.okDo, Bool.and_eq_true, Bool.not_eq_true'] at hk'
    obtain ⟨⟨hB, hC⟩, hkb⟩ := hk'
    obtain ⟨dB, dC, _⟩ := desugar_esc body hkb
    have hb' := ihb hkb
    have ho₁ : o₁ = .normal := by
      rcases ho with rfl | rfl
      · rfl
      · exact absurd rfl (no_brk_cont hb' (dB.trans hB) (dC.trans hC)).2
    subst ho₁
    simp only [JStmt.desugar]
    exact JExec.seqN hb' (JExec.loopF ht)
  | @doX w cs body fb fc σ τ o n₁ _ ho ihb =>
    intro hk
    have hk' := hk
    simp only [JStmt.okDo, Bool.and_eq_true, Bool.not_eq_true'] at hk'
    obtain ⟨⟨hB, hC⟩, hkb⟩ := hk'
    obtain ⟨dB, dC, _⟩ := desugar_esc body hkb
    have hb' := ihb hkb
    obtain ⟨nb, _⟩ := no_brk_cont hb' (dB.trans hB) (dC.trans hC)
    have hc' : o.catchBrk = o := by cases o <;> simp_all [Outcome.catchBrk]
    rw [hc']
    simp only [JStmt.desugar]
    exact JExec.seqJ hb' (by rcases ho with rfl | rfl | rfl <;> simp_all)

mutual
/-- The checker's translation of a `do` loop is that of its desugared form. -/
theorem tr_desugar (r n : ℕ) (G : List ℕ) : ∀ (j : JStmt) (ctx : List Frame) (k : MStmt),
    j.okDo = true → tr r n G ctx j.desugar k = tr r n G ctx j k
  | .basic _, _, _, _ => rfl
  | .seq a b, ctx, k, h => by
    simp only [JStmt.okDo, Bool.and_eq_true] at h
    have iha := fun ctx k => tr_desugar r n G a ctx k h.1
    have ihb := fun ctx k => tr_desugar r n G b ctx k h.2
    simp only [JStmt.desugar, tr, iha, ihb]
  | .ite w c a b, ctx, k, h => by
    simp only [JStmt.okDo, Bool.and_eq_true] at h
    have iha := fun ctx k => tr_desugar r n G a ctx k h.1
    have ihb := fun ctx k => tr_desugar r n G b ctx k h.2
    obtain ⟨a1, a2, a3⟩ := desugar_esc a h.1
    obtain ⟨b1, b2, b3⟩ := desugar_esc b h.2
    simp only [JStmt.desugar, tr, iha, ihb, JStmt.ends, JStmt.hasRet, JStmt.escB, JStmt.escC,
      a1, a2, a3, b1, b2, b3]
  | .loop w cs body inc fb fc, ctx, k, h => by
    have hb : body.okDo = true := by simpa [JStmt.okDo] using h
    have ih := fun ctx k => tr_desugar r n G body ctx k hb
    obtain ⟨a1, a2, a3⟩ := desugar_esc body hb
    simp only [JStmt.desugar, tr, ih, a1, a2, a3]
  | .brk _, _, _, _ => rfl
  | .cont _, _, _, _ => rfl
  | .ret _, _, _, _ => rfl
  | .switch w sc gs, ctx, k, h => by
    have hg : JStmt.okDoL gs = true := by simpa [JStmt.okDo] using h
    have ih := fun ctx => trL_desugar r n G gs ctx hg
    obtain ⟨_, a2, a3⟩ := desugar_escL gs hg
    simp only [JStmt.desugar, tr, ih, a2, a3]
  | .fall _, _, _, _ => rfl
  | .doLoop w cs body fb fc, ctx, k, h => by
    have h' := h
    simp only [JStmt.okDo, Bool.and_eq_true, Bool.not_eq_true'] at h'
    obtain ⟨⟨hB, hC⟩, hb⟩ := h'
    have ih := fun ctx k => tr_desugar r n G body ctx k hb
    obtain ⟨a1, a2, a3⟩ := desugar_esc body hb
    simp only [JStmt.desugar, tr, ih, a1, a2, a3, hB, hC]
    simp [freshGh, nodup, disjoint, Option.bind_assoc]
    split_ifs <;> try rfl
    all_goals (cases tr r n G _ body MStmt.skip <;> rfl)
theorem trL_desugar (r n : ℕ) (G : List ℕ) : ∀ (gs : List JStmt) (ctx : List Frame),
    JStmt.okDoL gs = true → trL r n G ctx (JStmt.desugarL gs) = trL r n G ctx gs
  | [], _, _ => rfl
  | g :: gs, ctx, h => by
    simp only [JStmt.okDoL, Bool.and_eq_true] at h
    have ih1 := fun ctx k => tr_desugar r n G g ctx k h.1
    have ih2 := fun ctx => trL_desugar r n G gs ctx h.2
    simp only [JStmt.desugarL, trL, ih1, ih2]
end

mutual
/-- A statement that the checker translates has `do` loops without jumps of their own. -/
theorem tr_okDo (r n : ℕ) (G : List ℕ) : ∀ (j : JStmt) (ctx : List Frame) (k m : MStmt),
    tr r n G ctx j k = some m → j.okDo = true
  | .basic _, _, _, _, _ => rfl
  | .seq a b, ctx, k, m, h => by
    simp only [tr, Option.bind_eq_bind, Option.bind_eq_some] at h
    obtain ⟨kb, hb, ha⟩ := h
    simp [JStmt.okDo, tr_okDo r n G a _ _ _ ha, tr_okDo r n G b _ _ _ hb]
  | .ite w c a b, ctx, k, m, h => by
    simp only [tr] at h
    split_ifs at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
      obtain ⟨ta, ha, tb, hb, _⟩ := h
      simp [JStmt.okDo, tr_okDo r n G a _ _ _ ha, tr_okDo r n G b _ _ _ hb]
    · simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
      obtain ⟨ta, ha, tb, hb, _⟩ := h
      simp [JStmt.okDo, tr_okDo r n G a _ _ _ ha, tr_okDo r n G b _ _ _ hb]
  | .loop w cs body inc fb fc, ctx, k, m, h => by
    obtain ⟨_, _, _, _, _, bd, hbd, _⟩ := tr_loop_inv h
    simp [JStmt.okDo, tr_okDo r n G body _ _ _ hbd]
  | .brk _, _, _, _, _ => rfl
  | .cont _, _, _, _, _ => rfl
  | .ret _, _, _, _, _ => rfl
  | .switch w sc gs, ctx, k, m, h => by
    obtain ⟨_, _, groups, hg, _⟩ := tr_switch_inv h
    simp [JStmt.okDo, trL_okDo r n G gs _ _ hg]
  | .fall _, _, _, _, h => by simp [tr] at h
  | .doLoop w cs body fb fc, ctx, k, m, h => by
    simp only [tr] at h
    split_ifs at h with h1
    all_goals
      simp only [Option.bind_eq_bind, Option.bind_eq_some] at h
      obtain ⟨bd, hbd, hm⟩ := h
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h1
      simp [JStmt.okDo, h1.1, h1.2, tr_okDo r n G body _ _ _ hm]
theorem trL_okDo (r n : ℕ) (G : List ℕ) : ∀ (gs : List JStmt) (ctx : List Frame)
    (groups : List MStmt), trL r n G ctx gs = some groups → JStmt.okDoL gs = true
  | [], _, _, _ => rfl
  | g :: gs, ctx, groups, h => by
    simp only [trL, Option.bind_eq_bind, Option.bind_eq_some] at h
    obtain ⟨g', hg, gs', hgs, _⟩ := h
    simp [JStmt.okDoL, tr_okDo r n G g _ _ _ hg, trL_okDo r n G gs _ _ hgs]
end

mutual
theorem desugar_ghosts : ∀ (j : JStmt) (x : ℕ), x ∈ j.desugar.ghosts → x ∈ j.ghosts
  | .basic _, _, h => h
  | .seq a b, x, h => by
    simp only [JStmt.desugar, JStmt.ghosts, List.mem_append] at h ⊢
    exact h.imp (desugar_ghosts a x) (desugar_ghosts b x)
  | .ite _ _ a b, x, h => by
    simp only [JStmt.desugar, JStmt.ghosts, List.mem_append] at h ⊢
    exact h.imp (desugar_ghosts a x) (desugar_ghosts b x)
  | .loop _ _ body _ _ _, x, h => by
    simp only [JStmt.desugar, JStmt.ghosts, List.mem_append] at h ⊢
    exact h.imp_right (desugar_ghosts body x)
  | .brk _, _, h => h
  | .cont _, _, h => h
  | .ret _, _, h => h
  | .switch _ _ gs, x, h => by
    simp only [JStmt.desugar, JStmt.ghosts, List.mem_cons] at h ⊢
    exact h.imp_right (desugar_ghostsL gs x)
  | .fall gs, x, h => by
    simp only [JStmt.desugar, JStmt.ghosts] at h ⊢
    exact desugar_ghostsL gs x h
  | .doLoop _ _ body _ _, x, h => by
    simp only [JStmt.desugar, JStmt.ghosts, List.mem_append] at h ⊢
    rcases h with h | (h | h)
    · exact Or.inr (desugar_ghosts body x h)
    · exact Or.inl h
    · exact Or.inr (desugar_ghosts body x h)
theorem desugar_ghostsL : ∀ (gs : List JStmt) (x : ℕ),
    x ∈ JStmt.ghostsL (JStmt.desugarL gs) → x ∈ JStmt.ghostsL gs
  | [], _, h => h
  | g :: gs, x, h => by
    simp only [JStmt.desugarL, JStmt.ghostsL, List.mem_append] at h ⊢
    exact h.imp (desugar_ghosts g x) (desugar_ghostsL gs x)
end

/-! ### Validated certificates of functions with early exits and `switch` -/

/-- **Validated certificates, with jumps.** If the program certificate `fs` is accepted,
    the bodies of its functions are the procedures of `Φ` and its contracts hold, the body
    `b` of function `i` is validated against the statement `j` of mini-C with jumps
    (`validateJ`: once its jumps are eliminated, `j` lowers to `b`), and no procedure reads
    or writes the ghost variables of `j` among those that `j` can call, the functions
    numbered below `i` (for the functions of the file this follows from `quietCmd`,
    `quiet_of_quietB`; for contracts it is an assumption), then, from every
    state satisfying the precondition, **every execution prefix of `j` in its direct
    semantics (`JExecD`, with `do` loops) costs at most the function's bound**, and every
    run that ends (normally or by `return`) ends in a state that satisfies the
    postcondition up to the ghost variables and the cost variable. -/
theorem validatedJ_sound (fs : List FunCert) (h : checkProgram fs = true)
    (hbody : ∀ i F b, fs[i]? = some F → F.body = some b → Φ i = b.toCmd)
    (hcontract : ∀ i F, fs[i]? = some F → F.body = none → FunSpec Φ i F)
    {i : ℕ} {F : FunCert} {b : ACmd} (hF : fs[i]? = some F) (hb : F.body = some b)
    {r : ℕ} {j : JStmt} (hv : validateJ i b r j = true)
    (hΦ : ∀ p, p < i → Quiet i (costVar :: ghostSet r j) (ghostSet r j) (Φ p)) :
    ∀ ρ σ, holds F.pre ρ σ →
      (∀ τ n, JExecD Φ j σ τ .stop n → n ≤ F.bound.eval ρ) ∧
      (∀ τ o n, JExecD Φ j σ τ o n → o ≠ .stop →
        ∃ τ', Agree (costVar :: ghostSet r j) τ τ' ∧ holds F.post ρ τ') := by
  simp only [validateJ, Bool.and_eq_true, Bool.not_eq_true'] at hv
  obtain ⟨⟨h0, h1⟩, hv⟩ := hv
  split at hv
  · next s hs =>
    obtain ⟨d, hd, hsound⟩ := validated_sound fs h hbody hcontract hF hb hv
    have h0' : choiceVar ∉ ghostSet r j := by simpa using h0
    have h1' : costVar ∉ ghostSet r j := by simpa using h1
    have hr : r ∈ ghostSet r j := List.mem_cons_self _ _
    have hgj : ∀ x ∈ j.desugar.ghosts, x ∈ ghostSet r j := fun x hx =>
      List.mem_cons_of_mem _ (desugar_ghosts j x hx)
    have hok := tr_okDo r i (ghostSet r j) j [] .skip s hs
    have hs' : tr r i (ghostSet r j) [] j.desugar .skip = some s := by
      rw [tr_desugar r i (ghostSet r j) j [] .skip hok]; exact hs
    have hw : WF (ghostSet r j) [] := fun _ h => by simp at h
    intro ρ σ hpre
    obtain ⟨hbound, hpost⟩ := hsound ρ σ hpre
    have main : ∀ τ o n, JExecD Φ j σ τ o n →
        Res Φ (costVar :: ghostSet r j) r [] .skip d σ τ o n := fun τ o n hx =>
      (sim hΦ hr h0' h1' (desugar_exec hx hok)).1 [] .skip s d hw hgj hs' hd σ (Agree.refl _ _)
        (by simp [FlagsOK, okFlags])
    refine ⟨fun τ n hx => ?_, fun τ o n hx ho => ?_⟩
    · obtain ⟨n', hn, hp⟩ := main τ .stop n hx
      exact hn.trans (hbound n' hp)
    · have hres := main τ o n hx
      cases o with
      | stop => exact absurd rfl ho
      | normal =>
        obtain ⟨τ', n', _, ha, _, cs, hcs, hrun, _⟩ := hres
        simp [lower] at hcs; subst hcs
        exact ⟨τ', ha, hpost τ' _ (hrun τ' 0 (Exec.skip _))⟩
      | brk => obtain ⟨τ', n', _, ha, _, e⟩ := hres; exact ⟨τ', ha, hpost τ' n' e⟩
      | cont => obtain ⟨τ', n', _, ha, _, e⟩ := hres; exact ⟨τ', ha, hpost τ' n' e⟩
      | ret => obtain ⟨τ', n', _, ha, _, e⟩ := hres; exact ⟨τ', ha, hpost τ' n' e⟩
  · cases hv

/-! ### Examples -/

/-- `while (i < n) { if (n <= i + 5) break; i = i + 1; }` with `i = x₂`, `n = x₃`, the
    `break` flag `x₄`, unit weights. -/
def breakSrc : JStmt :=
  .loop 1 [.cmp .lt (.var 2) (.var 3)]
    (.seq (.ite 1 (.cmp .le (.var 3) (.add (.var 2) (.lit 5))) (.brk 1) (.basic .skip))
      (.basic (.assign 1 2 (.add (.var 2) (.lit 1)))))
    none (some 4) none

/-- Its elimination: the flag cleared, tested by the loop and set by the `break`; the
    statement after the conditional moved into its other branch. -/
theorem breakSrc_elim : elim 5 0 breakSrc = some
    (.seq (seqs [flagSet 0 4 0])
      (.seq (.while 1 [.cmp .lt (.var 2) (.var 3), clearTest 4]
          (.seq .skip (.seq (.ite 1 (.cmp .le (.var 3) (.add (.var 2) (.lit 5))) (flagSet 1 4 1)
            (.seq .skip (.seq (.assign 1 2 (.add (.var 2) (.lit 1))) .skip))) .skip)))
        .skip)) := by rfl

/-- A flag that is a variable of the source is refused. -/
theorem breakSrc_flag_clash : elim 5 0 (.loop 1 [.cmp .lt (.var 2) (.var 3)]
    (.seq (.brk 1) (.basic (.assign 1 4 (.lit 0)))) none (some 4) none) = none := by rfl

end ImperativeOptimization.MiniC
