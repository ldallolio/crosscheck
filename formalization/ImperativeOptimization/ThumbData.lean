/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import ImperativeOptimization.Thumb
import ImperativeOptimization.ThumbDataCore
import ImperativeOptimization.Checker

/-!
# Loop bounds of Cortex-M0 machine code: soundness

The data semantics of machine code. A state holds the low registers `r0`-`r7` (words,
below `2^32`) and the flags N, Z, C, V. A step of a run executes the instruction at the
program counter: it goes to the successor allowed by `decode`/`trans` (for a conditional
branch, the taken one if and only if the condition holds on the flags, `condHolds`), with
the effect `effect` on the registers and flags (`EffOk`): sums and differences modulo
`2^32`, the flags of an addition (`flagsAdd`) or a subtraction (`flagsSub`) as ARM's
AddWithCarry computes them, any value where the effect says so. Memory is not modelled: a
load gives any value. A call is one step, whose effect is that of `BL` in `effect`.

`data_sound`: if `checkBinary` and `checkData` accept, every run in this semantics costs at
most the certified bound; only the rows the certificate leaves as trusted are assumed. The
proof shows that the invariants hold at every step and that the potentials telescope, so
that the rows of the certified loops hold (`chain_rows`), and that a run of the data
semantics is a run of `Thumb.MRun` (`drun_mrun`).

Trusted, as the specification of the processor: `decode` and `effect`, the flags and the
conditions, the semantics above (no interrupts; a callee changes only the registers that
`effect` lets a call change); and that the code is that of the binary.
-/

namespace ImperativeOptimization.Thumb

open ImperativeOptimization.Cycles
open ImperativeOptimization.Checker (Lin PExp Env entails1 entails1_sound holds holds_cons vadd vsmul unit
  dot_vadd dot_vsmul dot_unit)

/-! ### The data semantics -/

def flagsOfE (r : Nat → Nat) : FEff → Flags → Flags → Prop
  | .keep, f, f' => f' = f
  | .any, _, _ => True
  | .add a b, _, f' => f' = flagsAdd (srcVal r a) (srcVal r b)
  | .sub a b, _, f' => f' = flagsSub (srcVal r a) (srcVal r b)

def wfState (σ : MState) : Prop := ∀ i < 8, σ.r i < U

/-- The effect of an instruction between the state before and the state after it: a
    register gets the value of its first write in `dst` (any value for `any`), the others
    keep theirs. -/
def EffOk (e : Eff) (σ σ' : MState) : Prop :=
  wfState σ' ∧
  (∀ i < 8, e.dst.find? (fun p => p.1 == i) = none → σ'.r i = σ.r i) ∧
  (∀ i < 8, ∀ p, e.dst.find? (fun p => p.1 == i) = some p → ∀ v, valOf σ.r p.2 = some v → σ'.r i = v) ∧
  flagsOfE σ.r e.fl σ.f σ'.f

/-- The instruction at `a`, in state `σ`, allows its `j`-th transition (to `next`, with `w`
    cycles, calling `calls`). -/
def DOk (mul : Nat) (c : Code) (a j : Nat) (σ : MState) (next : Option Nat) (w : Nat)
    (calls : List Nat) : Prop :=
  wfState σ ∧ ∃ i, decode mul c a = some i ∧ (trans i a)[j]? = some (next, w, calls) ∧
    (∀ t, i.kind = .cond t → condHolds (ccOf c a) σ.f = (j == 0))

/-- A step of a data run: the step of the machine run, the transition taken, the state
    before it. -/
structure DStep where
  st : MStep
  j : Nat
  σ : MState

/-- The steps follow each other from the given address until a return, each state being
    the effect of the previous instruction on the previous state. -/
def DChain (abi : Bool) (c : Code) : Option Nat → List DStep → Prop
  | none, [] => True
  | some a, x :: t => x.st.a = a ∧ (∀ y ∈ t.head?, EffOk (effect abi c a) x.σ y.σ) ∧
      DChain abi c x.st.next t
  | _, _ => False

/-- The function at entry `e` and its certificate. -/
def dfAt (fs : List BFun) (Ls : List DFun) (e : Nat) : Option (BFun × DFun) :=
  (find (fs.map (·.entry)) e).bind fun k =>
    match fs[k]?, Ls[k]? with
    | some f, some L => some (f, L)
    | _, _ => none

/-- Runs of the data semantics of the function at entry `e`, of cost `total`, with calls
    nested less than `d` deep. Only the rows left as trusted by the certificate are
    assumed. -/
def DRun (mul : Nat) (abi : Bool) (c : Code) (fs : List BFun) (Ls : List DFun) :
    Nat → Nat → Int → Prop
  | 0, _, _ => False
  | d + 1, e, total => ∃ f L s, dfAt fs Ls e = some (f, L) ∧ DChain abi c (some e) s ∧
      (∀ x ∈ s, DOk mul c x.st.a x.j x.σ x.st.next x.st.w x.st.calls ∧
        CallsWith (DRun mul abi c fs Ls d) x.st.calls x.st.x) ∧
      (∀ r ∈ L.trusted, (s.map fun x => coefPair r.coef x.st.a x.st.next).sum ≤ r.rhs) ∧
      total = (s.map fun x => (x.st.w : Int) + x.st.x).sum

/-! ### Evaluation of the constraints -/

theorem mk_eval (terms : List (Int × Nat)) (c : Int) (ρ s : Env) :
    (mk terms c).eval ρ s = (terms.map fun t => t.1 * s t.2).sum + c := by
  simp only [mk, Lin.eval, Checker.dot]
  induction terms with
  | nil => simp [Checker.dot]
  | cons t ts ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, dot_vadd, dot_vsmul, dot_unit]
    linarith

theorem dle_eval (c : Int) (ρ s : Env) : (dle c).eval ρ s = s 8 - s 9 + c := by
  simp [dle, mk_eval]; ring
theorem dge_eval (c : Int) (ρ s : Env) : (dge c).eval ρ s = s 9 - s 8 + c := by
  simp [dge, mk_eval]; ring
theorem lo_eval (v : Nat) (ρ s : Env) : (lo v).eval ρ s = s v + 1 - 2147483648 := by
  simp [lo, mk_eval]; ring
theorem hi_eval (v : Nat) (ρ s : Env) : (hi v).eval ρ s = 2147483648 - s v := by
  simp [hi, mk_eval]; ring
theorem sumC_eval (k c : Int) (ρ s : Env) : (sumC k c).eval ρ s = k * (s 8 + s 9) + c := by
  simp [sumC, mk_eval]; ring

/-! ### The facts of the conditions -/

theorem beq_decide (p q : Prop) [Decidable p] [Decidable q] :
    (decide p == decide q) = decide (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem sub_z (a b : Nat) (ha : a < U) (hb : b < U) : (flagsSub a b).z = decide (a = b) := by
  simp only [flagsSub, U] at *
  rw [decide_eq_decide]; omega

theorem sub_c (a b : Nat) : (flagsSub a b).c = decide (b ≤ a) := by
  simp only [flagsSub]

theorem sub_nv (a b : Nat) (ha : a < U) (hb : b < U) :
    ((flagsSub a b).n == (flagsSub a b).v) = decide (sgn b ≤ sgn a) := by
  simp only [flagsSub, sgn, U] at *
  rw [beq_decide, decide_eq_decide]
  split_ifs <;> omega

theorem add_z (a b : Nat) (ha : a < U) (hb : b < U) :
    (flagsAdd a b).z = decide (a + b = 0 ∨ a + b = U) := by
  simp only [flagsAdd, U] at *
  rw [decide_eq_decide]; omega

theorem add_c (a b : Nat) : (flagsAdd a b).c = decide (U ≤ a + b) := by
  simp only [flagsAdd]

theorem bne_not (x y : Bool) : (x != y) = !(x == y) := rfl

theorem cond_xor (cc : Nat) (hcc : cc < 14) (f : Flags) :
    condHolds (cc ^^^ 1) f = !condHolds cc f := by
  rcases f with ⟨n, z, c, v⟩
  interval_cases cc <;> cases n <;> cases z <;> cases c <;> cases v <;> decide

theorem subFacts_true (a b : Nat) (ha : a < U) (hb : b < U) (c' : Nat) (hc : c' < 16)
    (h : condHolds c' (flagsSub a b) = true) (ρ s : Env) (h8 : s 8 = a) (h9 : s 9 = b) :
    ∃ D ∈ subFacts c', holds D ρ s := by
  have hz := sub_z a b ha hb
  have hcy := sub_c a b
  have hnv := sub_nv a b ha hb
  simp only [U] at ha hb
  interval_cases c' <;> simp only [condHolds, bne_not, hz, hcy, hnv] at h <;>
    simp [subFacts, holds, dle_eval, dge_eval, lo_eval, hi_eval, h8, h9, sgn] at h ⊢ <;>
    (try split_ifs at h) <;> omega

theorem addFacts_true (a b : Nat) (ha : a < U) (hb : b < U) (c' : Nat) (hc : c' < 16)
    (h : condHolds c' (flagsAdd a b) = true) (ρ s : Env) (h8 : s 8 = a) (h9 : s 9 = b) :
    ∃ D ∈ addFacts c', holds D ρ s := by
  have hz := add_z a b ha hb
  have hcy := add_c a b
  simp only [U] at ha hb hz hcy
  interval_cases c' <;> simp only [condHolds, bne_not, hz, hcy] at h <;>
    simp [addFacts, holds, sumC_eval, h8, h9, U] at h ⊢ <;> omega

/-- The facts of a branch hold on the operands that set the flags. -/
theorem condFacts_sound (k : FKind) (a b : Nat) (ha : a < U) (hb : b < U) (f : Flags)
    (hf : match k with | .none => True | .add => f = flagsAdd a b | .sub => f = flagsSub a b)
    (cc : Nat) (hcc : cc < 16) (taken : Bool) (h : condHolds cc f = taken) (ρ s : Env)
    (h8 : s 8 = a) (h9 : s 9 = b) :
    ∃ D ∈ condFacts k cc taken, holds D ρ s := by
  have key : ∀ c', c' < 16 → condHolds c' f = true → ∃ D ∈ condFacts k c' true, holds D ρ s := by
    intro c' hc' h'
    cases k with
    | none => exact ⟨[], by simp [condFacts], by simp [holds]⟩
    | add => simp only at hf; subst hf; simpa [condFacts] using addFacts_true a b ha hb c' hc' h' ρ s h8 h9
    | sub => simp only at hf; subst hf; simpa [condFacts] using subFacts_true a b ha hb c' hc' h' ρ s h8 h9
  have hc1 : ∀ c', condFacts k (c' ^^^ 1) true = condFacts k c' false := by
    intro c'; simp [condFacts]
  cases taken with
  | true => exact key cc hcc h
  | false =>
    by_cases h14 : cc < 14
    · rw [← hc1]
      apply key (cc ^^^ 1)
      · interval_cases cc <;> decide
      · rw [cond_xor cc h14, h]; rfl
    · interval_cases cc <;> simp [condHolds] at h

/-! ### Affine expressions -/

theorem padd_eval (a b : PExp) (s : Env) : (padd a b).eval s = a.eval s + b.eval s := by
  simp only [padd, PExp.eval, dot_vadd]; ring

theorem psmul_eval (k : Int) (a : PExp) (s : Env) : (psmul k a).eval s = k * a.eval s := by
  simp only [psmul, PExp.eval, dot_vsmul]; ring

theorem pv_eval (i : Nat) (s : Env) : (pv i).eval s = s i := by
  simp [pv, PExp.eval, dot_unit]

theorem pconst_eval (k : Int) (s : Env) : (pconst k).eval s = k := by
  simp [pconst, PExp.eval, Checker.dot]

theorem substSv_eval : ∀ (l : List Int) (σ : Nat → PExp) (s : Env),
    (substSv l σ).eval s = Checker.dot l (fun v => (σ v).eval s)
  | [], σ, s => by simp [substSv, pconst_eval, Checker.dot]
  | a :: l, σ, s => by
    simp only [substSv, padd_eval, psmul_eval, Checker.dot]
    rw [substSv_eval l]

theorem substL_eval (g : Lin) (σ : Nat → PExp) (ρ s : Env) :
    (substL g σ).eval ρ s = g.eval ρ (fun v => (σ v).eval s) := by
  have := substSv_eval g.sv σ s
  show Checker.dot (substSv g.sv σ).sv s + Checker.dot g.lv ρ + (g.c + (substSv g.sv σ).c) = _
  simp only [Lin.eval, PExp.eval] at this ⊢
  linarith

theorem substP_eval (g : PExp) (σ : Nat → PExp) (s : Env) :
    (substP g σ).eval s = g.eval (fun v => (σ v).eval s) := by
  have := substSv_eval g.sv σ s
  show Checker.dot (substSv g.sv σ).sv s + (g.c + (substSv g.sv σ).c) = _
  simp only [PExp.eval] at this ⊢
  linarith

theorem goalLin_eval (k : Int) (p q : PExp) (ρ s : Env) :
    (goalLin k p q).eval ρ s = k + p.eval s - q.eval s := by
  simp only [goalLin, Lin.eval, PExp.eval, dot_vadd, dot_vsmul, Checker.dot]; ring

theorem dot_congr : ∀ (l : List Int) (f g : Env) (n : Nat), l.length ≤ n →
    (∀ v < n, f v = g v) → Checker.dot l f = Checker.dot l g
  | [], _, _, _, _, _ => rfl
  | a :: l, f, g, n, hl, h => by
    simp only [Checker.dot]
    have h0 : f 0 = g 0 := h 0 (by simp at hl; omega)
    rw [h0, dot_congr l (fun i => f (i + 1)) (fun i => g (i + 1)) (n - 1) (by simp at hl; omega)
      (fun v hv => h (v + 1) (by omega))]

/-! ### Environments -/

/-- The variables of a state: registers `0`-`7`, the ghosts `8`, `9`. -/
def envOf (σ : MState) (fa fb : Nat) : Env := fun v =>
  if v < 8 then (σ.r v : Int) else if v = 8 then (fa : Int) else if v = 9 then (fb : Int) else 0

/-- The variables of a transition: those of the state before, then the registers after
    (`10`-`17`); the fresh ghosts `18`, `19` are `0`. -/
def envT (σ σ' : MState) (fa fb : Nat) : Env := fun v =>
  if v < 10 then envOf σ fa fb v else if v < 18 then (σ'.r (v - 10) : Int) else 0

theorem envT_below (σ σ' : MState) (fa fb v : Nat) (hv : v < 10) :
    envT σ σ' fa fb v = envOf σ fa fb v := by simp [envT, hv]

theorem rangesL_holds (σ σ' : MState) (fa fb : Nat) (hσ : wfState σ) (hσ' : wfState σ')
    (ha : fa < U) (hb : fb < U) (ρ : Env) : holds rangesL ρ (envT σ σ' fa fb) := by
  intro e he
  simp only [rangesL, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at he
  obtain ⟨v, hv, rfl | rfl⟩ := he
  all_goals
    simp only [mk_eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have h1 : 0 ≤ envT σ σ' fa fb v ∧ envT σ σ' fa fb v < (U : Int) := by
      simp only [envT, envOf]
      split_ifs with h1 h2 h3 h4 h5
      · exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (hσ v h2)⟩
      · exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr ha⟩
      · exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hb⟩
      · exact ⟨le_refl _, by simp [U]⟩
      · exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (hσ' _ (by omega))⟩
      · exact ⟨le_refl _, by simp [U]⟩
    simp only [U] at h1 ⊢
    omega

/-! ### The effect of a write -/

/-- The wrap case of a sum or difference. -/
def mOf (r : Nat → Nat) : Val → Int
  | .add a b => -(((srcVal r a + srcVal r b) / U : Nat) : Int)
  | .sub a b => if srcVal r b ≤ srcVal r a then 0 else 1
  | .any => 0

def mSel (e : Eff) (r : Nat → Nat) : Int :=
  match opOf e with
  | some p => mOf r p.2
  | none => 0

theorem srcOk_lt (σ : MState) (hσ : wfState σ) (x : Src) (h : srcOk x = true) :
    srcVal σ.r x < U := by
  cases x with
  | reg i => simp [srcOk] at h; exact hσ i h
  | imm k => simpa [srcOk] using h

theorem srcE_eval (σ σ' : MState) (fa fb : Nat) (x : Src) (h : srcOk x = true) :
    (srcE x).eval (envT σ σ' fa fb) = srcVal σ.r x := by
  cases x with
  | reg i =>
    simp [srcOk] at h
    simp [srcE, srcVal, pv_eval, envT, envOf, h, show i < 10 by omega]
  | imm k => simp [srcE, srcVal, pconst_eval]

theorem opOf_mem (e : Eff) (p : Nat × Val) (h : opOf e = some p) : p ∈ e.dst ∧ isOp p.2 = true := by
  simp only [opOf] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem wfEff_dst (e : Eff) (h : wfEff e = true) (p : Nat × Val) (hp : p ∈ e.dst) :
    p.1 < 8 ∧ valOk p.2 = true := by
  simp only [wfEff, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1 p hp

theorem mSel_mem (e : Eff) (σ : MState) (hσ : wfState σ) (h : wfEff e = true) :
    mSel e σ.r ∈ mcases e := by
  simp only [mSel, mcases]
  cases hp : opOf e with
  | none => simp
  | some p =>
    simp only [Option.isSome_some, if_true, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false]
    obtain ⟨hm, _⟩ := opOf_mem e p hp
    have hv := (wfEff_dst e h p hm).2
    cases hq : p.2 with
    | add a b =>
      rw [hq] at hv; simp only [valOk, Bool.and_eq_true] at hv
      have ha := srcOk_lt σ hσ a hv.1
      have hb := srcOk_lt σ hσ b hv.2
      simp only [mOf]
      simp only [U] at ha hb ⊢
      omega
    | sub a b => simp only [mOf]; split_ifs <;> simp
    | any => simp [mOf]

/-- The value of a sum or difference, in its wrap case, is the value written. -/
theorem valE_eval (σ σ' : MState) (fa fb : Nat) (hσ : wfState σ) (v : Val) (hv : valOk v = true)
    (i x : Nat) (hx : valOf σ.r v = some x) :
    (valE v (mOf σ.r v) i).eval (envT σ σ' fa fb) = x := by
  cases v with
  | add a b =>
    simp only [valOk, Bool.and_eq_true] at hv
    have ha := srcOk_lt σ hσ a hv.1
    have hb := srcOk_lt σ hσ b hv.2
    simp only [valOf, Option.some.injEq] at hx
    simp only [valE, mOf, padd_eval, pconst_eval, srcE_eval σ σ' fa fb a hv.1, srcE_eval σ σ' fa fb b hv.2]
    subst hx
    simp only [U] at ha hb ⊢
    push_cast
    omega
  | sub a b =>
    simp only [valOk, Bool.and_eq_true] at hv
    have ha := srcOk_lt σ hσ a hv.1
    have hb := srcOk_lt σ hσ b hv.2
    simp only [valOf, Option.some.injEq] at hx
    simp only [valE, mOf, padd_eval, psmul_eval, pconst_eval, srcE_eval σ σ' fa fb a hv.1,
      srcE_eval σ σ' fa fb b hv.2]
    subst hx
    simp only [U] at ha hb ⊢
    split_ifs <;> push_cast <;> omega
  | any => simp [valOf] at hx

theorem valOf_op (r : Nat → Nat) (v : Val) (h : isOp v = true) : ∃ x, valOf r v = some x := by
  cases v <;> simp_all [valOf, isOp]

theorem valOf_lt (r : Nat → Nat) (v : Val) (x : Nat) (h : valOf r v = some x) : x < U := by
  cases v <;> simp only [valOf, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> exact Nat.mod_lt _ (by simp [U])

theorem wrapPrem_holds (e : Eff) (σ σ' : MState) (fa fb : Nat) (hσ : wfState σ) (h : wfEff e = true)
    (ρ : Env) : holds (wrapPrem e (mSel e σ.r)) ρ (envT σ σ' fa fb) := by
  simp only [wrapPrem, mSel]
  cases hp : opOf e with
  | none => intro c hc; simp at hc
  | some p =>
    obtain ⟨i, v⟩ := p
    simp only
    obtain ⟨hm, hop⟩ := opOf_mem e (i, v) hp
    have hv := (wfEff_dst e h (i, v) hm).2
    obtain ⟨x, hx⟩ := valOf_op σ.r v hop
    have hlt := valOf_lt σ.r v x hx
    have hval := valE_eval σ σ' fa fb hσ v hv i x hx
    simp only [PExp.eval] at hval
    intro c hc
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    simp only [U] at hlt
    rcases hc with rfl | rfl <;> simp only [Lin.eval, dot_vsmul, Checker.dot, U] <;> push_cast at hval ⊢ <;> omega

/-! ### The values after an instruction -/

/-- The ghosts after an instruction: kept, the operands of the new flags, or `0`. -/
def postG (e : Eff) (r : Nat → Nat) (fa fb : Nat) : Nat × Nat :=
  match e.fl with
  | .keep => (fa, fb)
  | .any => (0, 0)
  | .add a b => (srcVal r a, srcVal r b)
  | .sub a b => (srcVal r a, srcVal r b)

theorem eq_of_length_le_one {α : Type} : ∀ (l : List α) (x y : α), l.length ≤ 1 → x ∈ l → y ∈ l → x = y
  | [], _, _, _, hx, _ => by simp at hx
  | [z], x, y, _, hx, hy => by simp at hx hy; rw [hx, hy]
  | _ :: _ :: _, _, _, hl, _, _ => by simp at hl

theorem opOf_of_find (e : Eff) (h : wfEff e = true) (i : Nat) (p : Nat × Val)
    (hp : e.dst.find? (fun q => q.1 == i) = some p) (hop : isOp p.2 = true) : opOf e = some p := by
  have hm := List.mem_of_find?_eq_some hp
  simp only [wfEff, Bool.and_eq_true, decide_eq_true_eq] at h
  have hlen := h.1.2
  have hsome : (e.dst.find? fun q => isOp q.2).isSome := List.find?_isSome.mpr ⟨p, hm, hop⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
  have hqm := List.mem_of_find?_eq_some hq
  have hqop : isOp q.2 = true := by simpa using List.find?_some hq
  have : q = p := eq_of_length_le_one _ q p hlen (List.mem_filter.mpr ⟨hqm, hqop⟩)
    (List.mem_filter.mpr ⟨hm, hop⟩)
  simp only [opOf, hq, this]

theorem wfEff_fl (e : Eff) (h : wfEff e = true) :
    match e.fl with
    | .add a b => srcOk a = true ∧ srcOk b = true
    | .sub a b => srcOk a = true ∧ srcOk b = true
    | _ => True := by
  simp only [wfEff, Bool.and_eq_true] at h
  have h3 := h.2
  split <;> simp_all

/-- The value of every variable after the instruction, in the right wrap case. -/
theorem postE_eval (e : Eff) (h : wfEff e = true) (σ σ' : MState) (fa fb : Nat) (hσ : wfState σ)
    (heff : EffOk e σ σ') (v : Nat) (hv : v < 10) :
    (postE e (mSel e σ.r) v).eval (envT σ σ' fa fb) =
      envOf σ' (postG e σ.r fa fb).1 (postG e σ.r fa fb).2 v := by
  obtain ⟨_, hkeep, hwrite, _⟩ := heff
  by_cases h8 : v < 8
  · have hev : envOf σ' (postG e σ.r fa fb).1 (postG e σ.r fa fb).2 v = σ'.r v := by
      simp [envOf, h8]
    rw [hev]
    simp only [postE, h8, if_true]
    cases hf : e.dst.find? (fun p => p.1 == v) with
    | none =>
      simp only
      rw [pv_eval, envT_below _ _ _ _ _ hv]
      simp [envOf, h8, hkeep v h8 hf]
    | some p =>
      simp only
      have hm := List.mem_of_find?_eq_some hf
      have hpv := (wfEff_dst e h p hm).2
      by_cases hop : isOp p.2 = true
      · have hO := opOf_of_find e h v p hf hop
        obtain ⟨x, hx⟩ := valOf_op σ.r p.2 hop
        rw [show mSel e σ.r = mOf σ.r p.2 by simp [mSel, hO]]
        rw [valE_eval σ σ' fa fb hσ p.2 hpv v x hx, hwrite v h8 p hf x hx]
      · have hany : p.2 = .any := by
          cases hq : p.2 <;> simp_all [isOp]
        rw [hany]
        simp [valE, pv_eval, envT, show ¬ (10 + v < 10) by omega, show 10 + v < 18 by omega]
  · have hv89 : v = 8 ∨ v = 9 := by omega
    have hfl := wfEff_fl e h
    simp only [postE, h8, if_false, postG]
    cases hq : e.fl with
    | keep =>
      simp only
      rw [pv_eval, envT_below _ _ _ _ _ hv]
      rcases hv89 with rfl | rfl <;> simp [envOf]
    | any =>
      simp only
      rw [pv_eval]
      rcases hv89 with rfl | rfl <;> simp [envT, envOf]
    | add a b =>
      rw [hq] at hfl
      simp only
      rcases hv89 with rfl | rfl
      · simp only [if_true]; rw [srcE_eval σ σ' fa fb a hfl.1]; simp [envOf]
      · simp only [show (9 : Nat) ≠ 8 by omega, if_false]; rw [srcE_eval σ σ' fa fb b hfl.2]; simp [envOf]
    | sub a b =>
      rw [hq] at hfl
      simp only
      rcases hv89 with rfl | rfl
      · simp only [if_true]; rw [srcE_eval σ σ' fa fb a hfl.1]; simp [envOf]
      · simp only [show (9 : Nat) ≠ 8 by omega, if_false]; rw [srcE_eval σ σ' fa fb b hfl.2]; simp [envOf]

/-! ### Invariants -/

/-- The flags are those of the operation of kind `k` on `a` and `b`. -/
def flagsAt : FKind → Nat → Nat → Flags → Prop
  | .none, _, _, _ => True
  | .add, a, b, f => f = flagsAdd a b
  | .sub, a, b, f => f = flagsSub a b

/-- The meaning of the certificate at instruction `a`, with ghosts `fa`, `fb`. -/
def Inv (f : BFun) (L : DFun) (a : Nat) (σ : MState) (fa fb : Nat) : Prop :=
  wfState σ ∧ fa < U ∧ fb < U ∧ flagsAt (kindAt f L a) fa fb σ.f ∧
    holds (invAt f L a) (fun _ => 0) (envOf σ fa fb)

theorem flags_post (ka kn : FKind) (e : Eff) (h : wfEff e = true) (σ σ' : MState) (hσ : wfState σ)
    (fa fb : Nat) (hfa : fa < U) (hfb : fb < U) (hf : flagsAt ka fa fb σ.f)
    (hk : kindOk ka e.fl kn = true) (hfl : flagsOfE σ.r e.fl σ.f σ'.f) :
    flagsAt kn (postG e σ.r fa fb).1 (postG e σ.r fa fb).2 σ'.f ∧
      (postG e σ.r fa fb).1 < U ∧ (postG e σ.r fa fb).2 < U := by
  have hw := wfEff_fl e h
  simp only [kindOk, Bool.or_eq_true, beq_iff_eq] at hk
  cases hq : e.fl with
  | keep =>
    rw [hq] at hk hfl
    simp only [postG, hq, flagsOfE] at hk hfl ⊢
    refine ⟨?_, hfa, hfb⟩
    rcases hk with hk | hk <;> (try simp only [beq_iff_eq] at hk) <;> subst hk
    · simp [flagsAt]
    · rw [hfl]; exact hf
  | any =>
    rw [hq] at hk
    simp only [postG, hq, reduceCtorEq, or_false] at hk ⊢
    subst hk
    exact ⟨trivial, by simp [U], by simp [U]⟩
  | add a b =>
    rw [hq] at hk hfl hw
    simp only [postG, hq, flagsOfE] at hk hfl ⊢
    refine ⟨?_, srcOk_lt σ hσ a hw.1, srcOk_lt σ hσ b hw.2⟩
    rcases hk with hk | hk <;> (try simp only [beq_iff_eq] at hk) <;> subst hk
    · simp [flagsAt]
    · exact hfl
  | sub a b =>
    rw [hq] at hk hfl hw
    simp only [postG, hq, flagsOfE] at hk hfl ⊢
    refine ⟨?_, srcOk_lt σ hσ a hw.1, srcOk_lt σ hσ b hw.2⟩
    rcases hk with hk | hk <;> (try simp only [beq_iff_eq] at hk) <;> subst hk
    · simp [flagsAt]
    · exact hfl

theorem lin_congr (g : Lin) (hg : wfLin g = true) (ρ ρ' s s' : Env) (h : ∀ v < 10, s v = s' v) :
    g.eval ρ s = g.eval ρ' s' := by
  simp only [wfLin, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hg
  simp only [Lin.eval, hg.1, Checker.dot]
  rw [dot_congr g.sv s s' 10 hg.2 h]

theorem pexp_congr (p : PExp) (hp : p.sv.length ≤ 10) (s s' : Env) (h : ∀ v < 10, s v = s' v) :
    p.eval s = p.eval s' := by
  simp only [PExp.eval]; rw [dot_congr p.sv s s' 10 hp h]

theorem holds_append (A B : List Lin) (ρ s : Env) : holds (A ++ B) ρ s ↔ holds A ρ s ∧ holds B ρ s := by
  simp only [holds, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

/-! ### The checks -/

theorem checkObs_mem : ∀ (obs : List (List Lin × Lin)) (ps : List (Nat × List Nat)),
    checkObs obs ps = true → ∀ o ∈ obs, ∃ p, entails1 o.1 o.2 p = true
  | [], [], _, o, ho => by simp at ho
  | [], _ :: _, h, _, _ => by simp [checkObs] at h
  | _ :: _, [], h, _, _ => by simp [checkObs] at h
  | o' :: os, p :: ps, h, o, ho => by
    simp only [checkObs, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ho with rfl | ho
    · exact ⟨p, h.1⟩
    · exact checkObs_mem os ps h.2 o ho

theorem checkDFun_spec {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (h : checkDFun mul abi c f L = true) :
    closed mul c f.entry f.nodes = true ∧ nodupB f.nodes = true ∧
    f.rows = L.trusted ++ L.loops.map (loopRow f) ∧
    (∀ a ∈ f.nodes, nodeOk mul abi c f L a = true) ∧ kindAt f L f.entry = .none ∧
    (∀ l ∈ L.inv, ∀ g ∈ l, wfLin g = true) ∧ (∀ lc ∈ L.loops, ∀ p ∈ lc.pot, p.sv.length ≤ 10) ∧
    checkObs (obligations mul abi c f L) L.proofs = true := by
  simp only [checkDFun, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem invAt_wf (f : BFun) (L : DFun) (hw : ∀ l ∈ L.inv, ∀ g ∈ l, wfLin g = true) (a : Nat) :
    ∀ g ∈ invAt f L a, wfLin g = true := by
  intro g hg
  simp only [invAt] at hg
  cases hk : find f.nodes a with
  | none => simp [hk] at hg
  | some k =>
    cases hl : L.inv[k]? with
    | none => simp [hk, hl] at hg
    | some l =>
      simp [hk, hl] at hg
      exact hw l (List.mem_of_getElem? hl) g hg

theorem potAt_wf (lc : LoopCert) (hw : ∀ p ∈ lc.pot, p.sv.length ≤ 10) (x : Option Nat) :
    (potAt lc x).sv.length ≤ 10 := by
  cases x with
  | none => simp [potAt, pconst]
  | some a =>
    simp only [potAt]
    cases hk : find lc.body a with
    | none => simp [pconst]
    | some k =>
      cases hp : lc.pot[k]? with
      | none => simp [hp, pconst]
      | some p => simp [hp]; exact hw p (List.mem_of_getElem? hp)

theorem nodeOk_spec {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun} {a : Nat}
    (h : nodeOk mul abi c f L a = true) :
    wfEff (effect abi c a) = true ∧ ∃ i, decode mul c a = some i ∧ ∀ p ∈ trans i a, ∀ n, p.1 = some n →
      kindOk (kindAt f L a) (effect abi c a).fl (kindAt f L n) = true := by
  simp only [nodeOk, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  split at h2
  · cases h2
  · rename_i i hi
    refine ⟨i, hi, fun p hp n hn => ?_⟩
    simp only [List.all_eq_true] at h2
    have := h2 p hp
    rw [hn] at this
    exact this

theorem mem_indexed {α : Type} : ∀ (l : List α) (k j : Nat) (x : α), l[j]? = some x → (k + j, x) ∈ indexed k l
  | [], _, _, _, h => by simp at h
  | y :: ys, k, 0, x, h => by simp at h; subst h; simp [indexed]
  | y :: ys, k, j + 1, x, h => by
    simp only [indexed, List.mem_cons]
    right
    have := mem_indexed ys (k + 1) j x (by simpa using h)
    rwa [show k + 1 + j = k + (j + 1) by omega] at this

/-- The goals of a transition: the invariant of the successor, the descent of the potentials. -/
def tGoals (f : BFun) (L : DFun) (e : Eff) (m : Int) (a : Nat) (next : Option Nat) : List Lin :=
  (match next with
    | some n => (invAt f L n).map fun g => substL g (postE e m)
    | none => []) ++
  L.loops.map fun lc => goalLin (coefStep lc a next) (substP (potAt lc next) (postE e m)) (potAt lc (some a))

theorem obs_mem (mul : Nat) (abi : Bool) (c : Code) (f : BFun) (L : DFun) (a : Nat) (i : Insn)
    (j : Nat) (next : Option Nat) (w : Nat) (calls : List Nat) (m : Int) (D : List Lin) (g : Lin)
    (hdec : decode mul c a = some i) (hj : (trans i a)[j]? = some (next, w, calls))
    (hm : m ∈ mcases (effect abi c a))
    (hD : D ∈ (match i.kind with
      | .cond _ => condFacts (kindAt f L a) (ccOf c a) (j == 0)
      | _ => [[]]))
    (hg : g ∈ tGoals f L (effect abi c a) m a next) :
    (D ++ wrapPrem (effect abi c a) m ++ invAt f L a ++ rangesL, g) ∈ obsOf mul abi c f L a := by
  unfold obsOf
  rw [hdec]
  simp only [List.mem_flatMap, List.mem_map]
  refine ⟨(0 + j, (next, w, calls)), mem_indexed _ 0 j _ hj, m, hm, D, ?_, g, by simpa [tGoals] using hg, rfl⟩
  simpa using hD

/-- One transition: the invariant of the successor holds, and every potential descends by
    the coefficient of the transition in the loop's row. -/
theorem step_ok {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (hc : checkDFun mul abi c f L = true) {a j : Nat} {σ : MState} {next : Option Nat} {w : Nat}
    {calls : List Nat} (ha : a ∈ f.nodes) (hok : DOk mul c a j σ next w calls) {fa fb : Nat}
    (hinv : Inv f L a σ fa fb) (σ' : MState) (hwf' : wfState σ')
    (heff : next ≠ none → EffOk (effect abi c a) σ σ') :
    (∀ n, next = some n →
      Inv f L n σ' (postG (effect abi c a) σ.r fa fb).1 (postG (effect abi c a) σ.r fa fb).2) ∧
    ∀ lc ∈ L.loops, coefStep lc a next +
      (potAt lc next).eval (envOf σ' (postG (effect abi c a) σ.r fa fb).1 (postG (effect abi c a) σ.r fa fb).2) -
      (potAt lc (some a)).eval (envOf σ fa fb) ≤ 0 := by
  obtain ⟨_, _, _, hnodes, _, hwinv, hwpot, hobs⟩ := checkDFun_spec hc
  obtain ⟨hσ, i, hdec, hj, hcond⟩ := hok
  obtain ⟨_, hfa, hfb, hfl, hI⟩ := hinv
  obtain ⟨hwfe, i', hdec', hkind⟩ := nodeOk_spec (hnodes a ha)
  rw [hdec] at hdec'
  cases hdec'
  set e := effect abi c a with he
  set m := mSel e σ.r with hmdef
  have hm : m ∈ mcases e := mSel_mem e σ hσ hwfe
  set env := envT σ σ' fa fb with henv
  have h8 : env 8 = fa := by simp [env, envT, envOf]
  have h9 : env 9 = fb := by simp [env, envT, envOf]
  -- the facts of the branch
  obtain ⟨D, hD, hDh⟩ : ∃ D ∈ (match i.kind with
      | .cond _ => condFacts (kindAt f L a) (ccOf c a) (j == 0)
      | _ => [[]]), holds D (fun _ => 0) env := by
    cases hk : i.kind with
    | cond t =>
      simp only
      have hcc : ccOf c a < 16 := Nat.mod_lt _ (by omega)
      exact condFacts_sound (kindAt f L a) fa fb hfa hfb σ.f
        (by revert hfl; cases kindAt f L a <;> simp [flagsAt]) (ccOf c a) hcc (j == 0)
        (hcond t hk) _ env h8 h9
    | _ => exact ⟨[], by simp, by simp [holds]⟩
  -- the premises hold
  have hprem : holds (D ++ wrapPrem e m ++ invAt f L a ++ rangesL) (fun _ => 0) env := by
    rw [holds_append, holds_append, holds_append]
    refine ⟨⟨⟨hDh, wrapPrem_holds e σ σ' fa fb hσ hwfe _⟩, ?_⟩,
      rangesL_holds σ σ' fa fb hσ hwf' hfa hfb _⟩
    intro g hg
    rw [lin_congr g (invAt_wf f L hwinv a g hg) _ (fun _ => 0) env (envOf σ fa fb)
      (fun v hv => envT_below σ σ' fa fb v hv)]
    exact hI g hg
  -- every goal of the transition holds
  have hgoal : ∀ g ∈ tGoals f L e m a next, g.eval (fun _ => 0) env ≤ 0 := by
    intro g hg
    have hmem := obs_mem mul abi c f L a i j next w calls m D g hdec hj hm hD hg
    have hin : (D ++ wrapPrem e m ++ invAt f L a ++ rangesL, g) ∈ obligations mul abi c f L := by
      simp only [obligations, List.mem_append]
      right
      exact List.mem_flatMap.mpr ⟨a, ha, hmem⟩
    obtain ⟨p, hp⟩ := checkObs_mem _ _ hobs _ hin
    exact entails1_sound hp hprem
  have hpot_a : ∀ lc ∈ L.loops, (potAt lc (some a)).eval env = (potAt lc (some a)).eval (envOf σ fa fb) :=
    fun lc hlc => pexp_congr _ (potAt_wf lc (hwpot lc hlc) _) _ _ (fun v hv => envT_below σ σ' fa fb v hv)
  constructor
  · intro n hn
    subst hn
    have heff' := heff (by simp)
    have hflE := heff'.2.2.2
    have hpost : ∀ v < 10, (postE e m v).eval env =
        envOf σ' (postG e σ.r fa fb).1 (postG e σ.r fa fb).2 v :=
      fun v hv => postE_eval e hwfe σ σ' fa fb hσ heff' v hv
    have hk := hkind (some n, w, calls) (List.mem_of_getElem? hj) n rfl
    obtain ⟨hfl', hga, hgb⟩ := flags_post _ _ e hwfe σ σ' hσ fa fb hfa hfb hfl hk hflE
    refine ⟨hwf', hga, hgb, hfl', ?_⟩
    intro g hg
    have := hgoal (substL g (postE e m)) (by
      simp only [tGoals]; exact List.mem_append_left _ (List.mem_map.mpr ⟨g, hg, rfl⟩))
    rw [substL_eval] at this
    rwa [lin_congr g (invAt_wf f L hwinv n g hg) (fun _ => 0) (fun _ => 0) _ _ hpost] at this
  · intro lc hlc
    have := hgoal _ (by simp only [tGoals]; exact List.mem_append_right _ (List.mem_map.mpr ⟨lc, hlc, rfl⟩))
    rw [goalLin_eval, substP_eval, hpot_a lc hlc] at this
    cases next with
    | none => simpa [potAt, pconst_eval] using this
    | some n =>
      have heff' := heff (by simp)
      have hpost : ∀ v < 10, (postE e m v).eval env =
          envOf σ' (postG e σ.r fa fb).1 (postG e σ.r fa fb).2 v :=
        fun v hv => postE_eval e hwfe σ σ' fa fb hσ heff' v hv
      rwa [pexp_congr _ (potAt_wf lc (hwpot lc hlc) _) _ _ hpost] at this

/-! ### Runs -/

theorem potAt_none (lc : LoopCert) (s : Env) : (potAt lc none).eval s = 0 := by
  simp [potAt, pconst_eval]

/-- Along a chain, the instructions are in the function, the invariants hold, and the sum
    of the coefficients of every loop row is at most the potential at the start. -/
theorem chain_ok {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (hc : checkDFun mul abi c f L = true) :
    ∀ (t : List DStep) (x : DStep) (a fa fb : Nat), DChain abi c (some a) (x :: t) → a ∈ f.nodes →
      (∀ y ∈ x :: t, DOk mul c y.st.a y.j y.σ y.st.next y.st.w y.st.calls) →
      Inv f L a x.σ fa fb →
      (∀ y ∈ x :: t, y.st.a ∈ f.nodes) ∧
      ∀ lc ∈ L.loops, ((x :: t).map fun y => coefStep lc y.st.a y.st.next).sum ≤
        (potAt lc (some a)).eval (envOf x.σ fa fb)
  | [], x, a, fa, fb, hch, ha, hok, hinv => by
    obtain ⟨hxa, _, hrest⟩ := hch
    cases hn : x.st.next with
    | some _ => rw [hn] at hrest; simp [DChain] at hrest
    | none =>
      have hok' := hok x (by simp)
      rw [hxa, hn] at hok'
      obtain ⟨_, hpot⟩ := step_ok hc ha hok' hinv x.σ hinv.1 (fun h => absurd rfl h)
      refine ⟨fun y hy => by simp at hy; rw [hy, hxa]; exact ha, fun lc hlc => ?_⟩
      have := hpot lc hlc
      rw [potAt_none] at this
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hxa, hn]
      linarith
  | y :: t, x, a, fa, fb, hch, ha, hok, hinv => by
    obtain ⟨hxa, heff, hrest⟩ := hch
    cases hn : x.st.next with
    | none => rw [hn] at hrest; simp [DChain] at hrest
    | some n =>
      rw [hn] at hrest
      have hya : y.st.a = n := hrest.1
      have hok' := hok x (by simp)
      rw [hxa, hn] at hok'
      have hwfy : wfState y.σ := (hok y (by simp)).1
      have hE : EffOk (effect abi c a) x.σ y.σ := heff y (by simp)
      obtain ⟨hinvn, hpot⟩ := step_ok hc ha hok' hinv y.σ hwfy (fun _ => hE)
      have hnn : n ∈ f.nodes := by
        obtain ⟨hcl, _⟩ := (checkDFun_spec hc)
        obtain ⟨_, hcl2⟩ := closed_spec mul c f.entry f.nodes hcl
        obtain ⟨i, hi, _, hsucc⟩ := hcl2 a ha
        obtain ⟨_, i', hi', hj, _⟩ := hok'
        rw [hi] at hi'; cases hi'
        exact hsucc _ (List.mem_of_getElem? hj) n rfl
      obtain ⟨hnodes, hsum⟩ := chain_ok hc t y n _ _ hrest hnn (fun z hz => hok z (by simp [hz])) (hinvn n rfl)
      refine ⟨fun z hz => ?_, fun lc hlc => ?_⟩
      · rcases List.mem_cons.mp hz with rfl | hz
        · rw [hxa]; exact ha
        · exact hnodes z hz
      · have h1 := hpot lc hlc
        have h2 := hsum lc hlc
        simp only [List.map_cons, List.sum_cons] at h2 ⊢
        rw [hxa, hn]
        linarith

theorem coefPair_not_mem (h : Nat) (k : Nat → Int) (a : Nat) (n : Option Nat) :
    ∀ nodes : List Nat, a ∉ nodes → coefPair (nodes.map fun u => (u, h, k u)) a n = 0
  | [], _ => rfl
  | u :: us, ha => by
    simp only [List.mem_cons, not_or] at ha
    simp only [List.map_cons, coefPair]
    rw [coefPair_not_mem h k a n us ha.2]
    simp [Ne.symm ha.1]

theorem coefPair_loop (h : Nat) (k : Nat → Int) (a : Nat) (n : Option Nat) :
    ∀ nodes : List Nat, nodupB nodes = true → a ∈ nodes →
      coefPair (nodes.map fun u => (u, h, k u)) a n = if n = some h then k a else 0
  | [], _, ha => by simp at ha
  | u :: us, hd, ha => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_any_beq] at hd
    simp only [List.map_cons, coefPair]
    by_cases hu : u = a
    · subst hu
      have hnot : u ∉ us := by
        intro hm
        have : us.any (fun x => u == x) = true := List.any_eq_true.mpr ⟨u, hm, by simp⟩
        rw [this] at hd; exact absurd hd.1 (by simp)
      rw [coefPair_not_mem h k u n us hnot]
      by_cases hnh : n = some h <;> simp [hnh]
    · have ha' : a ∈ us := by
        rcases List.mem_cons.mp ha with rfl | ha
        · exact absurd rfl hu
        · exact ha
      rw [coefPair_loop h k a n us hd.2 ha']
      simp [hu]

theorem loopRow_coef (f : BFun) (lc : LoopCert) (hd : nodupB f.nodes = true) (a : Nat) (n : Option Nat)
    (ha : a ∈ f.nodes) : coefPair (loopRow f lc).coef a n = coefStep lc a n := by
  simp only [loopRow]
  rw [coefPair_loop lc.header (fun u => if u ∈ lc.body then (lc.scale : Int) else -(lc.bound : Int)) a n
    f.nodes hd ha]
  simp [coefStep]

/-- A certified function: every data run from its entry satisfies the rows of its
    certified loops. -/
theorem chain_rows {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (hc : checkDFun mul abi c f L = true) (s : List DStep) (hch : DChain abi c (some f.entry) s)
    (hok : ∀ y ∈ s, DOk mul c y.st.a y.j y.σ y.st.next y.st.w y.st.calls) :
    ∀ lc ∈ L.loops, (s.map fun y => coefPair (loopRow f lc).coef y.st.a y.st.next).sum ≤ (loopRow f lc).rhs := by
  obtain ⟨hcl, hnd, _, _, hke, hwinv, hwpot, hobs⟩ := checkDFun_spec hc
  cases s with
  | nil => simp [DChain] at hch
  | cons x t =>
    have hwf : wfState x.σ := (hok x (by simp)).1
    have he : f.entry ∈ f.nodes := (closed_spec mul c f.entry f.nodes hcl).1
    have env0 := rangesL_holds x.σ x.σ 0 0 hwf hwf (by simp [U]) (by simp [U]) (fun _ => 0)
    have hinv : Inv f L f.entry x.σ 0 0 := by
      refine ⟨hwf, by simp [U], by simp [U], by rw [hke]; trivial, fun g hg => ?_⟩
      have hin : (rangesL, g) ∈ obligations mul abi c f L := by
        simp only [obligations, List.mem_append, List.mem_map]
        left; left; exact ⟨g, hg, rfl⟩
      obtain ⟨p, hp⟩ := checkObs_mem _ _ hobs _ hin
      have := entails1_sound hp env0
      rwa [lin_congr g (invAt_wf f L hwinv _ g hg) _ (fun _ => 0) _ (envOf x.σ 0 0)
        (fun v hv => envT_below x.σ x.σ 0 0 v hv)] at this
    obtain ⟨hnodes, hsum⟩ := chain_ok hc t x f.entry 0 0 hch he hok hinv
    intro lc hlc
    have hin : (rangesL, goalLin (-(rowRhs f lc)) (potAt lc (some f.entry)) (pconst 0)) ∈
        obligations mul abi c f L := by
      simp only [obligations, List.mem_append, List.mem_map]
      left; right; exact ⟨lc, hlc, rfl⟩
    obtain ⟨p, hp⟩ := checkObs_mem _ _ hobs _ hin
    have h0 := entails1_sound hp env0
    rw [goalLin_eval, pconst_eval, pexp_congr _ (potAt_wf lc (hwpot lc hlc) _) _ (envOf x.σ 0 0)
      (fun v hv => envT_below x.σ x.σ 0 0 v hv)] at h0
    have h1 := hsum lc hlc
    have hsame : ((x :: t).map fun y => coefPair (loopRow f lc).coef y.st.a y.st.next) =
        ((x :: t).map fun y => coefStep lc y.st.a y.st.next) :=
      List.map_congr_left (fun y hy => loopRow_coef f lc hnd _ _ (hnodes y hy))
    rw [hsame]
    simp only [loopRow]
    linarith

theorem callsWith_mono (R1 R2 : Nat → Int → Prop) (h : ∀ g c, R1 g c → R2 g c) :
    ∀ (cs : List Nat) (x : Int), CallsWith R1 cs x → CallsWith R2 cs x
  | [], _, hx => hx
  | g :: gs, x, ⟨c0, hc, hr⟩ => ⟨c0, h g c0 hc, callsWith_mono R1 R2 h gs (x - c0) hr⟩

theorem dchain_mchain (abi : Bool) (c : Code) :
    ∀ (s : List DStep) (o : Option Nat), DChain abi c o s → MChain o (s.map (·.st))
  | [], none, _ => by simp [MChain]
  | [], some _, h => by simp [DChain] at h
  | _ :: _, none, h => by simp [DChain] at h
  | x :: t, some a, ⟨hxa, _, hrest⟩ => ⟨hxa, dchain_mchain abi c t x.st.next hrest⟩

theorem dfAt_spec {mul : Nat} {abi : Bool} {c : Code} {fs : List BFun} {Ls : List DFun}
    (hD : checkData mul abi c fs Ls = true) {e : Nat} {f : BFun} {L : DFun}
    (h : dfAt fs Ls e = some (f, L)) :
    fnAt fs e = some f ∧ checkDFun mul abi c f L = true ∧ f.entry = e := by
  simp only [dfAt] at h
  cases hk : find (fs.map (·.entry)) e with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.bind_some] at h
    cases hf : fs[k]? with
    | none => simp [hf] at h
    | some f' =>
      cases hl : Ls[k]? with
      | none => simp [hf, hl] at h
      | some L' =>
        simp [hf, hl] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp [fnAt, hk, hf], ?_, ?_⟩
        · simp only [checkData, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hD
          exact hD.2 (f', L') (List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hf, hl⟩))
        · have := find_get _ e k hk
          simp [hf] at this
          exact this

/-- Every run of the data semantics is a run of `Thumb.MRun`: the rows of the certified
    loops hold on it. -/
theorem drun_mrun {mul : Nat} {abi : Bool} {c : Code} {fs : List BFun} {Ls : List DFun}
    (hD : checkData mul abi c fs Ls = true) :
    ∀ d e tot, DRun mul abi c fs Ls d e tot → MRun mul c fs d e tot := by
  intro d
  induction d with
  | zero => intro e tot h; simp [DRun] at h
  | succ d ih =>
    intro e tot h
    obtain ⟨f, L, s, hdf, hch, hsteps, htr, htot⟩ := h
    obtain ⟨hfn, hc, hentry⟩ := dfAt_spec hD hdf
    obtain ⟨_, _, hrows, _⟩ := checkDFun_spec hc
    refine ⟨f, s.map (·.st), hfn, dchain_mchain abi c s _ hch, ?_, ?_, ?_⟩
    · intro st hst
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hst
      obtain ⟨⟨_, i, hi, hj, _⟩, hcalls⟩ := hsteps x hx
      exact ⟨step_of hi (List.mem_of_getElem? hj), callsWith_mono _ _ (ih) _ _ hcalls⟩
    · intro r hr
      rw [hrows] at hr
      rw [List.map_map]
      rcases List.mem_append.mp hr with hr | hr
      · exact htr r hr
      · obtain ⟨lc, hlc, rfl⟩ := List.mem_map.mp hr
        rw [← hentry] at hch
        exact chain_rows hc s hch (fun y hy => (hsteps y hy).1) lc hlc
    · rw [htot, List.map_map]; rfl

/-- **Soundness on machine code, loop bounds included**: if `checkBinary` and `checkData`
    accept, every run of the data semantics of the function at entry `e` (the `i`-th of
    the program) costs at most its certified bound. Only the rows left in `trusted` are
    assumed. -/
theorem data_sound (mul : Nat) (abi : Bool) (c : Code) (fs : List BFun) (Cs : List Cert)
    (Ls : List DFun) (h : checkBinary mul c fs Cs = true) (hD : checkData mul abi c fs Ls = true)
    (d e i : Nat) (tot : Int) (hrun : DRun mul abi c fs Ls d e tot)
    (hfind : find (fs.map (·.entry)) e = some i) :
    tot ≤ ((Cs.map Cert.bound).getD i 0 : Nat) :=
  binary_sound mul c fs Cs h d e i tot (drun_mrun hD d e tot hrun) hfind

/-! ### An example: the counting loop of `Thumb.exCode`, its bound proved on the code

`movs r0, #0; cmp r0, #10; bge 0x10a; adds r0, #1; b 0x102; bx lr`. The certificate (made
by `benchmarks/cycles/binloops.py`) gives the loop at `0x102` the potential `10 − r0`
(`11 − r0` after the increment) and the bound 10 back edges per entry; the invariants say
`r0 ≤ 10` and relate the ghosts to `r0` and `10`. No row is trusted: every run of the data
semantics costs at most 68 cycles. -/

open ImperativeOptimization.Checker (Lin) in
section
def exKinds : List FKind := [.none, .none, .sub, .sub, .add, .sub]

def exInv : List (List Lin) :=
  [[],
    [⟨[1], [], -10⟩],
    [⟨[1], [], -10⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, -1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -10⟩, ⟨[-1, 0, 0, 0, 0, 0, 0, 0, 1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -10⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 10⟩],
    [⟨[1], [], -9⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, -1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -9⟩, ⟨[-1, 0, 0, 0, 0, 0, 0, 0, 1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -10⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 10⟩],
    [⟨[1], [], -10⟩, ⟨[-1], [], 1⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, -1], [], -1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -9⟩, ⟨[-1, 0, 0, 0, 0, 0, 0, 0, 1], [], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 1⟩],
    [⟨[1], [], -10⟩, ⟨[-1], [], 10⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -10⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1], [], 10⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -10⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 10⟩]]

def exLoop : LoopCert := ⟨258, [258, 260, 262, 264], 1, 10, [⟨[-1], 10⟩, ⟨[-1], 10⟩, ⟨[-1], 10⟩, ⟨[-1], 11⟩]⟩

def exProofs : List (Nat × List Nat) :=
  [(1, []),
    (1, []),
    (1, []),
    (1, [0, 4294967286]),
    (1, []),
    (1, []),
    (1, [1]),
    (1, [1]),
    (1, []),
    (1, [1]),
    (1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [0, 0, 0, 1]),
    (1, [0, 0, 1, 0, 0, 0, 1, 0, 1]),
    (1, [0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 1, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1]),
    (1, [0, 3, 0, 0, 0, 0, 3, 0, 0, 1]),
    (1, [0, 1, 0, 0, 0, 0, 1, 0, 1]),
    (1, [0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 3, 0, 0, 0, 0, 3, 0, 0, 1]),
    (1, [0, 0, 1, 0, 1, 0, 0, 1]),
    (1, [0, 0, 0, 0, 1]),
    (1, [0, 0, 1, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, [3, 0, 0, 0, 3, 0, 0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, [0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, [0, 0, 1]),
    (1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [0, 4294967291, 0, 0, 0, 0, 0, 0, 4294967291, 1]),
    (1, [0, 1, 0, 0, 0, 0, 0, 0, 2]),
    (1, [0, 2147483648, 0, 0, 0, 0, 0, 0, 2147483648]),
    (1, [0, 2147483643, 0, 0, 0, 0, 0, 0, 2147483643, 1]),
    (1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 2, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 2]),
    (1, []),
    (1, []),
    (1, [2, 0, 2]),
    (1, [1]),
    (1, []),
    (1, [])]


def exDFun : DFun := ⟨exKinds, exInv, [exLoop], [], exProofs⟩

def exFunD0 : BFun := ⟨0x100, [0x100, 0x102, 0x104, 0x106, 0x108, 0x10A], []⟩

/-- The function with the row of its certified loop (generated, `loopRow`). -/
def exFunD : BFun := { exFunD0 with rows := [loopRow exFunD0 exLoop] }

theorem exData_checks : checkData 32 false exCode [exFunD] [exDFun] = true := by decide

theorem exBinaryD_checks : checkBinary 32 exCode [exFunD] [exCert] = true := by decide

/-- A bound of 9 iterations is refused. -/
theorem exData_tight :
    checkData 32 false exCode [{ exFunD0 with rows := [loopRow exFunD0 { exLoop with bound := 9 }] }]
      [⟨exKinds, exInv, [{ exLoop with bound := 9 }], [], exProofs⟩] = false := by decide

/-- Every run of the data semantics of the example costs at most 68 cycles, with no
    trusted row. -/
theorem exData_sound (d : Nat) (tot : Int) (h : DRun 32 false exCode [exFunD] [exDFun] d 0x100 tot) :
    tot ≤ 68 :=
  data_sound 32 false exCode [exFunD] [exCert] [exDFun] exBinaryD_checks exData_checks d 0x100 0 tot h
    (by decide)

end

end ImperativeOptimization.Thumb
