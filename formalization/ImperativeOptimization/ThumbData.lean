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
AddWithCarry computes them, any value where the effect says so. The stack pointer and the
memory follow `stackEffect` (`StackOk`): a load through SP gives the word stored there, a
load from the literal pool the word of the code, any other load any value. A call is one
step, whose effect is that of `BL` in `effect`.

`data_sound`: if `checkBinary` and `checkData` accept, every run in this semantics costs at
most the certified bound; only the rows the certificate leaves as trusted are assumed. The
proof shows that the invariants hold at every step and that the potentials telescope, so
that the rows of the certified loops hold (`chain_rows`), and that a run of the data
semantics is a run of `Thumb.MRun` (`drun_mrun`).

Trusted, as the specification of the processor: `decode` and `effect`, the flags and the
conditions, the semantics above (no interrupts; a callee changes only the registers that
`effect` lets a call change); and that the code is that of the binary and is not written
during a run (a load from the literal pool gives the word of the code, `effect`).
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

/-- The stack pointer and the memory hold words. -/
def wfStack (σ : MState) : Prop := σ.sp < U ∧ ∀ A, σ.mem A < U

/-- The effect of an instruction on the stack pointer and the memory (`SP₀`: the stack
    pointer at the entry of the function). A word loaded from `sp + imm` is the word
    there; a store through SP writes the register; PUSH writes the words below SP; a store
    through another register or a call may write any word, except, with the assumption
    `frame`, the words of the function's frame (from SP up to `SP₀`). -/
def StackOk (frame : Bool) (SP0 : Nat) (s : StackE) (σ σ' : MState) : Prop :=
  wfStack σ' ∧
  (match s.sp with
   | .keep => σ'.sp = σ.sp
   | .add k => σ'.sp = aOf (σ.sp + k)
   | .any => True) ∧
  (match s.mem with
   | .keep => ∀ A, σ'.mem A = σ.mem A
   | .storeSP imm rt => σ'.mem (aOf (σ.sp + imm)) = σ.r rt ∧
       ∀ A, A ≠ aOf (σ.sp + imm) → σ'.mem A = σ.mem A
   | .push n => ∀ A, (∀ i < n, A ≠ aOf (σ.sp - 4 * ((i : Int) + 1))) → σ'.mem A = σ.mem A
   | .other => frame = true → ∀ k : Int, 0 < k → k ≤ ((SP0 : Int) - σ.sp) % (U : Int) →
       σ'.mem (aOf (SP0 - k)) = σ.mem (aOf (SP0 - k))) ∧
  (∀ p, s.load = some p → σ'.r p.1 = σ.mem (aOf (σ.sp + p.2)))

/-- The step of the machine: the instruction at `a`, in state `σ`, takes its `j`-th
    transition (to `next`, with `w` cycles, calling `calls`); `ADD PC, rm` and `MOV PC, rm`
    (`m < 8`) go to the address computed from `rm` (`pcDestV`, bit 0 cleared), in 3 cycles. -/
def DOkM (mul : Nat) (c : Code) (a j : Nat) (σ : MState) (next : Option Nat) (w : Nat)
    (calls : List Nat) : Prop :=
  wfState σ ∧ wfStack σ ∧ ∃ i, decode mul c a = some i ∧
    (((trans i a)[j]? = some (next, w, calls) ∧
      (∀ t, i.kind = .cond t → condHolds (ccOf c a) σ.f = (j == 0))) ∨
     (i.kind = .stop ∧ ∃ add m, pcWrite c a = some (add, m) ∧
       next = some (pcDestV a add (σ.r m)) ∧ w = 3 ∧ calls = []))

/-- A step along the transitions of the function (`transJ`: those of `decode`, and the
    targets of the jumps listed in `J`). Every step of a data run is one
    (`dokm_dok`, by `jumpOk` and `interiorOk`). -/
def DOk (mul : Nat) (c : Code) (J : List JT) (a j : Nat) (σ : MState) (next : Option Nat) (w : Nat)
    (calls : List Nat) : Prop :=
  wfState σ ∧ wfStack σ ∧ ∃ i, decode mul c a = some i ∧ (transJ J i a)[j]? = some (next, w, calls) ∧
    (∀ t, i.kind = .cond t → condHolds (ccOf c a) σ.f = (j == 0))

/-- The exact values of `ADD rd, PC`, of `ADR` and of the loads from the code (`xop`):
    the register gets the value `xres` computes from the registers before (a load from the
    code gives the code: the code is not written during a run). -/
def XOk (c : Code) (a : Nat) (σ σ' : MState) : Prop :=
  (∀ op, xop c a = some op → ∀ v, xres c a (fun i => some (σ.r i)) op = some v → σ'.r op.dst = v) ∧
  -- the bounds of `rngOps`: `ANDS` by either operand, `LSRS` by a constant, `UXTB`, `LDRB`
  ∀ q ∈ rngOps c a, σ'.r q.1 ≤ srcVal σ.r q.2

/-- A step of a data run: the step of the machine run, the transition taken, the state
    before it. -/
structure DStep where
  st : MStep
  j : Nat
  σ : MState

/-- `XOk` between consecutive steps. -/
def XChain (c : Code) (s : List DStep) : Prop :=
  ∀ (k : Nat) (x y : DStep), s[k]? = some x → s[k + 1]? = some y → XOk c x.st.a x.σ y.σ

/-- The steps follow each other from the given address until a return, each state being
    the effect of the previous instruction on the previous state (`SP₀`: the stack pointer
    at the entry). -/
def DChain (abi frame : Bool) (c : Code) (SP0 : Nat) : Option Nat → List DStep → Prop
  | none, [] => True
  | some a, x :: t => x.st.a = a ∧
      (∀ y ∈ t.head?, EffOk (effect abi c a) x.σ y.σ ∧ StackOk frame SP0 (stackEffect abi c a) x.σ y.σ) ∧
      DChain abi frame c SP0 x.st.next t
  | _, _ => False

/-- The stack pointer at the first step. -/
def headSp : List DStep → Nat
  | x :: _ => x.σ.sp
  | [] => 0

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
  | d + 1, e, total => ∃ f L s, dfAt fs Ls e = some (f, L) ∧ DChain abi L.frame c (headSp s) (some e) s ∧
      XChain c s ∧
      (∀ x ∈ s, DOkM mul c x.st.a x.j x.σ x.st.next x.st.w x.st.calls ∧
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

/-- The tracked word `j` of the frame: the word at `SP₀ − slots[j]`. -/
def slotVal (σ : MState) (SP0 : Nat) (slots : List Nat) (j : Nat) : Int :=
  (σ.mem (aOf ((SP0 : Int) - ((slots.getD j 0 : Nat) : Int))) : Int)

/-- The variables of a state: registers `0`-`7`, the ghosts `8`, `9`, the tracked words
    `20`.. of the frame. -/
def envOf (σ : MState) (fa fb : Nat) (SP0 : Nat) (slots : List Nat) : Env := fun v =>
  if v < 8 then (σ.r v : Int) else if v = 8 then (fa : Int) else if v = 9 then (fb : Int)
  else if 20 ≤ v ∧ v < 20 + slots.length then slotVal σ SP0 slots (v - 20) else 0

/-- The variables of a transition: those of the state before, the registers after
    (`10`-`17`), the fresh ghosts `18`, `19` (`0`), the tracked words before, then after
    (`20 + S`..). -/
def envT (σ σ' : MState) (fa fb : Nat) (SP0 : Nat) (slots : List Nat) : Env := fun v =>
  if v < 10 then envOf σ fa fb SP0 slots v else if v < 18 then (σ'.r (v - 10) : Int)
  else if v < 20 then 0
  else if v < 20 + slots.length then envOf σ fa fb SP0 slots v
  else if v < 20 + 2 * slots.length then slotVal σ' SP0 slots (v - 20 - slots.length) else 0

theorem envT_below (σ σ' : MState) (fa fb SP0 : Nat) (slots : List Nat) (v : Nat) (hv : v < 10) :
    envT σ σ' fa fb SP0 slots v = envOf σ fa fb SP0 slots v := by simp [envT, hv]

theorem envT_state (σ σ' : MState) (fa fb SP0 : Nat) (slots : List Nat) (v : Nat)
    (hv : v < 10 ∨ 20 ≤ v ∧ v < 20 + slots.length) :
    envT σ σ' fa fb SP0 slots v = envOf σ fa fb SP0 slots v := by
  rcases hv with hv | hv
  · simp [envT, hv]
  · simp only [envT]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hv.2]

theorem rangesN_holds (σ σ' : MState) (fa fb SP0 : Nat) (slots : List Nat) (hσ : wfState σ)
    (hσ' : wfState σ') (hs : wfStack σ) (hs' : wfStack σ') (ha : fa < U) (hb : fb < U) (ρ : Env) :
    holds (rangesN (nVars slots.length)) ρ (envT σ σ' fa fb SP0 slots) := by
  intro e he
  simp only [rangesN, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at he
  obtain ⟨v, _, rfl | rfl⟩ := he
  all_goals
    simp only [mk_eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have h1 : 0 ≤ envT σ σ' fa fb SP0 slots v ∧ envT σ σ' fa fb SP0 slots v < (U : Int) := by
      simp only [envT, envOf, slotVal]
      split_ifs
      all_goals first
        | exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (hσ _ (by omega))⟩
        | exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr ha⟩
        | exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hb⟩
        | exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (hσ' _ (by omega))⟩
        | exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (hs.2 _)⟩
        | exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (hs'.2 _)⟩
        | exact ⟨le_refl _, by simp [U]⟩
    simp only [U] at h1 ⊢
    omega

/-! ### The effect of a write -/

/-- The wrap case of a sum or difference. -/
def mOf (r : Nat → Nat) : Val → Int
  | .add a b => -(((srcVal r a + srcVal r b) / U : Nat) : Int)
  | .sub a b => if srcVal r b ≤ srcVal r a then 0 else 1
  | .shl a k => if srcVal r a * 2 ^ k < U then 0 else 1
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

theorem srcE_eval (σ σ' : MState) (fa fb SP0 : Nat) (slots : List Nat) (x : Src) (h : srcOk x = true) :
    (srcE x).eval (envT σ σ' fa fb SP0 slots) = srcVal σ.r x := by
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
    | shl a k => simp only [mOf]; split_ifs <;> simp
    | any => simp [mOf]

/-- The value of a sum or difference, in its wrap case, is the value written. -/
theorem valE_eval_ar (σ σ' : MState) (fa fb SP0 : Nat) (slots : List Nat) (hσ : wfState σ) (v : Val) (hv : valOk v = true)
    (hs : ¬ ∃ a k, v = .shl a k) (i x : Nat) (hx : valOf σ.r v = some x) :
    (valE v (mOf σ.r v) i).eval (envT σ σ' fa fb SP0 slots) = x := by
  cases v with
  | shl a k => exact absurd ⟨a, k, rfl⟩ hs
  | add a b =>
    simp only [valOk, Bool.and_eq_true] at hv
    have ha := srcOk_lt σ hσ a hv.1
    have hb := srcOk_lt σ hσ b hv.2
    simp only [valOf, Option.some.injEq] at hx
    simp only [valE, mOf, padd_eval, pconst_eval, srcE_eval σ σ' fa fb SP0 slots a hv.1, srcE_eval σ σ' fa fb SP0 slots b hv.2]
    subst hx
    simp only [U] at ha hb ⊢
    push_cast
    omega
  | sub a b =>
    simp only [valOk, Bool.and_eq_true] at hv
    have ha := srcOk_lt σ hσ a hv.1
    have hb := srcOk_lt σ hσ b hv.2
    simp only [valOf, Option.some.injEq] at hx
    simp only [valE, mOf, padd_eval, psmul_eval, pconst_eval, srcE_eval σ σ' fa fb SP0 slots a hv.1,
      srcE_eval σ σ' fa fb SP0 slots b hv.2]
    subst hx
    simp only [U] at ha hb ⊢
    split_ifs <;> push_cast <;> omega
  | any => simp [valOf] at hx

/-- The value of a sum, difference or shift, in its wrap case, is the value written. -/
theorem valE_eval (σ σ' : MState) (fa fb SP0 : Nat) (slots : List Nat) (hσ : wfState σ) (v : Val) (hv : valOk v = true)
    (i x : Nat) (hx : valOf σ.r v = some x) (hi : i < 8) (hw : σ'.r i = x) :
    (valE v (mOf σ.r v) i).eval (envT σ σ' fa fb SP0 slots) = x := by
  by_cases hs : ∃ a k, v = .shl a k
  · obtain ⟨a, k, rfl⟩ := hs
    simp only [valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [valOf, Option.some.injEq] at hx
    by_cases h1 : srcVal σ.r a * 2 ^ k < U
    · simp only [valE, mOf, h1, if_true]
      rw [psmul_eval, srcE_eval σ σ' fa fb SP0 slots a hv.1, ← hx, Nat.mod_eq_of_lt h1]
      push_cast; ring
    · simp only [valE, mOf, h1, if_false, show (1 : Int) ≠ 0 by decide]
      rw [pv_eval]
      simp [envT, show ¬ (10 + i < 10) by omega, show 10 + i < 18 by omega, hw]
  · exact valE_eval_ar σ σ' fa fb SP0 slots hσ v hv hs i x hx

theorem valOf_op (r : Nat → Nat) (v : Val) (h : isOp v = true) : ∃ x, valOf r v = some x := by
  cases v <;> simp_all [valOf, isOp]

theorem valOf_lt (r : Nat → Nat) (v : Val) (x : Nat) (h : valOf r v = some x) : x < U := by
  cases v <;> simp only [valOf, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> exact Nat.mod_lt _ (by simp [U])

theorem wrapPrem_holds (e : Eff) (σ σ' : MState) (fa fb SP0 : Nat) (slots : List Nat) (hσ : wfState σ) (h : wfEff e = true)
    (ρ : Env) : holds (wrapPrem e (mSel e σ.r)) ρ (envT σ σ' fa fb SP0 slots) := by
  simp only [wrapPrem, mSel]
  cases hp : opOf e with
  | none => intro c hc; simp at hc
  | some p =>
    obtain ⟨i, v⟩ := p
    simp only
    obtain ⟨hm, hop⟩ := opOf_mem e (i, v) hp
    have hv := (wfEff_dst e h (i, v) hm).2
    have hi := (wfEff_dst e h (i, v) hm).1
    obtain ⟨x, hx⟩ := valOf_op σ.r v hop
    have hlt := valOf_lt σ.r v x hx
    cases v with
    | shl a k =>
      simp only [valOk, Bool.and_eq_true, decide_eq_true_eq] at hv
      have hae := srcE_eval σ σ' fa fb SP0 slots a hv.1
      simp only [PExp.eval] at hae
      have key : ((2 ^ k : Nat) : Int) * Checker.dot (srcE a).sv (envT σ σ' fa fb SP0 slots) +
          ((2 ^ k : Nat) : Int) * (srcE a).c = ((srcVal σ.r a * 2 ^ k : Nat) : Int) := by
        rw [← mul_add, hae]; push_cast; ring
      have hN := Int.natCast_nonneg (srcVal σ.r a * 2 ^ k)
      intro c hc
      by_cases h1 : srcVal σ.r a * 2 ^ k < U
      · simp only [mOf, h1, if_true, valE, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at hc
        have h1' : ((srcVal σ.r a * 2 ^ k : Nat) : Int) < (U : Int) := by exact_mod_cast h1
        rcases hc with rfl | rfl <;>
          simp only [Lin.eval, dot_vsmul, Checker.dot, psmul] <;>
          simp only [Checker.dot, dot_vsmul] at key ⊢ <;> simp only [U] at h1' ⊢ <;> push_cast at key h1' hN ⊢ <;> linarith
      · simp only [mOf, h1, if_false, show (1 : Int) ≠ 0 by decide, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hc
        have h1' : (U : Int) ≤ ((srcVal σ.r a * 2 ^ k : Nat) : Int) := by exact_mod_cast not_lt.mp h1
        subst hc
        simp only [Lin.eval, dot_vsmul, Checker.dot, psmul] at key ⊢
        simp only [U] at h1' ⊢
        push_cast at key h1' ⊢
        linarith
    | add a b =>
      have hval := valE_eval_ar σ σ' fa fb SP0 slots hσ _ hv (by simp) i x hx
      simp only [PExp.eval] at hval
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      simp only [U] at hlt
      rcases hc with rfl | rfl <;> simp only [Lin.eval, dot_vsmul, Checker.dot, U] <;> push_cast at hval ⊢ <;> omega
    | sub a b =>
      have hval := valE_eval_ar σ σ' fa fb SP0 slots hσ _ hv (by simp) i x hx
      simp only [PExp.eval] at hval
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      simp only [U] at hlt
      rcases hc with rfl | rfl <;> simp only [Lin.eval, dot_vsmul, Checker.dot, U] <;> push_cast at hval ⊢ <;> omega
    | any => simp [isOp] at hop

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
theorem postE_eval (e : Eff) (h : wfEff e = true) (σ σ' : MState) (fa fb SP0 : Nat) (slots : List Nat) (hσ : wfState σ)
    (heff : EffOk e σ σ') (v : Nat) (hv : v < 10) :
    (postE e (mSel e σ.r) v).eval (envT σ σ' fa fb SP0 slots) =
      envOf σ' (postG e σ.r fa fb).1 (postG e σ.r fa fb).2 SP0 slots v := by
  obtain ⟨_, hkeep, hwrite, _⟩ := heff
  by_cases h8 : v < 8
  · have hev : envOf σ' (postG e σ.r fa fb).1 (postG e σ.r fa fb).2 SP0 slots v = σ'.r v := by
      simp [envOf, h8]
    rw [hev]
    simp only [postE, h8, if_true]
    cases hf : e.dst.find? (fun p => p.1 == v) with
    | none =>
      simp only
      rw [pv_eval, envT_below _ _ _ _ _ _ _ hv]
      simp [envOf, h8, hkeep v h8 hf]
    | some p =>
      simp only
      have hm := List.mem_of_find?_eq_some hf
      have hpv := (wfEff_dst e h p hm).2
      by_cases hop : isOp p.2 = true
      · have hO := opOf_of_find e h v p hf hop
        obtain ⟨x, hx⟩ := valOf_op σ.r p.2 hop
        rw [show mSel e σ.r = mOf σ.r p.2 by simp [mSel, hO]]
        rw [valE_eval σ σ' fa fb SP0 slots hσ p.2 hpv v x hx h8 (hwrite v h8 p hf x hx), hwrite v h8 p hf x hx]
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
      rw [pv_eval, envT_below _ _ _ _ _ _ _ hv]
      rcases hv89 with rfl | rfl <;> simp [envOf]
    | any =>
      simp only
      rw [pv_eval]
      rcases hv89 with rfl | rfl <;> simp [envT, envOf]
    | add a b =>
      rw [hq] at hfl
      simp only
      rcases hv89 with rfl | rfl
      · simp only [if_true]; rw [srcE_eval σ σ' fa fb SP0 slots a hfl.1]; simp [envOf]
      · simp only [show (9 : Nat) ≠ 8 by omega, if_false]; rw [srcE_eval σ σ' fa fb SP0 slots b hfl.2]; simp [envOf]
    | sub a b =>
      rw [hq] at hfl
      simp only
      rcases hv89 with rfl | rfl
      · simp only [if_true]; rw [srcE_eval σ σ' fa fb SP0 slots a hfl.1]; simp [envOf]
      · simp only [show (9 : Nat) ≠ 8 by omega, if_false]; rw [srcE_eval σ σ' fa fb SP0 slots b hfl.2]; simp [envOf]

/-! ### Invariants -/

/-- The flags are those of the operation of kind `k` on `a` and `b`. -/
def flagsAt : FKind → Nat → Nat → Flags → Prop
  | .none, _, _, _ => True
  | .add, a, b, f => f = flagsAdd a b
  | .sub, a, b, f => f = flagsSub a b

/-- The congruences hold. -/
def CongHolds (cs : List Cong) (s : Env) : Prop :=
  ∀ x ∈ cs, s x.1 % ((2 ^ x.2.1 : Nat) : Int) = (x.2.2 : Int) % ((2 ^ x.2.1 : Nat) : Int)

/-- The meaning of the certificate at instruction `a`, with ghosts `fa`, `fb`, in a run
    whose stack pointer at the entry is `SP0`. -/
def Inv (f : BFun) (L : DFun) (SP0 : Nat) (a : Nat) (σ : MState) (fa fb : Nat) : Prop :=
  wfState σ ∧ wfStack σ ∧ fa < U ∧ fb < U ∧ flagsAt (kindAt f L a) fa fb σ.f ∧
    (∀ d, spAt f L a = some d → σ.sp = aOf (SP0 + d)) ∧
    (∃ I ∈ invsAt f L a, holds I (fun _ => 0) (envOf σ fa fb SP0 L.slots)) ∧
    CongHolds (congAt f L a) (envOf σ fa fb SP0 L.slots)

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

theorem dot_congr_nz : ∀ (l : List Int) (f g : Env),
    (∀ v < l.length, l.getD v 0 ≠ 0 → f v = g v) → Checker.dot l f = Checker.dot l g
  | [], _, _, _ => rfl
  | a :: l, f, g, h => by
    simp only [Checker.dot]
    have h0 : a * f 0 = a * g 0 := by
      by_cases ha : a = 0
      · simp [ha]
      · rw [h 0 (by simp) (by simpa using ha)]
    rw [h0, dot_congr_nz l (fun i => f (i + 1)) (fun i => g (i + 1))
      (fun v hv hne => h (v + 1) (by simp; omega) (by simpa using hne))]

theorem wfSv_congr (S : Nat) (sv : List Int) (h : wfSv S sv = true) (f g : Env)
    (hfg : ∀ v, (v < 10 ∨ 20 ≤ v ∧ v < 20 + S) → f v = g v) :
    Checker.dot sv f = Checker.dot sv g := by
  simp only [wfSv, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  apply dot_congr_nz
  intro v hv hne
  apply hfg
  by_cases h10 : v < 10
  · exact Or.inl h10
  · right
    refine ⟨?_, by omega⟩
    by_contra h20
    have := h.2 (v - 10) (by omega)
    rw [show 10 + (v - 10) = v by omega] at this
    exact hne this

theorem lin_congr (S : Nat) (g : Lin) (hg : wfLin S g = true) (ρ ρ' s s' : Env)
    (h : ∀ v, (v < 10 ∨ 20 ≤ v ∧ v < 20 + S) → s v = s' v) : g.eval ρ s = g.eval ρ' s' := by
  simp only [wfLin, Bool.and_eq_true, List.isEmpty_iff] at hg
  simp only [Lin.eval, hg.1, Checker.dot]
  rw [wfSv_congr S g.sv hg.2 s s' h]

theorem pexp_congr (S : Nat) (p : PExp) (hp : wfSv S p.sv = true) (s s' : Env)
    (h : ∀ v, (v < 10 ∨ 20 ≤ v ∧ v < 20 + S) → s v = s' v) : p.eval s = p.eval s' := by
  simp only [PExp.eval]; rw [wfSv_congr S p.sv hp s s' h]

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
    closed mul c f.jumps f.entry f.nodes = true ∧ nodupB f.nodes = true ∧
    f.rows = L.trusted ++ L.loops.map (loopRow f) ∧
    (∀ a ∈ f.nodes, nodeOk mul abi c f L a = true) ∧ kindAt f L f.entry = .none ∧
    (spAt f L f.entry = some 0 ∨ spAt f L f.entry = none) ∧ slotsOk L = true ∧
    (∀ l ∈ L.inv, ∀ g ∈ l, wfLin L.slots.length g = true) ∧
    (∀ lc ∈ L.loops, ∀ p ∈ lc.pot, wfSv L.slots.length p.sv = true) ∧
    checkObs (obligations mul abi c f L) L.proofs = true := by
  simp only [checkDFun, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, _⟩, h9⟩, h10⟩, _⟩, _⟩, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem checkDFun_alt {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (h : checkDFun mul abi c f L = true) :
    ∀ l ∈ L.alt, ∀ I ∈ l, ∀ g ∈ I, wfLin L.slots.length g = true := by
  simp only [checkDFun, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, ha⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact ha

theorem checkDFun_cong {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (h : checkDFun mul abi c f L = true) :
    congAt f L f.entry = [] ∧ (∀ l ∈ L.cong, ∀ x ∈ l, wfCong L.slots.length x = true) ∧
    ∀ a ∈ f.nodes, congOk mul abi c f L a = true := by
  simp only [checkDFun, Bool.and_eq_true] at h
  have h' := h.1.1.2
  simp only [congChecks, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩

/-! ### Congruences -/

theorem congOf_sound (cs : List Cong) (s : Env) (h : CongHolds cs s) (v : Nat) :
    s v % ((2 ^ (congOf cs v).1 : Nat) : Int) = ((congOf cs v).2 : Int) % ((2 ^ (congOf cs v).1 : Nat) : Int) := by
  unfold congOf
  split
  · rename_i x hf
    have hx := List.mem_of_find?_eq_some hf
    have hv : x.1 = v := by simpa using List.find?_some hf
    rw [← hv]
    exact h x hx
  · simp [Int.emod_one]

theorem congOf_dvd (cs : List Cong) (s : Env) (h : CongHolds cs s) (v : Nat) :
    ((2 ^ (congOf cs v).1 : Nat) : Int) ∣ s v - (congOf cs v).2 :=
  Int.ModEq.dvd (congOf_sound cs s h v).symm

theorem foldl_max_mem : ∀ (l : List Nat) (acc : Nat), l.foldl max acc = acc ∨ l.foldl max acc ∈ l
  | [], acc => Or.inl rfl
  | x :: l, acc => by
    rcases foldl_max_mem l (max acc x) with h | h
    · simp only [List.foldl_cons, h]
      rcases Nat.le_total acc x with hx | hx
      · right; simp [Nat.max_eq_right hx]
      · left; exact Nat.max_eq_left hx
    · right; simp only [List.foldl_cons]; exact List.mem_cons_of_mem _ h

theorem gExp_dvd (cs : List Cong) (s : Env) (h : CongHolds cs s) :
    ((2 ^ gExp cs : Nat) : Int) ∣ s 8 - s 9 := by
  unfold gExp
  rcases foldl_max_mem ((List.range 33).filter fun e => decide (e ≤ (congOf cs 8).1 ∧ e ≤ (congOf cs 9).1 ∧
      ((congOf cs 8).2 : Int) % (2 ^ e : Nat) = ((congOf cs 9).2 : Int) % (2 ^ e : Nat))) 0 with h0 | hm
  · simp only at h0 ⊢
    rw [h0]; simp
  · simp only at hm ⊢
    set e := List.foldl max 0 _ with he
    simp only [List.mem_filter, decide_eq_true_eq] at hm
    obtain ⟨h8, h9, hr⟩ := hm.2
    have d8 : ((2 ^ e : Nat) : Int) ∣ ((2 ^ (congOf cs 8).1 : Nat) : Int) :=
      Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h8)
    have d9 : ((2 ^ e : Nat) : Int) ∣ ((2 ^ (congOf cs 9).1 : Nat) : Int) :=
      Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h9)
    have a8 := dvd_trans d8 (congOf_dvd cs s h 8)
    have a9 := dvd_trans d9 (congOf_dvd cs s h 9)
    have ar : ((2 ^ e : Nat) : Int) ∣ ((congOf cs 8).2 : Int) - (congOf cs 9).2 :=
      Int.ModEq.dvd hr.symm
    have : s 8 - s 9 = (s 8 - (congOf cs 8).2) - (s 9 - (congOf cs 9).2) + (((congOf cs 8).2 : Int) - (congOf cs 9).2) := by ring
    rw [this]
    exact dvd_add (dvd_sub a8 a9) ar

theorem gExpS_dvd (cs : List Cong) (s : Env) (h : CongHolds cs s) :
    ((2 ^ gExpS cs : Nat) : Int) ∣ s 8 + s 9 := by
  unfold gExpS
  rcases foldl_max_mem ((List.range 33).filter fun e => decide (e ≤ (congOf cs 8).1 ∧ e ≤ (congOf cs 9).1 ∧
      (((congOf cs 8).2 : Int) + (congOf cs 9).2) % (2 ^ e : Nat) = 0)) 0 with h0 | hm
  · simp only at h0 ⊢
    rw [h0]; simp
  · simp only at hm ⊢
    set e := List.foldl max 0 _ with he
    simp only [List.mem_filter, decide_eq_true_eq] at hm
    obtain ⟨h8, h9, hr⟩ := hm.2
    have d8 : ((2 ^ e : Nat) : Int) ∣ ((2 ^ (congOf cs 8).1 : Nat) : Int) :=
      Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h8)
    have d9 : ((2 ^ e : Nat) : Int) ∣ ((2 ^ (congOf cs 9).1 : Nat) : Int) :=
      Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h9)
    have a8 := dvd_trans d8 (congOf_dvd cs s h 8)
    have a9 := dvd_trans d9 (congOf_dvd cs s h 9)
    have ar : ((2 ^ e : Nat) : Int) ∣ ((congOf cs 8).2 : Int) + (congOf cs 9).2 :=
      Int.dvd_of_emod_eq_zero hr
    have : s 8 + s 9 = (s 8 - (congOf cs 8).2) + (s 9 - (congOf cs 9).2) + (((congOf cs 8).2 : Int) + (congOf cs 9).2) := by ring
    rw [this]
    exact dvd_add (dvd_add a8 a9) ar

theorem sumC_sv (k : Int) (s : Env) : Checker.dot (sumC k 0).sv s = k * (s 8 + s 9) := by
  have h := sumC_eval k 0 (fun _ => 0) s
  have hlv : (sumC k 0).lv = [] := rfl
  have hc : (sumC k 0).c = 0 := rfl
  simp only [Checker.Lin.eval, hlv, hc, Checker.dot] at h
  linarith

theorem dle_sv (s : Env) : Checker.dot (dle 0).sv s = s 8 - s 9 := by
  have h := dle_eval 0 (fun _ => 0) s
  have hlv : (dle 0).lv = [] := rfl
  have hc : (dle 0).c = 0 := rfl
  simp only [Checker.Lin.eval, hlv, hc, Checker.dot] at h
  linarith

theorem dge_sv (s : Env) : Checker.dot (dge 0).sv s = s 9 - s 8 := by
  have h := dge_eval 0 (fun _ => 0) s
  have hlv : (dge 0).lv = [] := rfl
  have hc : (dge 0).c = 0 := rfl
  simp only [Checker.Lin.eval, hlv, hc, Checker.dot] at h
  linarith

theorem round_le (M d c : Int) (hM : 0 < M) (hd : M ∣ d) (h : d + c ≤ 0) :
    d + -((-c) / M * M) ≤ 0 := by
  obtain ⟨q, rfl⟩ := hd
  have : q ≤ (-c) / M := (Int.le_ediv_iff_mul_le hM).mpr (by linarith [mul_comm M q])
  nlinarith

theorem tightenL_holds (e : Nat) (g : Lin) (ρ s : Env)
    (hd : ((2 ^ e : Nat) : Int) ∣ s 8 - s 9) (h : g.eval ρ s ≤ 0) : (tightenL e g).eval ρ s ≤ 0 := by
  unfold tightenL
  split
  · rename_i hc
    obtain ⟨_, hlv, hsv⟩ := hc
    have hM : (0 : Int) < ((2 ^ e : Nat) : Int) := by exact_mod_cast Nat.pos_pow_of_pos e (by norm_num)
    simp only [Checker.Lin.eval, Checker.dot, add_zero] at h ⊢
    rw [hlv] at h
    simp only [Checker.dot, add_zero] at h
    rcases hsv with hsv | hsv
    · rw [hsv, dle_sv s] at h ⊢
      exact round_le _ _ _ hM hd h
    · rw [hsv, dge_sv s] at h ⊢
      exact round_le _ _ _ hM (by simpa using hd.neg_right) h
  · exact h

theorem tightenS_holds (e : Nat) (g : Lin) (ρ s : Env)
    (hd : ((2 ^ e : Nat) : Int) ∣ s 8 + s 9) (h : g.eval ρ s ≤ 0) : (tightenS e g).eval ρ s ≤ 0 := by
  unfold tightenS
  split
  · rename_i hc
    obtain ⟨_, hlv, hsv⟩ := hc
    have hM : (0 : Int) < ((2 ^ e : Nat) : Int) := by exact_mod_cast Nat.pos_pow_of_pos e (by norm_num)
    simp only [Checker.Lin.eval, Checker.dot, add_zero] at h ⊢
    rw [hlv] at h
    simp only [Checker.dot, add_zero] at h
    rcases hsv with hsv | hsv
    · rw [hsv, sumC_sv 1 s] at h ⊢
      exact round_le _ _ _ hM (by simpa using hd) h
    · rw [hsv, sumC_sv (-1) s] at h ⊢
      exact round_le _ _ _ hM (by simpa using hd.neg_right) h
  · exact h

theorem condFactsM_sound (k : FKind) (a b : Nat) (ha : a < U) (hb : b < U) (f : Flags)
    (hf : match k with | .none => True | .add => f = flagsAdd a b | .sub => f = flagsSub a b)
    (cc : Nat) (hcc : cc < 16) (taken : Bool) (h : condHolds cc f = taken) (ρ s : Env)
    (h8 : s 8 = a) (h9 : s 9 = b) (e : Nat) (hd : ((2 ^ e : Nat) : Int) ∣ s 8 - s 9)
    (es : Nat) (hds : ((2 ^ es : Nat) : Int) ∣ s 8 + s 9) :
    ∃ D ∈ condFactsM k cc taken e es, holds D ρ s := by
  obtain ⟨D, hD, hh⟩ := condFacts_sound k a b ha hb f hf cc hcc taken h ρ s h8 h9
  refine ⟨D.map (fun g => tightenS es (tightenL e g)), List.mem_map.mpr ⟨D, hD, rfl⟩, fun g hg => ?_⟩
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  exact tightenS_holds es _ ρ s hds (tightenL_holds e g0 ρ s hd (hh g0 hg0))

theorem congSv_sound (cs : List Cong) (s : Env) (hC : CongHolds cs s) (e : Nat) :
    ∀ (l : List Int) (v : Nat) (t : Int) (g : Env), (∀ i, g i = s (v + i)) →
      congSv cs e v l = some t → ((2 ^ e : Nat) : Int) ∣ Checker.dot l g - t
  | [], v, t, g, _, h => by simp [congSv] at h; subst h; simp [Checker.dot]
  | k :: l, v, t, g, hg, h => by
    simp only [congSv] at h
    cases hb : congSv cs e (v + 1) l with
    | none => rw [hb] at h; simp at h
    | some b =>
      rw [hb] at h
      simp only at h
      split at h
      · rename_i hk
        simp only [Option.some.injEq] at h
        subst h
        have ih := congSv_sound cs s hC e l (v + 1) b (fun i => g (i + 1))
          (fun i => by show g (i + 1) = _; rw [hg]; congr 1; omega) hb
        have hv := congOf_dvd cs s hC v
        have hk' : ((2 ^ e : Nat) : Int) ∣ k * ((2 ^ (congOf cs v).1 : Nat) : Int) :=
          Int.dvd_of_emod_eq_zero hk
        have h1 : ((2 ^ e : Nat) : Int) ∣ k * (s v - (congOf cs v).2) := by
          obtain ⟨q, hq⟩ := hv
          rw [hq, ← mul_assoc]
          exact Dvd.dvd.mul_right hk' q
        have hg0 : g 0 = s v := by rw [hg, Nat.add_zero]
        simp only [Checker.dot, hg0]
        have : k * s v + Checker.dot l (fun i => g (i + 1)) - (k * ↑(congOf cs v).2 + b) =
            k * (s v - (congOf cs v).2) + (Checker.dot l (fun i => g (i + 1)) - b) := by ring
        rw [this]
        exact dvd_add h1 ih
      · simp at h

theorem congPE_sound (cs : List Cong) (s : Env) (hC : CongHolds cs s) (e r : Nat) (P : PExp)
    (h : congPE cs e r P = true) :
    P.eval s % ((2 ^ e : Nat) : Int) = (r : Int) % ((2 ^ e : Nat) : Int) := by
  unfold congPE at h
  cases ht : congSv cs e 0 P.sv with
  | none => rw [ht] at h; simp at h
  | some t =>
    rw [ht] at h
    simp only [decide_eq_true_eq] at h
    have hd := congSv_sound cs s hC e P.sv 0 t s (fun i => by simp) ht
    simp only [Checker.PExp.eval]
    rw [← h]
    exact (Int.ModEq.symm ((Int.modEq_iff_dvd).mpr (by
      rw [show Checker.dot P.sv s + P.c - (t + P.c) = Checker.dot P.sv s - t by ring]
      exact hd)))

theorem slotsOk_spec {L : DFun} (h : slotsOk L = true) :
    (∀ k ∈ L.slots, 0 < k ∧ k % 4 = 0 ∧ k < 1048576) ∧
    (∀ o ∈ L.spOff, ∀ d, o = some d → -1048576 ≤ d ∧ d ≤ 1048576) := by
  simp only [slotsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.2, fun o ho d hd => ?_⟩
  have := h.2 o ho
  rw [hd] at this
  simpa using this

theorem spAt_bound {f : BFun} {L : DFun} (h : slotsOk L = true) (a : Nat) (d : Int)
    (hd : spAt f L a = some d) : -1048576 ≤ d ∧ d ≤ 1048576 := by
  simp only [spAt] at hd
  cases hk : find f.nodes a with
  | none => simp [hk] at hd
  | some k =>
    cases ho : L.spOff[k]? with
    | none => simp [hk, ho] at hd
    | some o =>
      simp [hk, ho] at hd
      exact (slotsOk_spec h).2 o (List.mem_of_getElem? ho) d hd

theorem congAt_wf (f : BFun) (L : DFun) (hw : ∀ l ∈ L.cong, ∀ x ∈ l, wfCong L.slots.length x = true)
    (a : Nat) : ∀ x ∈ congAt f L a, wfCong L.slots.length x = true := by
  intro x hx
  simp only [congAt] at hx
  cases hk : find f.nodes a with
  | none => simp [hk] at hx
  | some k =>
    cases hl : L.cong[k]? with
    | none => simp [hk, hl] at hx
    | some l =>
      simp [hk, hl] at hx
      exact hw l (List.mem_of_getElem? hl) x hx

theorem wfCong_var {S : Nat} {x : Cong} (h : wfCong S x = true) : x.1 < 10 ∨ 20 ≤ x.1 ∧ x.1 < 20 + S := by
  simp only [wfCong, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem congHolds_congr (S : Nat) (cs : List Cong) (hw : ∀ x ∈ cs, wfCong S x = true) (s s' : Env)
    (hs : ∀ v, (v < 10 ∨ 20 ≤ v ∧ v < 20 + S) → s v = s' v) (h : CongHolds cs s') : CongHolds cs s := by
  intro x hx
  rw [hs x.1 (wfCong_var (hw x hx))]
  exact h x hx

theorem congOk_spec {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun} {a : Nat} {i : Insn}
    (h : congOk mul abi c f L a = true) (hdec : decode mul c a = some i)
    {p : Option Nat × Nat × List Nat} (hp : p ∈ transJ f.jumps i a) {n : Nat} (hn : p.1 = some n)
    {m : Int} (hm : m ∈ mcases (effect abi c a)) {x : Cong} (hx : x ∈ congAt f L n) :
    shlCong abi c a x = true ∨ congPE (congAt f L a) x.2.1 x.2.2
      (postS (effect abi c a) (stackEffect abi c a) L.frame (spAt f L a) L.slots m x.1) = true := by
  unfold congOk at h
  rw [hdec] at h
  simp only [List.all_eq_true] at h
  have := h p hp
  rw [hn] at this
  simp only [List.all_eq_true] at this
  rcases Bool.or_eq_true_iff.mp (this x hx) with h1 | h1
  · exact Or.inl h1
  · rw [List.all_eq_true] at h1
    exact Or.inr (h1 m hm)

/-- A congruence given by a shift holds after it. -/
theorem shlCong_sound {abi : Bool} {c : Code} {a : Nat} {x : Cong} (h : shlCong abi c a x = true)
    {σ σ' : MState} (he : EffOk (effect abi c a) σ σ') (fa fb SP0 : Nat) (slots : List Nat) :
    envOf σ' fa fb SP0 slots x.1 % ((2 ^ x.2.1 : Nat) : Int) =
      (x.2.2 : Int) % ((2 ^ x.2.1 : Nat) : Int) := by
  unfold shlCong at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, hm⟩ := h
  split at hm
  · rename_i q src k hf
    have hk := of_decide_eq_true hm
    obtain ⟨he1, _, hk3⟩ := hk
    have hv := he.2.2.1 x.1 hlt _ hf _ rfl
    simp only [envOf, if_pos hlt]
    rw [hv]
    have hU : U = 2 ^ 32 := rfl
    have hd : 2 ^ x.2.1 ∣ U := by rw [hU]; exact Nat.pow_dvd_pow 2 (by omega)
    have h0 : (srcVal σ.r src * 2 ^ k) % U % 2 ^ x.2.1 = 0 := by
      rw [Nat.mod_mod_of_dvd _ hd]
      exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 he1) _)
    rw [← Int.natCast_mod, ← Int.natCast_mod, h0, hk3]
  · cases hm

theorem invAt_wf (f : BFun) (L : DFun) (hw : ∀ l ∈ L.inv, ∀ g ∈ l, wfLin L.slots.length g = true)
    (a : Nat) : ∀ g ∈ invAt f L a, wfLin L.slots.length g = true := by
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

theorem invsAt_wf (f : BFun) (L : DFun) (hw : ∀ l ∈ L.inv, ∀ g ∈ l, wfLin L.slots.length g = true)
    (hwa : ∀ l ∈ L.alt, ∀ I ∈ l, ∀ g ∈ I, wfLin L.slots.length g = true)
    (a : Nat) : ∀ I ∈ invsAt f L a, ∀ g ∈ I, wfLin L.slots.length g = true := by
  intro I hI g hg
  simp only [invsAt, List.mem_cons] at hI
  rcases hI with rfl | hI
  · exact invAt_wf f L hw a g hg
  · cases hk : find f.nodes a with
    | none => simp [hk] at hI
    | some k =>
      cases hl : L.alt[k]? with
      | none => simp [hk, hl] at hI
      | some l =>
        simp only [hk] at hI
        simp [hl] at hI
        exact hwa l (List.mem_of_getElem? hl) I hI g hg

theorem tgtInv_mem (f : BFun) (L : DFun) (n t : Nat) : tgtInv f L n t ∈ invsAt f L n := by
  unfold tgtInv
  cases h : (invsAt f L n)[t]? with
  | none => simp [invsAt]
  | some J => exact List.mem_of_getElem? h

theorem wfSv_nil (S : Nat) : wfSv S [] = true := by
  simp [wfSv]

theorem potAt_wf (S : Nat) (lc : LoopCert) (hw : ∀ p ∈ lc.pot, wfSv S p.sv = true) (x : Option Nat) :
    wfSv S (potAt lc x).sv = true := by
  cases x with
  | none => simp [potAt, pconst, wfSv_nil]
  | some a =>
    simp only [potAt]
    cases hk : find lc.body a with
    | none => simp [pconst, wfSv_nil]
    | some k =>
      cases hp : lc.pot[k]? with
      | none => simp [hp, pconst, wfSv_nil]
      | some p => simp [hp]; exact hw p (List.mem_of_getElem? hp)

theorem nodeOk_spec {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun} {a : Nat}
    (h : nodeOk mul abi c f L a = true) :
    wfEff (effect abi c a) = true ∧ stackWf (stackEffect abi c a) = true ∧
    ∃ i, decode mul c a = some i ∧ ∀ p ∈ transJ f.jumps i a, ∀ n, p.1 = some n →
      kindOk (kindAt f L a) (effect abi c a).fl (kindAt f L n) = true ∧
      spOk (spAt f L a) (stackEffect abi c a).sp (spAt f L n) = true := by
  simp only [nodeOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, _⟩, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · cases h3
  · rename_i i hi
    refine ⟨i, hi, fun p hp n hn => ?_⟩
    simp only [List.all_eq_true] at h3
    have := h3 p hp
    rw [hn] at this
    simpa only [Bool.and_eq_true] using this

theorem mem_indexed {α : Type} : ∀ (l : List α) (k j : Nat) (x : α), l[j]? = some x → (k + j, x) ∈ indexed k l
  | [], _, _, _, h => by simp at h
  | y :: ys, k, 0, x, h => by simp at h; subst h; simp [indexed]
  | y :: ys, k, j + 1, x, h => by
    simp only [indexed, List.mem_cons]
    right
    have := mem_indexed ys (k + 1) j x (by simpa using h)
    rwa [show k + 1 + j = k + (j + 1) by omega] at this

/-- The goals of a transition: the invariant of the successor, the descent of the potentials. -/
def tGoals (f : BFun) (L : DFun) (e : Eff) (st : StackE) (frame : Bool) (m : Int) (a : Nat)
    (next : Option Nat) (t : Nat) : List Lin :=
  (match next with
    | some n => (tgtInv f L n t).map fun g => substL g (postS e st frame (spAt f L a) L.slots m)
    | none => []) ++
  L.loops.map fun lc => goalLin (coefStep lc a next)
    (substP (potAt lc next) (postS e st frame (spAt f L a) L.slots m)) (potAt lc (some a))

theorem obs_mem (mul : Nat) (abi : Bool) (c : Code) (f : BFun) (L : DFun) (a : Nat) (i : Insn)
    (j : Nat) (next : Option Nat) (w : Nat) (calls : List Nat) (m : Int) (D : List Lin) (g : Lin)
    (di si : Nat) (I : List Lin)
    (hdec : decode mul c a = some i) (hj : (transJ f.jumps i a)[j]? = some (next, w, calls))
    (hm : m ∈ mcases (effect abi c a))
    (hD : (match i.kind with
      | .cond _ => condFactsM (kindAt f L a) (ccOf c a) (j == 0) (gExp (congAt f L a)) (gExpS (congAt f L a))
      | _ => [[]])[di]? = some D)
    (hI : (invsAt f L a)[si]? = some I)
    (hg : g ∈ tGoals f L (effect abi c a) (stackEffect abi c a) L.frame m a next (tgtIdx f L a j m di si)) :
    (D ++ wrapPrem (effect abi c a) m ++ I ++ rangesN (nVars L.slots.length), g) ∈
      obsOf mul abi c f L a := by
  unfold obsOf
  rw [hdec]
  simp only [List.mem_flatMap, List.mem_map]
  refine ⟨(0 + j, (next, w, calls)), mem_indexed _ 0 j _ hj, m, hm, (0 + di, D), ?_,
    (0 + si, I), mem_indexed _ 0 si _ hI, g, ?_, rfl⟩
  · exact mem_indexed _ 0 di _ (by simpa using hD)
  · simpa [tGoals] using hg

/-! ### The stack -/

theorem slotIdx_spec (slots : List Nat) (k : Int) (j : Nat) (h : slotIdx slots k = some j) :
    0 < k ∧ slots.getD j 0 = k.toNat ∧ j < slots.length := by
  simp only [slotIdx] at h
  split at h
  · rename_i hk
    have := find_get slots k.toNat j h
    refine ⟨hk, ?_, ?_⟩
    · simp [List.getD, this]
    · exact (List.getElem?_eq_some_iff.mp this).1
  · cases h

theorem slot_mem (slots : List Nat) (j : Nat) (hj : j < slots.length) : slots.getD j 0 ∈ slots := by
  simp [List.getD, List.getElem?_eq_getElem hj]

/-- The value of every variable of the state after the instruction, the tracked words of
    the frame included. -/
theorem postS_eval (e : Eff) (st : StackE) (frame : Bool) (h : wfEff e = true) (hw : stackWf st = true)
    (σ σ' : MState) (fa fb SP0 : Nat) (slots : List Nat) (δ : Option Int)
    (hσ : wfState σ) (hSP0 : SP0 < U) (heff : EffOk e σ σ') (hst : StackOk frame SP0 st σ σ')
    (hsp : ∀ d, δ = some d → σ.sp = aOf (SP0 + d))
    (hδ : ∀ d, δ = some d → -1048576 ≤ d ∧ d ≤ 1048576)
    (hslots : ∀ k ∈ slots, 0 < k ∧ k % 4 = 0 ∧ k < 1048576)
    (v : Nat) (hv : v < 10 ∨ 20 ≤ v ∧ v < 20 + slots.length) :
    (postS e st frame δ slots (mSel e σ.r) v).eval (envT σ σ' fa fb SP0 slots) =
      envOf σ' (postG e σ.r fa fb).1 (postG e σ.r fa fb).2 SP0 slots v := by
  obtain ⟨_, _, hmem, hload⟩ := hst
  simp only [stackWf, Bool.and_eq_true] at hw
  rcases hv with hv | hv
  · by_cases h8 : v < 8
    · simp only [postS, if_pos h8]
      cases hl : st.load with
      | none => simp only; exact postE_eval e h σ σ' fa fb SP0 slots hσ heff v hv
      | some p =>
        cases δ with
        | none => simp only; exact postE_eval e h σ σ' fa fb SP0 slots hσ heff v hv
        | some d =>
          simp only
          by_cases hp : v = p.1
          · rw [if_pos hp]
            cases hj : slotIdx slots (-(d + (p.2 : Int))) with
            | none => simp only; exact postE_eval e h σ σ' fa fb SP0 slots hσ heff v hv
            | some j =>
              simp only
              obtain ⟨hk, hkj, hjl⟩ := slotIdx_spec slots _ j hj
              have hsd := hsp d rfl
              have hpb : p.2 < 1024 := by
                have := hw.1; rw [hl] at this; exact (by simpa [stackLoadOk] using this : p.1 < 8 ∧ p.2 < 1024).2
              rw [pv_eval, envT_state σ σ' fa fb SP0 slots _ (Or.inr ⟨by omega, by omega⟩)]
              simp only [envOf, h8, if_true, slotVal]
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega⟩]
              rw [hp, hload p hl]
              congr 2
              rw [show 20 + j - 20 = j by omega, hkj, hsd]
              simp only [aOf, U] at *
              omega
          · rw [if_neg hp]; exact postE_eval e h σ σ' fa fb SP0 slots hσ heff v hv
    · have h20 : ¬ v < 20 → False := fun h' => h' (by omega)
      simp only [postS, if_neg h8, if_pos (show v < 20 by omega)]
      exact postE_eval e h σ σ' fa fb SP0 slots hσ heff v hv
  · have hj : v - 20 < slots.length := by omega
    have hkm := hslots _ (slot_mem slots (v - 20) hj)
    set k := slots.getD (v - 20) 0 with hkdef
    have hpost : envOf σ' (postG e σ.r fa fb).1 (postG e σ.r fa fb).2 SP0 slots v = slotVal σ' SP0 slots (v - 20) := by
      simp only [envOf]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hv]
    have hpre : envT σ σ' fa fb SP0 slots v = slotVal σ SP0 slots (v - 20) := by
      rw [envT_state σ σ' fa fb SP0 slots v (Or.inr hv)]
      simp only [envOf]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hv]
    have hfresh : envT σ σ' fa fb SP0 slots (v + slots.length) = slotVal σ' SP0 slots (v - 20) := by
      simp only [envT]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      congr 1; omega
    rw [hpost]
    simp only [postS, if_neg (show ¬ v < 8 by omega), if_neg (show ¬ v < 20 by omega)]
    cases hm : st.mem with
    | keep =>
      rw [hm] at hmem
      simp only [pv_eval, hpre, slotVal]
      rw [hmem]
    | storeSP imm rt =>
      rw [hm] at hmem
      have hsb : imm < 1024 ∧ rt < 8 := by
        have := hw.2; rw [hm] at this; simpa [stackMemOk] using this
      cases δ with
      | none => simp only [pv_eval, hfresh]
      | some d =>
        have hsd := hsp d rfl
        have hdb := hδ d rfl
        simp only
        by_cases hk : ((k : Nat) : Int) = -(d + (imm : Int))
        · rw [if_pos hk, pv_eval]
          rw [envT_state σ σ' fa fb SP0 slots rt (Or.inl (by omega))]
          simp only [envOf, show rt < 8 by omega, if_true, slotVal]
          rw [← hkdef]
          have : aOf ((SP0 : Int) - (k : Int)) = aOf ((σ.sp : Int) + imm) := by
            rw [hsd]; simp only [aOf, U] at *; omega
          rw [this, hmem.1]
        · rw [if_neg hk, pv_eval, hpre]
          simp only [slotVal]
          rw [← hkdef]
          rw [hmem.2]
          rw [hsd]; simp only [aOf, U] at *; omega
    | push n =>
      rw [hm] at hmem
      have hnb : n ≤ 16 := by
        have := hw.2; rw [hm] at this; simpa [stackMemOk] using this
      cases δ with
      | none => simp only [pv_eval, hfresh]
      | some d =>
        have hsd := hsp d rfl
        have hdb := hδ d rfl
        simp only
        by_cases hr : d - 4 * (n : Int) ≤ -((k : Nat) : Int) ∧ -((k : Nat) : Int) < d
        · rw [if_pos hr, pv_eval, hfresh]
        · rw [if_neg hr, pv_eval, hpre]
          simp only [slotVal]
          rw [← hkdef]
          rw [hmem]
          intro i hi
          rw [hsd]; simp only [aOf, U] at *; omega
    | other =>
      rw [hm] at hmem
      cases δ with
      | none => simp only [pv_eval, hfresh]
      | some d =>
        have hsd := hsp d rfl
        have hdb := hδ d rfl
        simp only
        by_cases hr : frame = true ∧ ((k : Nat) : Int) ≤ -d
        · rw [if_pos hr, pv_eval, hpre]
          simp only [slotVal]
          rw [← hkdef]
          symm
          congr 1
          apply hmem hr.1 (k : Int) (by omega)
          rw [hsd]; simp only [aOf, U] at *; omega
        · rw [if_neg hr, pv_eval, hfresh]

/-! ### One transition -/

/-- One transition: the invariant of the successor holds, and every potential descends by
    the coefficient of the transition in the loop's row. -/
theorem step_ok {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (hc : checkDFun mul abi c f L = true) {SP0 a j : Nat} (hSP0 : SP0 < U) {σ : MState}
    {next : Option Nat} {w : Nat}
    {calls : List Nat} (ha : a ∈ f.nodes) (hok : DOk mul c f.jumps a j σ next w calls) {fa fb : Nat}
    (hinv : Inv f L SP0 a σ fa fb) (σ' : MState) (hwf' : wfState σ') (hws' : wfStack σ')
    (heff : next ≠ none → EffOk (effect abi c a) σ σ' ∧ StackOk L.frame SP0 (stackEffect abi c a) σ σ') :
    (∀ n, next = some n →
      Inv f L SP0 n σ' (postG (effect abi c a) σ.r fa fb).1 (postG (effect abi c a) σ.r fa fb).2) ∧
    ∀ lc ∈ L.loops, coefStep lc a next +
      (potAt lc next).eval (envOf σ' (postG (effect abi c a) σ.r fa fb).1
        (postG (effect abi c a) σ.r fa fb).2 SP0 L.slots) -
      (potAt lc (some a)).eval (envOf σ fa fb SP0 L.slots) ≤ 0 := by
  obtain ⟨_, _, _, hnodes, _, _, hslok, hwinv, hwpot, hobs⟩ := checkDFun_spec hc
  obtain ⟨hσ, hs, i, hdec, hj, hcond⟩ := hok
  obtain ⟨_, _, hfa, hfb, hfl, hspa, hI, hC⟩ := hinv
  obtain ⟨hwfe, hstw, i', hdec', hkind⟩ := nodeOk_spec (hnodes a ha)
  rw [hdec] at hdec'
  cases hdec'
  set e := effect abi c a with he
  set st := stackEffect abi c a with hst
  set m := mSel e σ.r with hmdef
  set S := L.slots.length with hS
  have hm : m ∈ mcases e := mSel_mem e σ hσ hwfe
  set env := envT σ σ' fa fb SP0 L.slots with henv
  have h8 : env 8 = fa := by simp [env, envT, envOf]
  have h9 : env 9 = fb := by simp [env, envT, envOf]
  have hstate : ∀ v, (v < 10 ∨ 20 ≤ v ∧ v < 20 + S) → env v = envOf σ fa fb SP0 L.slots v :=
    fun v hv => envT_state σ σ' fa fb SP0 L.slots v hv
  have hgs : ((2 ^ gExpS (congAt f L a) : Nat) : Int) ∣ env 8 + env 9 := by
    have := gExpS_dvd _ _ hC
    rw [h8, h9]
    simpa [envOf] using this
  have hgd : ((2 ^ gExp (congAt f L a) : Nat) : Int) ∣ env 8 - env 9 := by
    have := gExp_dvd _ _ hC
    rw [h8, h9]
    simpa [envOf] using this
  obtain ⟨I, hImem, hI⟩ := hI
  obtain ⟨si, hsi⟩ := List.mem_iff_getElem?.mp hImem
  obtain ⟨D, hD, hDh⟩ : ∃ D ∈ (match i.kind with
      | .cond _ => condFactsM (kindAt f L a) (ccOf c a) (j == 0) (gExp (congAt f L a)) (gExpS (congAt f L a))
      | _ => [[]]), holds D (fun _ => 0) env := by
    cases hk : i.kind with
    | cond t =>
      simp only
      have hcc : ccOf c a < 16 := Nat.mod_lt _ (by omega)
      exact condFactsM_sound (kindAt f L a) fa fb hfa hfb σ.f
        (by revert hfl; cases kindAt f L a <;> simp [flagsAt]) (ccOf c a) hcc (j == 0)
        (hcond t hk) _ env h8 h9 _ hgd _ hgs
    | _ => exact ⟨[], by simp, by simp [holds]⟩
  obtain ⟨di, hdi⟩ := List.mem_iff_getElem?.mp hD
  have hwalt := checkDFun_alt hc
  have hprem : holds (D ++ wrapPrem e m ++ I ++ rangesN (nVars S)) (fun _ => 0) env := by
    rw [holds_append, holds_append, holds_append]
    refine ⟨⟨⟨hDh, wrapPrem_holds e σ σ' fa fb SP0 L.slots hσ hwfe _⟩, ?_⟩,
      rangesN_holds σ σ' fa fb SP0 L.slots hσ hwf' hs hws' hfa hfb _⟩
    intro g hg
    rw [lin_congr S g (invsAt_wf f L hwinv hwalt a I hImem g hg) _ (fun _ => 0) env
      (envOf σ fa fb SP0 L.slots) hstate]
    exact hI g hg
  set t := tgtIdx f L a j m di si with ht
  have hgoal : ∀ g ∈ tGoals f L e st L.frame m a next t, g.eval (fun _ => 0) env ≤ 0 := by
    intro g hg
    have hmem := obs_mem mul abi c f L a i j next w calls m D g di si I hdec hj hm hdi hsi hg
    have hin : (D ++ wrapPrem e m ++ I ++ rangesN (nVars S), g) ∈
        obligations mul abi c f L := by
      simp only [obligations, List.mem_append]
      right
      exact List.mem_flatMap.mpr ⟨a, ha, hmem⟩
    obtain ⟨p, hp⟩ := checkObs_mem _ _ hobs _ hin
    exact entails1_sound hp hprem
  have hpot_a : ∀ lc ∈ L.loops, (potAt lc (some a)).eval env = (potAt lc (some a)).eval (envOf σ fa fb SP0 L.slots) :=
    fun lc hlc => pexp_congr S _ (potAt_wf S lc (hwpot lc hlc) _) _ _ hstate
  have hslots := (slotsOk_spec hslok).1
  have hpost : next ≠ none → ∀ v, (v < 10 ∨ 20 ≤ v ∧ v < 20 + S) →
      (postS e st L.frame (spAt f L a) L.slots m v).eval env =
        envOf σ' (postG e σ.r fa fb).1 (postG e σ.r fa fb).2 SP0 L.slots v := fun hn v hv =>
    postS_eval e st L.frame hwfe hstw σ σ' fa fb SP0 L.slots (spAt f L a) hσ hSP0 (heff hn).1 (heff hn).2
      hspa (fun d hd => spAt_bound hslok a d hd) hslots v hv
  constructor
  · intro n hn
    subst hn
    have heff' := heff (by simp)
    have hk := (hkind (some n, w, calls) (List.mem_of_getElem? hj) n rfl).1
    have hspk := (hkind (some n, w, calls) (List.mem_of_getElem? hj) n rfl).2
    obtain ⟨hfl', hga, hgb⟩ := flags_post _ _ e hwfe σ σ' hσ fa fb hfa hfb hfl hk heff'.1.2.2.2
    refine ⟨hwf', hws', hga, hgb, hfl', ?_, ?_, ?_⟩
    · intro dn hdn
      obtain ⟨_, hspE, _, _⟩ := heff'.2
      rw [hdn] at hspk
      simp only [spOk] at hspk
      cases hda : spAt f L a with
      | none => rw [hda] at hspk; simp at hspk
      | some d =>
        rw [hda] at hspk
        have hsd := hspa d hda
        cases hsq : st.sp with
        | keep =>
          rw [hsq] at hspk hspE
          simp only [beq_iff_eq] at hspk
          rw [hspE, hsd, hspk]
        | add k =>
          rw [hsq] at hspk hspE
          simp only [beq_iff_eq] at hspk
          rw [hspE, hsd, hspk]
          simp only [aOf, U] at *
          omega
        | any => rw [hsq] at hspk; simp at hspk
    · refine ⟨tgtInv f L n t, tgtInv_mem f L n t, fun g hg => ?_⟩
      have := hgoal (substL g (postS e st L.frame (spAt f L a) L.slots m)) (by
        simp only [tGoals]; exact List.mem_append_left _ (List.mem_map.mpr ⟨g, hg, rfl⟩))
      rw [substL_eval] at this
      rwa [lin_congr S g (invsAt_wf f L hwinv hwalt n _ (tgtInv_mem f L n t) g hg) (fun _ => 0)
        (fun _ => 0) _ _ (hpost (by simp))] at this
    · intro x hx
      obtain ⟨_, hwc, hcok⟩ := checkDFun_cong hc
      have hwx := congAt_wf f L hwc n x hx
      rcases congOk_spec (hcok a ha) hdec (List.mem_of_getElem? hj) rfl hm hx with hsh | hpe
      · exact shlCong_sound hsh (heff (by simp)).1 _ _ SP0 L.slots
      have hCa : CongHolds (congAt f L a) env :=
        congHolds_congr S _ (congAt_wf f L hwc a) env _ hstate hC
      have h1 := congPE_sound _ env hCa x.2.1 x.2.2 _ hpe
      rwa [hpost (by simp) x.1 (wfCong_var hwx)] at h1
  · intro lc hlc
    have := hgoal _ (by simp only [tGoals]; exact List.mem_append_right _ (List.mem_map.mpr ⟨lc, hlc, rfl⟩))
    rw [goalLin_eval, substP_eval, hpot_a lc hlc] at this
    cases next with
    | none => simpa [potAt, pconst_eval] using this
    | some n =>
      rwa [pexp_congr S _ (potAt_wf S lc (hwpot lc hlc) _) _ _ (hpost (by simp))] at this

/-! ### Runs -/

theorem potAt_none (lc : LoopCert) (s : Env) : (potAt lc none).eval s = 0 := by
  simp [potAt, pconst_eval]

/-- Along a chain, the instructions are in the function, the invariants hold, and the sum
    of the coefficients of every loop row is at most the potential at the start. -/
theorem chain_ok {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (hc : checkDFun mul abi c f L = true) {SP0 : Nat} (hSP0 : SP0 < U) :
    ∀ (t : List DStep) (x : DStep) (a fa fb : Nat), DChain abi L.frame c SP0 (some a) (x :: t) →
      a ∈ f.nodes →
      (∀ y ∈ x :: t, DOk mul c f.jumps y.st.a y.j y.σ y.st.next y.st.w y.st.calls) →
      Inv f L SP0 a x.σ fa fb →
      (∀ y ∈ x :: t, y.st.a ∈ f.nodes) ∧
      ∀ lc ∈ L.loops, ((x :: t).map fun y => coefStep lc y.st.a y.st.next).sum ≤
        (potAt lc (some a)).eval (envOf x.σ fa fb SP0 L.slots)
  | [], x, a, fa, fb, hch, ha, hok, hinv => by
    obtain ⟨hxa, _, hrest⟩ := hch
    cases hn : x.st.next with
    | some _ => rw [hn] at hrest; simp [DChain] at hrest
    | none =>
      have hok' := hok x (by simp)
      rw [hxa, hn] at hok'
      obtain ⟨_, hpot⟩ := step_ok hc hSP0 ha hok' hinv x.σ hinv.1 hinv.2.1 (fun h => absurd rfl h)
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
      have hok' := hok x (by simp)
      rw [hxa, hn] at hok'
      have hwfy : wfState y.σ := (hok y (by simp)).1
      have hwsy : wfStack y.σ := (hok y (by simp)).2.1
      have hE := heff y (by simp)
      obtain ⟨hinvn, hpot⟩ := step_ok hc hSP0 ha hok' hinv y.σ hwfy hwsy (fun _ => hE)
      have hnn : n ∈ f.nodes := by
        obtain ⟨hcl, _⟩ := (checkDFun_spec hc)
        obtain ⟨_, hcl2⟩ := closed_spec mul c f.jumps f.entry f.nodes hcl
        obtain ⟨i, hi, _, hsucc⟩ := hcl2 a ha
        obtain ⟨_, _, i', hi', hj, _⟩ := hok'
        rw [hi] at hi'; cases hi'
        exact hsucc _ (List.mem_of_getElem? hj) n rfl
      obtain ⟨hnodes, hsum⟩ := chain_ok hc hSP0 t y n _ _ hrest hnn
        (fun z hz => hok z (by simp [hz])) (hinvn n rfl)
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
    (hc : checkDFun mul abi c f L = true) (s : List DStep)
    (hch : DChain abi L.frame c (headSp s) (some f.entry) s)
    (hok : ∀ y ∈ s, DOk mul c f.jumps y.st.a y.j y.σ y.st.next y.st.w y.st.calls) :
    ∀ lc ∈ L.loops, (s.map fun y => coefPair (loopRow f lc).coef y.st.a y.st.next).sum ≤ (loopRow f lc).rhs := by
  obtain ⟨hcl, hnd, _, _, hke, hspe, hslok, hwinv, hwpot, hobs⟩ := checkDFun_spec hc
  cases s with
  | nil => simp [DChain] at hch
  | cons x t =>
    simp only [headSp] at hch
    have hwf : wfState x.σ := (hok x (by simp)).1
    have hws : wfStack x.σ := (hok x (by simp)).2.1
    have hSP0 : x.σ.sp < U := hws.1
    set S := L.slots.length
    have he : f.entry ∈ f.nodes := (closed_spec mul c f.jumps f.entry f.nodes hcl).1
    have env0 := rangesN_holds x.σ x.σ 0 0 x.σ.sp L.slots hwf hwf hws hws (by simp [U]) (by simp [U]) (fun _ => 0)
    have hstate : ∀ v, (v < 10 ∨ 20 ≤ v ∧ v < 20 + S) →
        envT x.σ x.σ 0 0 x.σ.sp L.slots v = envOf x.σ 0 0 x.σ.sp L.slots v :=
      fun v hv => envT_state x.σ x.σ 0 0 x.σ.sp L.slots v hv
    have hinv : Inv f L x.σ.sp f.entry x.σ 0 0 := by
      refine ⟨hwf, hws, by simp [U], by simp [U], by rw [hke]; trivial, ?_,
        ⟨invAt f L f.entry, by simp [invsAt], fun g hg => ?_⟩, ?_⟩
      · intro d hd
        rcases hspe with hspe | hspe <;> rw [hspe] at hd
        · cases hd
          simp only [aOf, U] at *
          omega
        · cases hd
      · have hin : (rangesN (nVars S), g) ∈ obligations mul abi c f L := by
          simp only [obligations, List.mem_append, List.mem_map]
          left; left; exact ⟨g, hg, rfl⟩
        obtain ⟨p, hp⟩ := checkObs_mem _ _ hobs _ hin
        have := entails1_sound hp env0
        rwa [lin_congr S g (invAt_wf f L hwinv _ g hg) _ (fun _ => 0) _ _ hstate] at this
      · intro x hx
        rw [(checkDFun_cong hc).1] at hx
        cases hx
    obtain ⟨hnodes, hsum⟩ := chain_ok hc hSP0 t x f.entry 0 0 hch he hok hinv
    intro lc hlc
    have hin : (rangesN (nVars S), goalLin (-(rowRhs f lc)) (potAt lc (some f.entry)) (pconst 0)) ∈
        obligations mul abi c f L := by
      simp only [obligations, List.mem_append, List.mem_map]
      left; right; exact ⟨lc, hlc, rfl⟩
    obtain ⟨p, hp⟩ := checkObs_mem _ _ hobs _ hin
    have h0 := entails1_sound hp env0
    rw [goalLin_eval, pconst_eval, pexp_congr S _ (potAt_wf S lc (hwpot lc hlc) _) _ _ hstate] at h0
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

theorem dchain_mchain (abi frame : Bool) (c : Code) (SP0 : Nat) :
    ∀ (s : List DStep) (o : Option Nat), DChain abi frame c SP0 o s → MChain o (s.map (·.st))
  | [], none, _ => by simp [MChain]
  | [], some _, h => by simp [DChain] at h
  | _ :: _, none, h => by simp [DChain] at h
  | x :: t, some a, ⟨hxa, _, hrest⟩ => ⟨hxa, dchain_mchain abi frame c SP0 t x.st.next hrest⟩

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

/-! ### Jumps through a table: every step of a data run follows `transJ`

At a listed jump, the data semantics goes to the address computed from the register
(`DOkM`). Nothing enters the window but from the instruction before (`interiorOk`), so a
run at the jump has executed the whole window from its `CMP` (`back_walk`); the branch not
taken bounds the compared register; the evaluation of the window (`wrun`) agrees with the
run (`wrun_sound`), so the address is one that `jumpOk` found among the targets. -/

theorem checkDFun_jumps {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (h : checkDFun mul abi c f L = true) :
    (∀ t ∈ f.jumps, jumpOkF abi mul c f L t = true) ∧ interiorOk mul c f = true := by
  simp only [checkDFun, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.2, h.2⟩

theorem getElem?_append_some {α : Type} : ∀ (l l' : List α) (j : Nat) (x : α),
    l[j]? = some x → (l ++ l')[j]? = some x
  | [], _, _, _, h => by simp at h
  | y :: ys, l', 0, x, h => by simpa using h
  | y :: ys, l', j + 1, x, h => by
    simpa using getElem?_append_some ys l' j x (by simpa using h)

theorem dchain_head {abi frame : Bool} {c : Code} {SP0 : Nat} {e : Nat} :
    ∀ (s : List DStep) (x : DStep), DChain abi frame c SP0 (some e) s → s[0]? = some x → x.st.a = e
  | [], _, _, hx => by simp at hx
  | y :: t, x, h, hx => by
    simp at hx; subst hx; exact h.1

theorem dchain_get {abi frame : Bool} {c : Code} {SP0 : Nat} :
    ∀ (s : List DStep) (o : Option Nat), DChain abi frame c SP0 o s →
      ∀ k x y, s[k]? = some x → s[k + 1]? = some y →
        x.st.next = some y.st.a ∧ EffOk (effect abi c x.st.a) x.σ y.σ
  | [], _, _, _, _, _, hx, _ => by simp at hx
  | _ :: _, none, h, _, _, _, _, _ => by simp [DChain] at h
  | x' :: t, some a, h, k, x, y, hx, hy => by
    obtain ⟨hxa, heff, hrest⟩ := h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      cases t with
      | nil => simp at hy
      | cons y' t' =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hy
        subst hy
        refine ⟨?_, ?_⟩
        · cases hn : x'.st.next with
          | none => rw [hn] at hrest; simp [DChain] at hrest
          | some b => rw [hn] at hrest; exact congrArg some hrest.1.symm
        · rw [hxa]; exact (heff y' (by simp)).1
    | succ k => exact dchain_get t x'.st.next hrest k x y (by simpa using hx) (by simpa using hy)

/-- Partial registers that agree with a state. -/
def Agree (P : Nat → Option Nat) (σ : MState) : Prop := ∀ i v, P i = some v → σ.r i = v

theorem srcP_sound {P : Nat → Option Nat} {σ : MState} (h : Agree P σ) :
    ∀ (s : Src) (v : Nat), srcP P s = some v → srcVal σ.r s = v
  | .reg i, v, hv => h i v hv
  | .imm k, v, hv => by simpa [srcP, srcVal] using hv

theorem valP_sound {P : Nat → Option Nat} {σ : MState} (h : Agree P σ) :
    ∀ (x : Val) (v : Nat), valP P x = some v → valOf σ.r x = some v
  | .add a b, v, hv => by
    simp only [valP, Option.bind_eq_some, Option.map_eq_some'] at hv
    obtain ⟨x, hx, y, hy, rfl⟩ := hv
    simp [valOf, srcP_sound h a x hx, srcP_sound h b y hy]
  | .sub a b, v, hv => by
    simp only [valP, Option.bind_eq_some, Option.map_eq_some'] at hv
    obtain ⟨x, hx, y, hy, rfl⟩ := hv
    simp [valOf, srcP_sound h a x hx, srcP_sound h b y hy]
  | .shl a k, v, hv => by
    simp only [valP, Option.map_eq_some'] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    simp [valOf, srcP_sound h a x hx]
  | .any, v, hv => by simp [valP] at hv

theorem xres_mono {P : Nat → Option Nat} {σ : MState} (h : Agree P σ) (c : Code) (a : Nat) :
    ∀ (op : XOp) (v : Nat), xres c a P op = some v → xres c a (fun i => some (σ.r i)) op = some v
  | .addPc d, v, hv => by
    simp only [xres, Option.map_eq_some'] at hv ⊢
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨σ.r d, rfl, by rw [h d x hx]⟩
  | .adr d k, v, hv => by simpa [xres] using hv
  | .ldImm sz d n off, v, hv => by
    simp only [xres, Option.bind_eq_some] at hv ⊢
    obtain ⟨x, hx, hl⟩ := hv
    exact ⟨σ.r n, rfl, by rw [h n x hx]; exact hl⟩
  | .ldReg sz d n m, v, hv => by
    simp only [xres, Option.bind_eq_some] at hv ⊢
    obtain ⟨x, hx, y, hy, hl⟩ := hv
    exact ⟨σ.r n, rfl, σ.r m, rfl, by rw [h n x hx, h m y hy]; exact hl⟩

theorem wstep_sound {abi : Bool} {c : Code} {a : Nat} {P : Nat → Option Nat} {σ σ' : MState}
    (hP : Agree P σ) (he : EffOk (effect abi c a) σ σ') (hx : XOk c a σ σ') :
    Agree (wstep abi c a P) σ' := by
  intro i v hv
  simp only [wstep] at hv
  by_cases hi : i < 8
  · rw [if_pos hi] at hv
    cases hf : (effect abi c a).dst.find? (fun p => p.1 == i) with
    | none =>
      rw [hf] at hv
      rw [he.2.1 i hi hf]
      exact hP i v hv
    | some p =>
      rw [hf] at hv
      cases hxo : xop c a with
      | none =>
        rw [hxo] at hv
        exact he.2.2.1 i hi p hf v (valP_sound hP p.2 v hv)
      | some op =>
        rw [hxo] at hv
        simp only at hv
        by_cases hd : op.dst = i
        · rw [if_pos hd] at hv
          rw [← hd]
          exact hx.1 op hxo v (xres_mono hP c a op v hv)
        · rw [if_neg hd] at hv
          exact he.2.2.1 i hi p hf v (valP_sound hP p.2 v hv)
  · rw [if_neg hi] at hv
    cases hv

theorem wrun_sound {abi frame : Bool} {c : Code} {SP0 : Nat} {o : Option Nat} (s : List DStep)
    (hch : DChain abi frame c SP0 o s) (hX : XChain c s) :
    ∀ (n a b : Nat) (P : Nat → Option Nat) (x : DStep), s[b]? = some x → Agree P x.σ →
      (∀ i ≤ n, ∃ y, s[b + i]? = some y ∧ y.st.a = a + 2 * i) →
      ∃ y, s[b + n]? = some y ∧ Agree (wrun abi c n a P) y.σ := by
  intro n
  induction n with
  | zero => intro a b P x hx hP _; exact ⟨x, by simpa using hx, hP⟩
  | succ n ih =>
    intro a b P x hx hP haddr
    have hxa : x.st.a = a := by
      obtain ⟨y0, hy0, hy0a⟩ := haddr 0 (by omega)
      rw [Nat.add_zero, hx] at hy0
      cases hy0
      simpa using hy0a
    obtain ⟨y1, hy1, hy1a⟩ := haddr 1 (by omega)
    obtain ⟨_, he⟩ := dchain_get s o hch b x y1 hx hy1
    have hxx := hX b x y1 hx hy1
    rw [hxa] at he hxx
    have hP1 := wstep_sound hP he hxx
    obtain ⟨y, hy, hag⟩ := ih (a + 2) (b + 1) (wstep abi c a P) y1 hy1 hP1 (fun i hi => by
      obtain ⟨z, hz, hza⟩ := haddr (i + 1) (by omega)
      exact ⟨z, by rw [show b + 1 + i = b + (i + 1) by omega]; exact hz, by rw [hza]; ring⟩)
    exact ⟨y, by rw [show b + (n + 1) = b + 1 + n by omega]; exact hy, by simpa [wrun] using hag⟩

theorem hi_false (v n : Nat) (hv : v < U) (hn : n < U) (h : condHolds 8 (flagsSub v n) = false) :
    v ≤ n := by
  simp only [condHolds, flagsSub, U, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Bool.not_eq_false', decide_eq_true_eq] at h hv hn
  omega

/-- A step whose address is a node and that follows a transition of the function. -/
def Good (mul : Nat) (c : Code) (f : BFun) (x : DStep) : Prop :=
  x.st.a ∈ f.nodes ∧ ∃ j, DOk mul c f.jumps x.st.a j x.σ x.st.next x.st.w x.st.calls

theorem good_medge {mul : Nat} {c : Code} {f : BFun} {x : DStep} (h : Good mul c f x) :
    (x.st.a, x.st.next, x.st.w, x.st.calls) ∈ medges mul c f.jumps f.nodes := by
  obtain ⟨ha, j, _, _, i, hi, hj, _⟩ := h
  exact mem_medges mul c f.jumps x.st.a i _ hi (List.mem_of_getElem? hj) f.nodes ha

/-- The address of the window `i` steps before the jump: from the jump down to `wbeg`, then
    the branch, then the `CMP`. -/
def wpath (c : Code) (t : JT) (i : Nat) : Nat :=
  if i ≤ (t.pos - wbeg c t) / 2 then t.pos - 2 * i
  else if i = (t.pos - wbeg c t) / 2 + 1 then t.start + 2 else t.start

theorem wbeg_cases (c : Code) (t : JT) :
    (lsForm c t = true ∧ wbeg c t = t.start + 6) ∨ (lsForm c t = false ∧ wbeg c t = t.start + 4) := by
  unfold wbeg
  cases h : lsForm c t <;> simp

theorem wpath_mem (c : Code) (t : JT) (hwb : wbeg c t ≤ t.pos) (hev : (t.pos - t.start) % 2 = 0)
    (i : Nat) (hi : i < (t.pos - wbeg c t) / 2 + 2) : wpath c t i ∈ interior c t := by
  have hw := wbeg_cases c t
  unfold wpath interior
  by_cases h1 : i ≤ (t.pos - wbeg c t) / 2
  · rw [if_pos h1]
    simp only [List.mem_cons, List.mem_map, List.mem_range]
    right
    exact ⟨(t.pos - wbeg c t) / 2 - i, by omega, by omega⟩
  · rw [if_neg h1, if_pos (by omega)]
    simp

theorem wpath_pred (c : Code) (t : JT) (hwb : wbeg c t ≤ t.pos) (hev : (t.pos - t.start) % 2 = 0)
    (i : Nat) (hi : i < (t.pos - wbeg c t) / 2 + 2) : wpred c t (wpath c t i) = wpath c t (i + 1) := by
  rcases wbeg_cases c t with ⟨hl, hb⟩ | ⟨hl, hb⟩
  · rw [hb] at hwb hi
    simp only [wpath, wpred, hl, hb, true_and]
    split_ifs <;> omega
  · rw [hb] at hwb hi
    simp only [wpath, wpred, hl, hb, Bool.false_eq_true, false_and, if_false]
    split_ifs <;> omega

theorem interiorOk_spec {mul : Nat} {c : Code} {f : BFun} (hint : interiorOk mul c f = true)
    (t : JT) (ht : t ∈ f.jumps) (hix : t.ix = none) :
    f.entry ∉ interior c t ∧ jumpTr f.jumps (t.start + 2) = [] ∧
      ∀ m ∈ medges mul c f.jumps f.nodes, ∀ p, m.2.1 = some p → p ∈ interior c t → m.1 = wpred c t p := by
  unfold interiorOk at hint
  rw [List.all_eq_true] at hint
  have htt := hint t ht
  rw [if_neg (by simp [hix])] at htt
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at htt
  obtain ⟨⟨hent, hj2⟩, hm⟩ := htt
  refine ⟨fun h => ?_, by simpa using hj2, fun m hm' p hp hin => ?_⟩
  · have : (interior c t).contains f.entry = true := List.contains_iff_mem.mpr h
    rw [this] at hent; cases hent
  · have := hm m hm'
    rw [hp] at this
    have hcont : (interior c t).contains p = true := List.contains_iff_mem.mpr hin
    simp only [hcont, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    exact this

/-- A window without `CMP`: nothing enters it but from the address before, and the entry
    is not in it. -/
theorem interiorR_spec {mul : Nat} {c : Code} {f : BFun} (hint : interiorOk mul c f = true)
    (t : JT) (ht : t ∈ f.jumps) (hix : t.ix.isSome = true) :
    f.entry ∉ interiorR t ∧
      ∀ m ∈ medges mul c f.jumps f.nodes, ∀ p, m.2.1 = some p → p ∈ interiorR t → m.1 = p - 2 := by
  unfold interiorOk at hint
  rw [List.all_eq_true] at hint
  have htt := hint t ht
  rw [if_pos hix, Bool.and_eq_true, List.all_eq_true] at htt
  obtain ⟨hent, hm⟩ := htt
  refine ⟨fun h => ?_, fun m hm' p hp hin => ?_⟩
  · have : (interiorR t).contains f.entry = true := List.contains_iff_mem.mpr h
    rw [this] at hent; cases hent
  · have := hm m hm'
    rw [hp] at this
    have hcont : (interiorR t).contains p = true := List.contains_iff_mem.mpr hin
    simp only [hcont, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    exact this

theorem interiorR_mem (t : JT) (i : Nat) (hle : t.start ≤ t.pos) (hev : (t.pos - t.start) % 2 = 0)
    (hi : i + 1 ≤ (t.pos - t.start) / 2) : t.pos - 2 * i ∈ interiorR t := by
  have hlt : (t.pos - t.start) / 2 - 1 - i < (t.pos - t.start) / 2 := by omega
  have heq : t.start + 2 + 2 * ((t.pos - t.start) / 2 - 1 - i) = t.pos - 2 * i := by omega
  unfold interiorR
  exact List.mem_map.mpr ⟨_, List.mem_range.mpr hlt, heq⟩

/-- The steps before a jump whose window has no `CMP`: the addresses `t.pos - 2i` back to
    `t.start`. -/
theorem back_walkR {mul : Nat} {abi frame : Bool} {c : Code} {SP0 : Nat} {f : BFun} (s : List DStep)
    (hch : DChain abi frame c SP0 (some f.entry) s) (t : JT) (ht : t ∈ f.jumps)
    (hint : interiorOk mul c f = true) (hix : t.ix.isSome = true) (hle : t.start ≤ t.pos)
    (hev : (t.pos - t.start) % 2 = 0)
    (k : Nat) (x : DStep) (hx : s[k]? = some x)
    (hxa : x.st.a = t.pos) (hgood : ∀ k' < k, ∀ y, s[k']? = some y → Good mul c f y) :
    ∀ i ≤ (t.pos - t.start) / 2, i ≤ k ∧ ∃ y, s[k - i]? = some y ∧ y.st.a = t.pos - 2 * i := by
  obtain ⟨hent, hm⟩ := interiorR_spec hint t ht hix
  intro i
  induction i with
  | zero => intro _; exact ⟨by omega, x, by simpa using hx, by rw [hxa]; omega⟩
  | succ i ih =>
    intro hi
    obtain ⟨hik, y, hy, hya⟩ := ih (by omega)
    have hin : y.st.a ∈ interiorR t := by
      rw [hya]
      exact interiorR_mem t i hle hev hi
    have hk0 : k - i ≠ 0 := by
      intro h0
      rw [h0] at hy
      have := dchain_head s y hch hy
      rw [this] at hin
      exact hent hin
    obtain ⟨z, hz⟩ : ∃ z, s[k - i - 1]? = some z := by
      have : k - i - 1 < s.length := by
        have := (List.getElem?_eq_some_iff.mp hy).1
        omega
      exact ⟨_, List.getElem?_eq_getElem this⟩
    have hz1 : s[k - i - 1 + 1]? = some y := by rw [show k - i - 1 + 1 = k - i by omega]; exact hy
    obtain ⟨hzn, _⟩ := dchain_get s _ hch (k - i - 1) z y hz hz1
    have hg := hgood (k - i - 1) (by omega) z hz
    have hza := hm _ (good_medge hg) _ hzn hin
    refine ⟨by omega, z, by rw [show k - (i + 1) = k - i - 1 by omega]; exact hz, ?_⟩
    simp only at hza
    rw [hza, hya]
    omega

theorem rngB_spec {c : Code} {a : Nat} {P : Nat → Option Nat} {d b : Nat}
    (h : rngB c a P = some (d, b)) : ∃ q ∈ rngOps c a, srcP P q.2 = some b ∧ q.1 = d := by
  unfold rngB at h
  obtain ⟨q, hq, hqv⟩ := List.exists_of_findSome?_eq_some h
  simp only [Option.map_eq_some'] at hqv
  obtain ⟨b', hb', hbe⟩ := hqv
  simp only [Prod.mk.injEq] at hbe
  obtain ⟨h1, h2⟩ := hbe
  subst h2
  exact ⟨q, hq, hb', h1⟩

/-- The jump case of a window without `CMP`: the registers known before the bounding
    instruction, its bound, then every value up to it. -/
theorem jump_good_rng {mul : Nat} {abi frame : Bool} {c : Code} {SP0 : Nat} {f : BFun}
    (hint : interiorOk mul c f = true) (s : List DStep)
    (hch : DChain abi frame c SP0 (some f.entry) s) (hX : XChain c s)
    (k : Nat) (x : DStep) (hx : s[k]? = some x) (t : JT) (ht : t ∈ f.jumps) (p : Nat)
    (hp : t.ix = some p) (add : Bool) (m : Nat) (hpw : pcWrite c t.pos = some (add, m))
    (hxa : x.st.a = t.pos) (hok : jumpRng abi c t = true)
    (hgood : ∀ k' < k, ∀ y, s[k']? = some y → Good mul c f y) :
    pcDestV t.pos add (x.σ.r m) ∈ t.tgts := by
  unfold jumpRng at hok
  rw [hp, hpw] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨hsp, hpp⟩, hev1⟩, hev⟩, hm⟩ := hok
  cases hrb : rngB c p (wpre abi c t p) with
  | none => rw [hrb] at hm; cases hm
  | some db =>
    obtain ⟨d, b⟩ := db
    rw [hrb] at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hm
    obtain ⟨⟨_, _⟩, hall⟩ := hm
    have hbw := back_walkR s hch t ht hint (by simp [hp]) (by omega) hev k x hx hxa hgood
    obtain ⟨_, y0, hy0, _⟩ := hbw ((t.pos - t.start) / 2) le_rfl
    obtain ⟨yp, hyp, hagp⟩ := wrun_sound s hch hX ((p - t.start) / 2) t.start
      (k - (t.pos - t.start) / 2) (fun _ => none) y0 hy0 (fun _ _ h => by cases h) (fun j hj => by
        obtain ⟨_, z, hz, hza⟩ := hbw ((t.pos - t.start) / 2 - j) (by omega)
        refine ⟨z, by rw [show k - (t.pos - t.start) / 2 + j = k - ((t.pos - t.start) / 2 - j) by omega]; exact hz, ?_⟩
        rw [hza]; omega)
    have hypa : yp.st.a = p := by
      obtain ⟨_, z, hz, hza⟩ := hbw ((t.pos - t.start) / 2 - (p - t.start) / 2) (by omega)
      rw [show k - ((t.pos - t.start) / 2 - (p - t.start) / 2) = k - (t.pos - t.start) / 2 + (p - t.start) / 2 by omega,
        hyp] at hz
      cases hz
      rw [hza]; omega
    obtain ⟨_, y1, hy1, _⟩ := hbw ((t.pos - t.start) / 2 - (p - t.start) / 2 - 1) (by omega)
    have hy1' : s[k - (t.pos - t.start) / 2 + (p - t.start) / 2 + 1]? = some y1 := by
      rw [show k - (t.pos - t.start) / 2 + (p - t.start) / 2 + 1 =
        k - ((t.pos - t.start) / 2 - (p - t.start) / 2 - 1) by omega]
      exact hy1
    obtain ⟨_, he⟩ := dchain_get s _ hch _ yp y1 hyp hy1'
    have hxo := hX _ yp y1 hyp hy1'
    rw [hypa] at he hxo
    have hag1 := wstep_sound hagp he hxo
    obtain ⟨q0, hq0, hsrc, hd0⟩ := rngB_spec hrb
    have hle : y1.σ.r d ≤ b := by
      have h1 := hxo.2 q0 hq0
      rw [hd0, srcP_sound hagp q0.2 b hsrc] at h1
      exact h1
    have hagx : Agree (setR (wstep abi c p (wpre abi c t p)) d (y1.σ.r d)) y1.σ := by
      intro i v hv
      unfold setR at hv
      by_cases hid : i = d
      · rw [if_pos hid] at hv; cases hv; rw [hid]
      · rw [if_neg hid] at hv; exact hag1 i v hv
    obtain ⟨y, hy, hagy⟩ := wrun_sound s hch hX ((t.pos - (p + 2)) / 2) (p + 2)
      (k - (t.pos - t.start) / 2 + (p - t.start) / 2 + 1) _ y1 hy1' hagx (fun j hj => by
        obtain ⟨_, z, hz, hza⟩ := hbw ((t.pos - t.start) / 2 - (p - t.start) / 2 - 1 - j) (by omega)
        refine ⟨z, ?_, ?_⟩
        · rw [show k - (t.pos - t.start) / 2 + (p - t.start) / 2 + 1 + j =
            k - ((t.pos - t.start) / 2 - (p - t.start) / 2 - 1 - j) by omega]
          exact hz
        · rw [hza]; omega)
    rw [show k - (t.pos - t.start) / 2 + (p - t.start) / 2 + 1 + (t.pos - (p + 2)) / 2 = k by omega,
      hx] at hy
    cases hy
    have hv := hall (y1.σ.r d) (by omega)
    split at hv
    · rename_i v hvv
      rw [hagy m v hvv]
      exact of_decide_eq_true hv
    · cases hv

theorem dchain_getS {abi frame : Bool} {c : Code} {SP0 : Nat} :
    ∀ (s : List DStep) (o : Option Nat), DChain abi frame c SP0 o s →
      ∀ k x y, s[k]? = some x → s[k + 1]? = some y →
        x.st.next = some y.st.a ∧ EffOk (effect abi c x.st.a) x.σ y.σ ∧
          StackOk frame SP0 (stackEffect abi c x.st.a) x.σ y.σ
  | [], _, _, _, _, _, hx, _ => by simp at hx
  | _ :: _, none, h, _, _, _, _, _ => by simp [DChain] at h
  | x' :: t, some a, h, k, x, y, hx, hy => by
    obtain ⟨hxa, heff, hrest⟩ := h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      cases t with
      | nil => simp at hy
      | cons y' t' =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hy
        subst hy
        refine ⟨?_, ?_, ?_⟩
        · cases hn : x'.st.next with
          | none => rw [hn] at hrest; simp [DChain] at hrest
          | some b => rw [hn] at hrest; exact congrArg some hrest.1.symm
        · rw [hxa]; exact (heff y' (by simp)).1
        · rw [hxa]; exact (heff y' (by simp)).2
    | succ k => exact dchain_getS t x'.st.next hrest k x y (by simpa using hx) (by simpa using hy)

/-- The invariant holds at the entry of a function, from the ranges alone. -/
theorem inv_entry {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (hc : checkDFun mul abi c f L = true) (σ : MState) (hwf : wfState σ) (hws : wfStack σ) :
    Inv f L σ.sp f.entry σ 0 0 := by
  obtain ⟨_, _, _, _, hke, hspe, _, hwinv, _, hobs⟩ := checkDFun_spec hc
  set S := L.slots.length
  have env0 := rangesN_holds σ σ 0 0 σ.sp L.slots hwf hwf hws hws (by simp [U]) (by simp [U]) (fun _ => 0)
  have hstate : ∀ v, (v < 10 ∨ 20 ≤ v ∧ v < 20 + S) →
      envT σ σ 0 0 σ.sp L.slots v = envOf σ 0 0 σ.sp L.slots v :=
    fun v hv => envT_state σ σ 0 0 σ.sp L.slots v hv
  refine ⟨hwf, hws, by simp [U], by simp [U], by rw [hke]; trivial, ?_,
    ⟨invAt f L f.entry, by simp [invsAt], fun g hg => ?_⟩, ?_⟩
  · intro d hd
    rcases hspe with hspe | hspe <;> rw [hspe] at hd
    · cases hd
      have := hws.1
      simp only [aOf, U] at *
      omega
    · cases hd
  · have hin : (rangesN (nVars S), g) ∈ obligations mul abi c f L := by
      simp only [obligations, List.mem_append, List.mem_map]
      left; left; exact ⟨g, hg, rfl⟩
    obtain ⟨p, hp⟩ := checkObs_mem _ _ hobs _ hin
    have := entails1_sound hp env0
    rwa [lin_congr S g (invAt_wf f L hwinv _ g hg) _ (fun _ => 0) _ _ hstate] at this
  · intro x hx
    rw [(checkDFun_cong hc).1] at hx
    cases hx

/-- The invariant holds at every step of a data run whose earlier steps follow the
    transitions of the function. -/
theorem inv_prefix {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (hc : checkDFun mul abi c f L = true) (s : List DStep)
    (hch : DChain abi L.frame c (headSp s) (some f.entry) s)
    (hwf : ∀ x ∈ s, wfState x.σ ∧ wfStack x.σ) :
    ∀ (k : Nat) (y : DStep), s[k]? = some y → (∀ k' < k, ∀ z, s[k']? = some z → Good mul c f z) →
      ∃ fa fb, Inv f L (headSp s) y.st.a y.σ fa fb := by
  intro k
  induction k with
  | zero =>
    intro y hy _
    cases s with
    | nil => simp at hy
    | cons x t =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      have hw := hwf x (by simp)
      refine ⟨0, 0, ?_⟩
      rw [hch.1]
      exact inv_entry hc x.σ hw.1 hw.2
  | succ k ih =>
    intro y hy hg
    obtain ⟨z, hz⟩ : ∃ z, s[k]? = some z := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨fa, fb, hiz⟩ := ih z hz (fun k' hk' => hg k' (by omega))
    obtain ⟨hzn, j, hdok⟩ := hg k (by omega) z hz
    obtain ⟨hnext, heff, hstk⟩ := dchain_getS s _ hch k z y hz hy
    have hSP0 : headSp s < U := by
      cases s with
      | nil => simp at hy
      | cons x t => exact (hwf x (by simp)).2.1
    have hwy := hwf y (List.mem_of_getElem? hy)
    exact ⟨_, _, (step_ok hc hSP0 hzn hdok hiz y.σ hwy.1 hwy.2 (fun _ => ⟨heff, hstk⟩)).1 y.st.a hnext⟩

theorem ubOf_sound {g : Lin} {d : Nat} {u : Int} (h : ubOf g d = some u) (s : Env)
    (hg : g.eval (fun _ => 0) s ≤ 0) : s d ≤ u := by
  unfold ubOf at h
  split at h
  · rename_i hz
    cases h
    have h1 := Checker.dot_isZero hz s
    rw [Checker.dot_vadd, Checker.dot_vsmul, Checker.dot_unit] at h1
    simp only [Lin.eval, Checker.dot_zero_env] at hg
    linarith
  · cases h

theorem lbOf_sound {g : Lin} {d : Nat} {l : Int} (h : lbOf g d = some l) (s : Env)
    (hg : g.eval (fun _ => 0) s ≤ 0) : l ≤ s d := by
  unfold lbOf at h
  split at h
  · rename_i hz
    cases h
    have h1 := Checker.dot_isZero hz s
    rw [Checker.dot_vadd, Checker.dot_unit] at h1
    simp only [Lin.eval, Checker.dot_zero_env] at hg
    linarith
  · cases h

theorem invBound_spec {f : BFun} {L : DFun} {p d lo hi : Nat} (h : invBound f L p d lo hi = true)
    (I : List Lin) (hI : I ∈ invsAt f L p) (s : Env) (hs : holds I (fun _ => 0) s) :
    s d ≤ hi ∧ (lo ≠ 0 → (lo : Int) ≤ s d) := by
  unfold invBound at h
  rw [List.all_eq_true] at h
  have hI' := h I hI
  rw [Bool.and_eq_true] at hI'
  obtain ⟨hu, hl⟩ := hI'
  obtain ⟨g, hg, hgu⟩ := List.any_eq_true.mp hu
  refine ⟨?_, ?_⟩
  · split at hgu
    · rename_i u hu'
      have h1 := ubOf_sound hu' s (hs g hg)
      have h2 : u ≤ hi := of_decide_eq_true hgu
      omega
    · cases hgu
  · intro hlo
    rcases Bool.or_eq_true_iff.mp hl with h0 | hl
    · exact absurd (by simpa using h0) hlo
    · obtain ⟨g', hg', hgl⟩ := List.any_eq_true.mp hl
      split at hgl
      · rename_i l hl'
        have h1 := lbOf_sound hl' s (hs g' hg')
        have h2 : (lo : Int) ≤ l := of_decide_eq_true hgl
        omega
      · cases hgl

/-- The jump case of a window bounded by the invariant: the registers known before `p`, the
    invariant and the congruence at `p` on the run (`hinv`), then every value allowed. -/
theorem jump_good_inv {mul : Nat} {abi frame : Bool} {c : Code} {SP0 : Nat} {f : BFun} {L : DFun}
    (hint : interiorOk mul c f = true) (s : List DStep)
    (hch : DChain abi frame c SP0 (some f.entry) s) (hX : XChain c s)
    (k : Nat) (x : DStep) (hx : s[k]? = some x) (t : JT) (ht : t ∈ f.jumps) (p : Nat)
    (hp : t.ix = some p) (add : Bool) (m : Nat) (hpw : pcWrite c t.pos = some (add, m))
    (hxa : x.st.a = t.pos) (hok : jumpInv abi c f L t = true)
    (hgood : ∀ k' < k, ∀ y, s[k']? = some y → Good mul c f y)
    (hinv : ∀ k' ≤ k, ∀ y, s[k']? = some y → ∃ fa fb, Inv f L SP0 y.st.a y.σ fa fb) :
    pcDestV t.pos add (x.σ.r m) ∈ t.tgts := by
  unfold jumpInv at hok
  rw [hp, hpw] at hok
  cases hvr : t.vr with
  | none => rw [hvr] at hok; cases hok
  | some db =>
    obtain ⟨d, lo, b⟩ := db
    rw [hvr] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      List.mem_range] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨hsp, hpp⟩, hev1⟩, hev⟩, hd8⟩, _⟩, hib⟩, hall⟩ := hok
    have hbw := back_walkR s hch t ht hint (by simp [hp]) (by omega) hev k x hx hxa hgood
    obtain ⟨hk0, y0, hy0, _⟩ := hbw ((t.pos - t.start) / 2) le_rfl
    obtain ⟨yp, hyp, hagp⟩ := wrun_sound s hch hX ((p - t.start) / 2) t.start
      (k - (t.pos - t.start) / 2) (fun _ => none) y0 hy0 (fun _ _ h => by cases h) (fun j hj => by
        obtain ⟨_, z, hz, hza⟩ := hbw ((t.pos - t.start) / 2 - j) (by omega)
        refine ⟨z, by rw [show k - (t.pos - t.start) / 2 + j = k - ((t.pos - t.start) / 2 - j) by omega]; exact hz, ?_⟩
        rw [hza]; omega)
    have hypa : yp.st.a = p := by
      obtain ⟨_, z, hz, hza⟩ := hbw ((t.pos - t.start) / 2 - (p - t.start) / 2) (by omega)
      rw [show k - ((t.pos - t.start) / 2 - (p - t.start) / 2) = k - (t.pos - t.start) / 2 + (p - t.start) / 2 by omega,
        hyp] at hz
      cases hz
      rw [hza]; omega
    obtain ⟨fa, fb, hI⟩ := hinv _ (by omega) yp hyp
    rw [hypa] at hI
    obtain ⟨_, _, _, _, _, _, ⟨I, hIm, hIh⟩, hC⟩ := hI
    have hbd := invBound_spec hib I hIm _ hIh
    simp only [envOf, if_pos hd8] at hbd
    have hle : yp.σ.r d ≤ b := by omega
    have hlo : ¬ yp.σ.r d < lo := by
      intro hlt
      by_cases h0 : lo = 0
      · omega
      · have := hbd.2 h0; omega
    have hcg : congFits f L p d (yp.σ.r d) = true := by
      have := congOf_sound _ _ hC d
      simp only [envOf, if_pos hd8] at this
      unfold congFits
      exact decide_eq_true this
    have hagx : Agree (setR (wpre abi c t p) d (yp.σ.r d)) yp.σ := by
      intro i v hv
      unfold setR at hv
      by_cases hid : i = d
      · rw [if_pos hid] at hv; cases hv; rw [hid]
      · rw [if_neg hid] at hv; exact hagp i v hv
    obtain ⟨y, hy, hagy⟩ := wrun_sound s hch hX ((t.pos - p) / 2) p
      (k - (t.pos - t.start) / 2 + (p - t.start) / 2) _ yp hyp hagx (fun j hj => by
        obtain ⟨_, z, hz, hza⟩ := hbw ((t.pos - t.start) / 2 - (p - t.start) / 2 - j) (by omega)
        refine ⟨z, ?_, ?_⟩
        · rw [show k - (t.pos - t.start) / 2 + (p - t.start) / 2 + j =
            k - ((t.pos - t.start) / 2 - (p - t.start) / 2 - j) by omega]
          exact hz
        · rw [hza]; omega)
    rw [show k - (t.pos - t.start) / 2 + (p - t.start) / 2 + (t.pos - p) / 2 = k by omega,
      hx] at hy
    cases hy
    have hv := hall (yp.σ.r d) (by omega)
    rw [hcg, decide_eq_false hlo] at hv
    simp only [Bool.not_true, Bool.false_or] at hv
    split at hv
    · rename_i v hvv
      rw [hagy m v hvv]
      exact of_decide_eq_true hv
    · cases hv

/-- The steps before a jump at `t.pos` are those of its window, along its path. -/
theorem back_walk {mul : Nat} {abi frame : Bool} {c : Code} {SP0 : Nat} {f : BFun} (s : List DStep)
    (hch : DChain abi frame c SP0 (some f.entry) s) (t : JT) (ht : t ∈ f.jumps)
    (hint : interiorOk mul c f = true) (hix : t.ix = none) (hwb : wbeg c t ≤ t.pos) (hev : (t.pos - t.start) % 2 = 0)
    (k : Nat) (x : DStep) (hx : s[k]? = some x)
    (hxa : x.st.a = t.pos) (hgood : ∀ k' < k, ∀ y, s[k']? = some y → Good mul c f y) :
    ∀ i ≤ (t.pos - wbeg c t) / 2 + 2, i ≤ k ∧ ∃ y, s[k - i]? = some y ∧ y.st.a = wpath c t i := by
  obtain ⟨hent, _, hm⟩ := interiorOk_spec hint t ht hix
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨by omega, x, by simpa using hx, by rw [hxa]; unfold wpath; rw [if_pos (by omega)]; omega⟩
  | succ i ih =>
    intro hi
    obtain ⟨hik, y, hy, hya⟩ := ih (by omega)
    have hin : y.st.a ∈ interior c t := by rw [hya]; exact wpath_mem c t hwb hev i (by omega)
    have hk0 : k - i ≠ 0 := by
      intro h0
      rw [h0] at hy
      have := dchain_head s y hch hy
      rw [this] at hin
      exact hent hin
    obtain ⟨z, hz⟩ : ∃ z, s[k - i - 1]? = some z := by
      have : k - i - 1 < s.length := by
        have := (List.getElem?_eq_some_iff.mp hy).1
        omega
      exact ⟨_, List.getElem?_eq_getElem this⟩
    have hz1 : s[k - i - 1 + 1]? = some y := by rw [show k - i - 1 + 1 = k - i by omega]; exact hy
    obtain ⟨hzn, _⟩ := dchain_get s _ hch (k - i - 1) z y hz hz1
    have hg := hgood (k - i - 1) (by omega) z hz
    have hza := hm _ (good_medge hg) _ hzn hin
    refine ⟨by omega, z, by rw [show k - (i + 1) = k - i - 1 by omega]; exact hz, ?_⟩
    simp only at hza
    rw [hza, hya]
    exact wpath_pred c t hwb hev i (by omega)

theorem jumpTr_some {J : List JT} {a : Nat} (h : jumpTr J a ≠ []) :
    ∃ t ∈ J, t.pos = a ∧ jumpTr J a = t.tgts.map fun q => (some q, 3, []) := by
  unfold jumpTr at h ⊢
  cases hf : J.find? (fun t => t.pos == a) with
  | none => rw [hf] at h; simp at h
  | some t =>
    exact ⟨t, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, by simp⟩

theorem ls_true (v n : Nat) (hv : v < U) (hn : n < U) (h : condHolds 9 (flagsSub v n) = true) :
    v ≤ n := by
  simp only [condHolds, flagsSub, U, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h hv hn
  omega

/-- The jump case: the address computed by the run is a target of the jump. -/
theorem jump_good {mul : Nat} {abi frame : Bool} {c : Code} {SP0 : Nat} {f : BFun} {L : DFun}
    (hc : checkDFun mul abi c f L = true) (s : List DStep)
    (hch : DChain abi frame c SP0 (some f.entry) s) (hX : XChain c s)
    (k : Nat) (x : DStep) (hx : s[k]? = some x) (ha : x.st.a ∈ f.nodes) (i : Insn)
    (hi : decode mul c x.st.a = some i) (hstop : i.kind = .stop) (add : Bool) (m : Nat)
    (hpw : pcWrite c x.st.a = some (add, m))
    (hgood : ∀ k' < k, ∀ y, s[k']? = some y → Good mul c f y)
    (hinv : ∀ k' ≤ k, ∀ y, s[k']? = some y → ∃ fa fb, Inv f L SP0 y.st.a y.σ fa fb) :
    ∃ t ∈ f.jumps, t.pos = x.st.a ∧ pcDestV x.st.a add (x.σ.r m) ∈ t.tgts ∧
      jumpTr f.jumps x.st.a = t.tgts.map fun q => (some q, 3, []) := by
  obtain ⟨hcl, _⟩ := checkDFun_spec hc
  obtain ⟨hjk, hint⟩ := checkDFun_jumps hc
  obtain ⟨_, hcl2⟩ := closed_spec mul c f.jumps f.entry f.nodes hcl
  obtain ⟨i', hi', hns, _⟩ := hcl2 _ ha
  rw [hi] at hi'; cases hi'
  have hjt : jumpTr f.jumps x.st.a ≠ [] := by
    rcases hns with h | h
    · exact absurd hstop h
    · exact h
  obtain ⟨t, ht, htp, hjtr⟩ := jumpTr_some hjt
  refine ⟨t, ht, htp, ?_, hjtr⟩
  by_cases hix : t.ix.isSome
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hix
    have hok := hjk t ht
    unfold jumpOkF at hok
    rw [if_pos hix] at hok
    rw [← htp] at hpw ⊢
    by_cases hvr : t.vr.isSome
    · rw [if_pos hvr] at hok
      exact jump_good_inv hint s hch hX k x hx t ht p hp add m hpw htp.symm hok hgood hinv
    · rw [if_neg hvr] at hok
      exact jump_good_rng hint s hch hX k x hx t ht p hp add m hpw htp.symm hok hgood
  have hixn : t.ix = none := by simpa using hix
  obtain ⟨_, hj2, _⟩ := interiorOk_spec hint t ht hixn
  have hok := hjk t ht
  unfold jumpOkF at hok
  rw [if_neg hix] at hok
  unfold jumpOk at hok
  rw [← htp] at hpw
  rw [hpw] at hok
  split at hok
  · rename_i r n _ tb _ _ _ _ he hd hpw'
    cases hpw'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq,
      List.all_eq_true, List.mem_range] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨hr, hn⟩, hform⟩, hebr⟩, hdec⟩, hwb⟩, hev⟩, hall⟩ := hok
    set M := (t.pos - wbeg c t) / 2 with hM
    have hbw := back_walk s hch t ht hint hixn hwb hev k x hx (by rw [htp]) hgood
    have hw := wbeg_cases c t
    obtain ⟨hk0, y0, hy0, hy0a⟩ := hbw (M + 2) (le_refl _)
    obtain ⟨_, y1, hy1, hy1a⟩ := hbw (M + 1) (by omega)
    obtain ⟨_, y2, hy2, hy2a⟩ := hbw M (by omega)
    have i01 : s[k - (M + 2) + 1]? = some y1 := by rw [show k - (M + 2) + 1 = k - (M + 1) by omega]; exact hy1
    have i12 : s[k - (M + 1) + 1]? = some y2 := by rw [show k - (M + 1) + 1 = k - M by omega]; exact hy2
    obtain ⟨_, he0⟩ := dchain_get s _ hch (k - (M + 2)) y0 y1 hy0 i01
    obtain ⟨hn12, he1⟩ := dchain_get s _ hch (k - (M + 1)) y1 y2 hy1 i12
    have hst : y0.st.a = t.start := by rw [hy0a]; unfold wpath; rw [if_neg (by omega), if_neg (by omega)]
    have hb : y1.st.a = t.start + 2 := by rw [hy1a]; unfold wpath; rw [if_neg (by omega), if_pos rfl]
    have hc4 : y2.st.a = wbeg c t := by rw [hy2a]; unfold wpath; rw [if_pos (le_refl _)]; omega
    rw [hst, he] at he0
    rw [hb, hebr] at he1
    -- the flags of the CMP, the branch: not taken (`BHI`) or taken (`BLS`)
    have hfl : y1.σ.f = flagsSub (y0.σ.r r) n := by simpa [flagsOfE, srcVal] using he0.2.2.2
    have hr01 : y1.σ.r r = y0.σ.r r := he0.2.1 r hr (by simp)
    have hr12 : y2.σ.r r = y1.σ.r r := he1.2.1 r hr (by simp)
    have hg1 := hgood (k - (M + 1)) (by omega) y1 hy1
    obtain ⟨_, j1, hw1, _, i1, hi1, hj1, hcond1⟩ := hg1
    rw [hb, hdec] at hi1; cases hi1
    have hch1 := hcond1 tb rfl
    rw [hb] at hch1
    have hv0 : y0.σ.r r < U := by rw [← hr01]; exact hw1 r hr
    rw [hfl] at hch1
    have hle' : y0.σ.r r ≤ n := by
      rcases hw with ⟨hl, hwb6⟩ | ⟨hl, hwb4⟩
      · rw [if_pos hl] at hform
        have hcc : ccOf c (t.start + 2) = 9 := by simpa [lsForm] using hl
        rw [hcc] at hch1
        have hj10 : j1 = 0 := by
          rw [hb] at hj1
          simp only [transJ, hj2, trans, List.append_nil] at hj1
          rcases j1 with _ | _ | j1
          · rfl
          · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
              Prod.mk.injEq] at hj1
            rw [hn12, hc4, hwb6] at hj1
            have := Option.some.inj hj1.1
            omega
          · simp at hj1
        rw [hj10] at hch1
        exact ls_true _ _ hv0 hn (by simpa using hch1)
      · rw [if_neg (by rw [hl]; simp)] at hform
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hform
        obtain ⟨hcc, htb⟩ := hform
        rw [hcc] at hch1
        have hj1ne : j1 ≠ 0 := by
          intro h0; subst h0
          simp only [transJ, trans] at hj1
          simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hj1
          rw [hn12, hc4, hwb4] at hj1
          exact htb (Option.some.inj hj1.1)
        have hjf : (j1 == 0) = false := by simp [hj1ne]
        rw [hjf] at hch1
        exact hi_false _ _ hv0 hn hch1
    -- the evaluation of the window
    have hag : Agree (fun i => if i = r then some (y2.σ.r r) else none) y2.σ := by
      intro i v hv
      by_cases h : i = r
      · subst h; simp at hv; exact hv
      · simp [h] at hv
    obtain ⟨y, hy, hagy⟩ := wrun_sound s hch hX M (wbeg c t) (k - M)
      _ y2 hy2 hag (fun j hj => by
        obtain ⟨_, z, hz, hza⟩ := hbw (M - j) (by omega)
        refine ⟨z, by rw [show k - M + j = k - (M - j) by omega]; exact hz, ?_⟩
        rw [hza]; unfold wpath; rw [if_pos (by omega)]
        rcases hw with ⟨_, hb'⟩ | ⟨_, hb'⟩ <;> omega)
    rw [show k - M + M = k by omega, hx] at hy
    cases hy
    have hv := hall (y2.σ.r r) (by rw [hr12, hr01]; omega)
    split at hv
    · rename_i v hvv
      rw [hagy m v hvv]
      rw [← htp]
      exact of_decide_eq_true hv
    · cases hv
  · cases hok

/-- Every step of a data run of a certified function is a step along `transJ`. -/
theorem steps_good {mul : Nat} {abi : Bool} {c : Code} {f : BFun} {L : DFun}
    (hc : checkDFun mul abi c f L = true) (s : List DStep)
    (hch : DChain abi L.frame c (headSp s) (some f.entry) s) (hX : XChain c s)
    (hok : ∀ x ∈ s, DOkM mul c x.st.a x.j x.σ x.st.next x.st.w x.st.calls) :
    ∀ (k : Nat) (x : DStep), s[k]? = some x → Good mul c f x := by
  obtain ⟨hcl, _⟩ := checkDFun_spec hc
  obtain ⟨hent, hcl2⟩ := closed_spec mul c f.jumps f.entry f.nodes hcl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx
    have ha : x.st.a ∈ f.nodes := by
      cases k with
      | zero => rw [dchain_head s x hch hx]; exact hent
      | succ k =>
        obtain ⟨z, hz⟩ : ∃ z, s[k]? = some z := by
          have := (List.getElem?_eq_some_iff.mp hx).1
          exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨hzn, _⟩ := dchain_get s _ hch k z x hz hx
        obtain ⟨hza, j, _, _, i, hi, hj, _⟩ := ih k (by omega) z hz
        obtain ⟨i', hi', _, hsucc⟩ := hcl2 _ hza
        rw [hi] at hi'; cases hi'
        exact hsucc _ (List.mem_of_getElem? hj) _ hzn
    refine ⟨ha, ?_⟩
    obtain ⟨hw, hws, i, hi, hcase⟩ := hok x (List.mem_of_getElem? hx)
    rcases hcase with ⟨hj, hcond⟩ | ⟨hstop, add, m, hpw, hnext, hw3, hcalls⟩
    · exact ⟨x.j, hw, hws, i, hi, getElem?_append_some _ _ _ _ hj, hcond⟩
    · obtain ⟨t, _, _, hmem, hjtr⟩ := jump_good hc s hch hX k x hx ha i hi hstop add m hpw
        (fun k' hk' y hy => ih k' hk' y hy)
        (fun k' hk' y hy => inv_prefix hc s hch (fun z hz => ⟨(hok z hz).1, (hok z hz).2.1⟩) k' y hy
          (fun k'' hk'' z hz => ih k'' (by omega) z hz))
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hmem
      have htr : trans i x.st.a = [] := by simp [trans, hstop]
      refine ⟨q, hw, hws, i, hi, ?_, fun tt htt => by rw [hstop] at htt; cases htt⟩
      rw [transJ, htr, List.nil_append, hjtr, hnext, hw3, hcalls]
      simp [hq]

/-- The run with the transitions of `transJ` chosen at each step. -/
theorem reindex {mul : Nat} {c : Code} {f : BFun} (s : List DStep)
    (h : ∀ x ∈ s, Good mul c f x) :
    ∃ s' : List DStep, s'.map (·.st) = s.map (·.st) ∧ s'.map (·.σ) = s.map (·.σ) ∧
      ∀ y ∈ s', DOk mul c f.jumps y.st.a y.j y.σ y.st.next y.st.w y.st.calls := by
  induction s with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons x t ih =>
    obtain ⟨t', h1, h2, h3⟩ := ih (fun y hy => h y (by simp [hy]))
    obtain ⟨_, j, hj⟩ := h x (by simp)
    refine ⟨⟨x.st, j, x.σ⟩ :: t', by simp [h1], by simp [h2], ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hj
    · exact h3 y hy

theorem dchain_congr (abi frame : Bool) (c : Code) (SP0 : Nat) :
    ∀ (s s' : List DStep) (o : Option Nat), s'.map (·.st) = s.map (·.st) → s'.map (·.σ) = s.map (·.σ) →
      DChain abi frame c SP0 o s → DChain abi frame c SP0 o s'
  | [], [], _, _, _, h => h
  | [], _ :: _, _, h1, _, _ => by simp at h1
  | _ :: _, [], _, h1, _, _ => by simp at h1
  | x :: t, x' :: t', o, h1, h2, h => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2
    cases o with
    | none => simp [DChain] at h
    | some a =>
      obtain ⟨hxa, heff, hrest⟩ := h
      refine ⟨by rw [h1.1]; exact hxa, fun y hy => ?_, ?_⟩
      · cases t' with
        | nil => simp at hy
        | cons z t'' =>
          cases t with
          | nil => simp at h1
          | cons w t3 =>
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
            subst hy
            simp only [List.map_cons, List.cons.injEq] at h2
            have := heff w (by simp)
            rw [h2.1, h2.2.1]
            exact this
      · rw [h1.1]
        exact dchain_congr abi frame c SP0 t t' _ h1.2 h2.2 hrest

theorem headSp_congr (s s' : List DStep) (h : s'.map (·.σ) = s.map (·.σ)) : headSp s' = headSp s := by
  cases s with
  | nil => cases s' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x t => cases s' with
    | nil => simp at h
    | cons y t' => simp only [List.map_cons, List.cons.injEq] at h; simp [headSp, h.1]

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
    obtain ⟨f, L, s, hdf, hch, hX, hsteps, htr, htot⟩ := h
    obtain ⟨hfn, hc, hentry⟩ := dfAt_spec hD hdf
    obtain ⟨_, _, hrows, _⟩ := checkDFun_spec hc
    have hch' : DChain abi L.frame c (headSp s) (some f.entry) s := by rw [hentry]; exact hch
    have hgood := steps_good hc s hch' hX (fun x hx => (hsteps x hx).1)
    obtain ⟨s', h1, h2, hok'⟩ := reindex s (fun x hx => by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
      exact hgood k x hk)
    have hch2 : DChain abi L.frame c (headSp s') (some f.entry) s' := by
      rw [headSp_congr s s' h2]; exact dchain_congr abi L.frame c _ s s' _ h1 h2 hch'
    refine ⟨f, s.map (·.st), hfn, dchain_mchain abi L.frame c _ s _ hch, ?_, ?_, ?_⟩
    · intro st hst
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hst
      have hst' : x.st ∈ s'.map (·.st) := by rw [h1]; exact List.mem_map_of_mem _ hx
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hst'
      obtain ⟨_, _, i, hi, hj, _⟩ := hok' y hy
      rw [hyx] at hi hj
      exact ⟨step_of hi (List.mem_of_getElem? hj), callsWith_mono _ _ (ih) _ _ (hsteps x hx).2⟩
    · intro r hr
      rw [hrows] at hr
      rw [List.map_map]
      rcases List.mem_append.mp hr with hr | hr
      · exact htr r hr
      · obtain ⟨lc, hlc, rfl⟩ := List.mem_map.mp hr
        have := chain_rows hc s' hch2 hok' lc hlc
        have hmap : (s.map fun x => coefPair (loopRow f lc).coef x.st.a x.st.next) =
            (s'.map fun x => coefPair (loopRow f lc).coef x.st.a x.st.next) := by
          have e1 : (s.map fun x => coefPair (loopRow f lc).coef x.st.a x.st.next) =
              ((s.map (·.st)).map fun st => coefPair (loopRow f lc).coef st.a st.next) := by
            rw [List.map_map]; rfl
          have e2 : (s'.map fun x => coefPair (loopRow f lc).coef x.st.a x.st.next) =
              ((s'.map (·.st)).map fun st => coefPair (loopRow f lc).coef st.a st.next) := by
            rw [List.map_map]; rfl
          rw [e1, e2, h1]
        simpa [Function.comp_def, hmap] using this
    · rw [htot, List.map_map]; rfl

/-- **Soundness on machine code, loop bounds included**: if `checkBinary` and `checkData`
    accept, every run of the data semantics of the function at entry `e` (the `i`-th of
    the program) costs at most its certified bound. Only the rows left in `trusted` are
    assumed. -/
theorem data_sound (mul : Nat) (abi : Bool) (c : Code) (fs : List BFun) (Cs : List Cert)
    (Ls : List DFun) (h : checkBinary mul c fs Cs true = true) (hD : checkData mul abi c fs Ls = true)
    (d e i : Nat) (tot : Int) (hrun : DRun mul abi c fs Ls d e tot)
    (hfind : find (fs.map (·.entry)) e = some i) :
    tot ≤ ((Cs.map Cert.bound).getD i 0 : Nat) :=
  binary_sound mul c fs Cs true h d e i tot (drun_mrun hD d e tot hrun) hfind

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


def exDFun : DFun := ⟨exKinds, exInv, [exLoop], [], exProofs, [some 0, none, none, none, none, none], [], false, [], [], []⟩

def exFunD0 : BFun := ⟨0x100, [0x100, 0x102, 0x104, 0x106, 0x108, 0x10A], [], []⟩

/-- The function with the row of its certified loop (generated, `loopRow`). -/
def exFunD : BFun := { exFunD0 with rows := [loopRow exFunD0 exLoop] }

theorem exData_checks : checkData 32 false exCode [exFunD] [exDFun] = true := by decide

theorem exBinaryD_checks : checkBinary 32 exCode [exFunD] [exCert] true = true := by decide

/-- A bound of 9 iterations is refused. -/
theorem exData_tight :
    checkData 32 false exCode [{ exFunD0 with rows := [loopRow exFunD0 { exLoop with bound := 9 }] }]
      [⟨exKinds, exInv, [{ exLoop with bound := 9 }], [], exProofs, [some 0, none, none, none, none, none], [], false, [], [], []⟩] = false := by decide

/-- Every run of the data semantics of the example costs at most 68 cycles, with no
    trusted row. -/
theorem exData_sound (d : Nat) (tot : Int) (h : DRun 32 false exCode [exFunD] [exDFun] d 0x100 tot) :
    tot ≤ 68 :=
  data_sound 32 false exCode [exFunD] [exCert] [exDFun] exBinaryD_checks exData_checks d 0x100 0 tot h
    (by decide)

end

/-! ### Data runs that exist: a concrete simulator

To show that the hypotheses of `data_sound` can be met, runs are built from concrete
states (eight registers as a list, the flags, SP `0x8000`, memory `0`) and checked by
boolean functions whose acceptance implies the relations of the data semantics
(`effOkB_sound`, `chainB_sound`, `dOkB_sound`; for instructions that do not touch the
stack). The counting loop then has a run of exactly 68 cycles (`exData_run`): the bound of
`exData_sound` is attained. -/

/-- A concrete state. -/
def mkS (r : List Nat) (f : Flags) : MState := ⟨fun i => r.getD i 0, f, 32768, fun _ => 0⟩

/-- The flags after an effect, checked on concrete values. -/
def flOkB (fl : FEff) (r : List Nat) (f f' : Flags) : Bool :=
  match fl with
  | .keep => f' == f
  | .any => true
  | .add a b => f' == flagsAdd (srcVal (fun k => r.getD k 0) a) (srcVal (fun k => r.getD k 0) b)
  | .sub a b => f' == flagsSub (srcVal (fun k => r.getD k 0) a) (srcVal (fun k => r.getD k 0) b)

/-- `EffOk`, checked on concrete registers and flags. -/
def effOkB (e : Eff) (r r' : List Nat) (f f' : Flags) : Bool :=
  (List.range 8).all (fun i => decide (r'.getD i 0 < U)) &&
  (List.range 8).all (fun i => match e.dst.find? (fun p => p.1 == i) with
    | none => r'.getD i 0 == r.getD i 0
    | some p => match valOf (fun k => r.getD k 0) p.2 with
      | some v => r'.getD i 0 == v
      | none => true) &&
  flOkB e.fl r f f'

theorem effOkB_sound (e : Eff) (r r' : List Nat) (f f' : Flags) (h : effOkB e r r' f f' = true) :
    EffOk e (mkS r f) (mkS r' f') := by
  simp only [effOkB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨hw, hd⟩, hf⟩ := h
  refine ⟨fun i hi => hw i hi, fun i hi hn => ?_, fun i hi p hp v hv => ?_, ?_⟩
  · have := hd i hi
    rw [hn] at this
    simpa [mkS] using this
  · have := hd i hi
    simp only [hp] at this
    simp only [mkS] at hv ⊢
    simp only [hv] at this
    simpa using this
  · simp only [mkS]
    cases hq : e.fl <;> rw [hq] at hf <;> simp_all [flOkB, flagsOfE]

/-- The instruction does not touch the stack. -/
def stackKeep (s : StackE) : Bool := s.sp == .keep && s.mem == .keep && s.load == none

theorem stackKeep_sound (s : StackE) (h : stackKeep s = true) (frame : Bool) (SP0 : Nat)
    (r r' : List Nat) (f f' : Flags) : StackOk frame SP0 s (mkS r f) (mkS r' f') := by
  simp only [stackKeep, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨by simp [mkS, U], fun _ => by simp [mkS, U]⟩, ?_, ?_, ?_⟩
  · rw [h1]; rfl
  · rw [h2]; intro _; rfl
  · intro p hp; rw [h3] at hp; cases hp

/-- A concrete step: the step of the machine run, the transition, registers, flags. -/
abbrev CStep := MStep × Nat × List Nat × Flags

def toD (x : CStep) : DStep := ⟨x.1, x.2.1, mkS x.2.2.1 x.2.2.2⟩

/-- `DChain`, checked on concrete steps (instructions that do not touch the stack). -/
def chainB (abi : Bool) (c : Code) : Option Nat → List CStep → Bool
  | none, [] => true
  | some a, x :: t => x.1.a == a &&
      (match t with
        | [] => true
        | y :: _ => effOkB (effect abi c a) x.2.2.1 y.2.2.1 x.2.2.2 y.2.2.2 && stackKeep (stackEffect abi c a)) &&
      chainB abi c x.1.next t
  | _, _ => false

theorem chainB_sound (abi frame : Bool) (c : Code) (SP0 : Nat) :
    ∀ (o : Option Nat) (l : List CStep), chainB abi c o l = true → DChain abi frame c SP0 o (l.map toD)
  | none, [], _ => by simp [DChain]
  | none, _ :: _, h => by simp [chainB] at h
  | some _, [], h => by simp [chainB] at h
  | some a, x :: t, h => by
    simp only [chainB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hxa, hm⟩, hr⟩ := h
    refine ⟨by simpa [toD] using hxa, fun y hy => ?_, chainB_sound abi frame c SP0 _ t hr⟩
    cases t with
    | nil => simp at hy
    | cons z t =>
      simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      simp only [Bool.and_eq_true] at hm
      exact ⟨effOkB_sound _ _ _ _ _ hm.1, stackKeep_sound _ hm.2 frame SP0 _ _ _ _⟩

/-- `DOk`, checked on a concrete step. -/
def dOkB (mul : Nat) (c : Code) (x : CStep) : Bool :=
  (List.range 8).all (fun i => decide (x.2.2.1.getD i 0 < U)) &&
  match decode mul c x.1.a with
  | some i => (trans i x.1.a)[x.2.1]? == some (x.1.next, x.1.w, x.1.calls) &&
      (match i.kind with
        | .cond _ => condHolds (ccOf c x.1.a) x.2.2.2 == (x.2.1 == 0)
        | _ => true)
  | none => false

theorem dOkB_sound (mul : Nat) (c : Code) (x : CStep) (h : dOkB mul c x = true) :
    DOkM mul c (toD x).st.a (toD x).j (toD x).σ (toD x).st.next (toD x).st.w (toD x).st.calls := by
  simp only [dOkB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hw, hd⟩ := h
  refine ⟨fun i hi => by simpa [toD, mkS] using hw i hi, ⟨by simp [toD, mkS, U], fun _ => by simp [toD, mkS, U]⟩, ?_⟩
  split at hd
  · rename_i i hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hd
    refine ⟨i, by simpa [toD] using hi, Or.inl ⟨by simpa [toD] using hd.1, fun t ht => ?_⟩⟩
    have := hd.2
    rw [ht] at this
    simpa [toD, mkS] using this
  · cases hd

/-- Runs of instructions without exact values beyond `effect` (no `xop`) satisfy `XChain`. -/
theorem xchain_none (c : Code) (s : List DStep)
    (h : ∀ x ∈ s, xop c x.st.a = none ∧ rngOps c x.st.a = []) : XChain c s := by
  intro k x y hx _
  have hh := h x (List.mem_of_getElem? hx)
  refine ⟨fun op hop => ?_, fun q hq => ?_⟩
  · rw [hh.1] at hop; cases hop
  · rw [hh.2] at hq; cases hq

/-- The registers `r0 = v`, the others `0`. -/
def regs0 (v : Nat) : List Nat := [v, 0, 0, 0, 0, 0, 0, 0]

def f0 : Flags := ⟨false, false, false, false⟩

def cstep (a : Nat) (next : Option Nat) (w j v : Nat) (f : Flags) : CStep := (⟨a, next, w, [], 0⟩, j, regs0 v, f)

/-- The flags at `cmp` in iteration `v`. -/
def exFl (v : Nat) : Flags := if v = 0 then f0 else flagsAdd (v - 1) 1

/-- The run of the counting loop: `movs`, ten iterations, the last test and the return. -/
def exRunC : List CStep :=
  [cstep 0x100 (some 0x102) 1 0 0 f0] ++
  (List.range 10).flatMap (fun v =>
    [cstep 0x102 (some 0x104) 1 0 v (exFl v), cstep 0x104 (some 0x106) 1 1 v (flagsSub v 10),
     cstep 0x106 (some 0x108) 1 0 v (flagsSub v 10), cstep 0x108 (some 0x102) 3 0 (v + 1) (flagsAdd v 1)]) ++
  [cstep 0x102 (some 0x104) 1 0 10 (exFl 10), cstep 0x104 (some 0x10A) 3 0 10 (flagsSub 10 10),
   cstep 0x10A none 3 0 10 (flagsSub 10 10)]

theorem exRun_chain : chainB false exCode (some 0x100) exRunC = true := by decide

theorem exRun_steps : exRunC.all (dOkB 32 exCode) = true := by decide

theorem exRun_noX : exRunC.all (fun x => xop exCode x.1.a == none && rngOps exCode x.1.a == []) = true := by decide

theorem exRun_cost : ((exRunC.map toD).map fun x => (x.st.w : Int) + x.st.x).sum = 68 := by decide

/-- **The hypotheses are satisfiable, and the bound is attained**: the counting loop has a
    run of the data semantics of exactly 68 cycles, the bound of `exData_sound`. -/
theorem exData_run : DRun 32 false exCode [exFunD] [exDFun] 1 0x100 68 := by
  refine ⟨exFunD, exDFun, exRunC.map toD, rfl, ?_, ?_, ?_, ?_, exRun_cost.symm⟩
  · exact chainB_sound false exDFun.frame exCode _ (some 0x100) exRunC exRun_chain
  · exact xchain_none exCode _ (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact List.all_eq_true.mp exRun_noX y hy |> fun h => by simpa [toD] using h)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    refine ⟨dOkB_sound 32 exCode y (List.all_eq_true.mp exRun_steps y hy), ?_⟩
    have : y.1.calls = [] ∧ y.1.x = 0 := by
      revert hy; simp only [exRunC, cstep, List.mem_append, List.mem_flatMap, List.mem_range,
        List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      intro hy; rcases hy with (rfl | ⟨v, _, hv⟩) | hv <;> (try rcases hv with rfl | rfl | rfl | rfl) <;> simp
    simp only [toD, this.1, this.2, CallsWith]
  · intro r hr; simp [exDFun] at hr

open ImperativeOptimization.Checker (Lin) in
section

/-! ### An example that needs congruences

`movs r0, #0; L: adds r0, #4; cmp r0, #40; bne L; bx lr`: the counter is stepped by 4 and
the loop exits on equality, so `r0 ≤ 40` and `r0 ≠ 40` do not give `r0 ≤ 36` without the
congruence `r0 ≡ 0 (mod 4)`. The certificate (made by `benchmarks/cycles/binloops.py`)
carries that congruence at the loop's instructions; the bound, 52 cycles, is the worst
case (ten iterations), with no trusted row. Without the congruences the same certificate
is rejected (`exStep_needs_cong`). -/

def exStepCode : Code := ⟨0x100, #[0x2000, 0x3004, 0x2828, 0xd1fc, 0x4770]⟩

def exStepKinds : List FKind := [.none, .none, .add, .sub, .sub]

def exStepInv : List (List Lin) :=
  [[],
    [⟨[1], [], -36⟩],
    [⟨[1], [], -40⟩, ⟨[-1], [], 4⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, -1], [], -4⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -36⟩, ⟨[-1, 0, 0, 0, 0, 0, 0, 0, 1], [], 4⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -4⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 4⟩],
    [⟨[1], [], -40⟩, ⟨[-1], [], 4⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, -1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -40⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1], [], 4⟩, ⟨[-1, 0, 0, 0, 0, 0, 0, 0, 1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -40⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 40⟩],
    [⟨[1], [], -40⟩, ⟨[-1], [], 40⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -40⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1], [], 40⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -40⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 40⟩]]

def exStepLoop : LoopCert := ⟨258, [258, 260, 262], 4, 36, [⟨[-1], 36⟩, ⟨[-1], 40⟩, ⟨[-1], 40⟩]⟩

def exStepProofs : List (Nat × List Nat) :=
  [(1, []),
    (1, []),
    (1, []),
    (1, [0, 4294967260]),
    (1, []),
    (1, []),
    (1, [1]),
    (1, [0, 0, 1]),
    (1, [0, 0, 0, 1]),
    (1, []),
    (1, [0, 0, 1]),
    (1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [0, 1717986911, 0, 1717986911, 1]),
    (1, [0, 1, 0, 2]),
    (1, [0, 858993460, 0, 858993460]),
    (1, [0, 858993452, 0, 858993452, 1]),
    (1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [1, 0, 1, 0, 1]),
    (1, [2, 0, 2, 1]),
    (1, []),
    (1, [2, 0, 2, 0, 1]),
    (1, [2, 0, 2]),
    (1, []),
    (1, []),
    (1, [2, 0, 2]),
    (1, [1]),
    (1, [0, 1]),
    (1, []),
    (1, [1]),
    (1, [0, 1]),
    (1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [1, 0, 0, 1, 0, 0, 0, 1]),
    (1, []),
    (1, [1073741815, 0, 0, 0, 1073741815, 0, 0, 0, 1073741815, 0, 1]),
    (1, []),
    (1, [0, 0, 1]),
    (1, [0, 1, 0, 0, 0, 0, 0, 1, 0, 1]),
    (1, [0, 0, 0, 0, 0, 1]),
    (1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 1]),
    (1, [])]

def exStepCong : List (List (Nat × Nat × Nat)) :=
  [[], [(0, 2, 0)], [(0, 2, 0), (8, 2, 0), (9, 32, 4)], [(0, 2, 0), (8, 2, 0), (9, 32, 40)], [(0, 2, 0), (8, 2, 0), (9, 32, 40)]]

def exStepFun0 : BFun := ⟨0x100, [256, 258, 260, 262, 264], [], []⟩

def exStepFun : BFun := { exStepFun0 with rows := [loopRow exStepFun0 exStepLoop] }

def exStepCert : Cert := ⟨4, [208, 24, 20, 16, 12, 0], [5], 52⟩

def exStepDFun : DFun :=
  ⟨exStepKinds, exStepInv, [exStepLoop], [], exStepProofs, [some 0, some 0, some 0, some 0, some 0], [], false, exStepCong, [], []⟩

theorem exStep_binary : checkBinary 32 exStepCode [exStepFun] [exStepCert] true = true := by decide

theorem exStep_checks : checkData 32 false exStepCode [exStepFun] [exStepDFun] = true := by decide

/-- The same certificate without its congruences is rejected. -/
theorem exStep_needs_cong :
    checkData 32 false exStepCode [exStepFun] [{ exStepDFun with cong := [] }] = false := by decide

/-- Every run of the data semantics of the stepped loop costs at most 52 cycles, with no
    trusted row. -/
theorem exStep_sound (d : Nat) (tot : Int)
    (h : DRun 32 false exStepCode [exStepFun] [exStepDFun] d 0x100 tot) : tot ≤ 52 :=
  data_sound 32 false exStepCode [exStepFun] [exStepCert] [exStepDFun] exStep_binary exStep_checks
    d 0x100 0 tot h (by decide)

end


open ImperativeOptimization.Checker (Lin) in
section

/-! ### An example that needs a disjunctive invariant

`movs r3, #9; L: subs r3, r3, #1; adds r2, r3, #1; bcs out; b L; out: bx lr`, the loop
`for (i = 9; i >= 0; i--)` as Clang compiles it (the run-time division routines count the
same way from 31): the exit is taken when `r3 + 1` carries, that is once `r3` has wrapped
around to `2^32 - 1`. Between the subtraction and the branch, `r3 ≤ 8` or `r3 = 2^32 - 1`,
which no conjunction of linear constraints expresses; the certificate (made by
`benchmarks/cycles/binloops.py`) gives the two disjuncts (`alt`) and the disjunct each case
lands in (`pick`). The bound, 63 cycles, has no trusted row. Without the alternatives the
same certificate is rejected (`exWrap_needs_alt`). -/

def exWrapCode : Code := ⟨0x100, #[0x2309, 0x1E5B, 0x1C5A, 0xD200, 0xE7FB, 0x4770, 0x0, 0x0]⟩

def exWrapKinds : List FKind := [.none, .none, .sub, .add, .add, .add]

def exWrapInv : List (List Lin) :=
  [[],
    [⟨[0, 0, 1, -1], [], -4294967286⟩, ⟨[0, 0, 0, 1], [], -9⟩],
    [⟨[0, 0, 1, -1], [], -4294967287⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, -1], [], -4294967286⟩, ⟨[0, 0, 0, 1], [], -8⟩, ⟨[0, 0, 0, 1, 0, 0, 0, 0, -1], [], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -9⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1], [], 1⟩, ⟨[0, 0, 0, -1, 0, 0, 0, 0, 1], [], -1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 1⟩],
    [⟨[0, 0, 1], [], -9⟩, ⟨[0, 0, -1], [], 1⟩, ⟨[0, 0, 1, -1], [], -1⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, -1], [], -1⟩, ⟨[0, 0, 0, 1], [], -8⟩, ⟨[0, 0, -1, 1], [], 1⟩, ⟨[0, 0, 0, 1, 0, 0, 0, 0, -1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -8⟩, ⟨[0, 0, -1, 0, 0, 0, 0, 0, 1], [], 1⟩, ⟨[0, 0, 0, -1, 0, 0, 0, 0, 1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 1⟩],
    [⟨[0, 0, 1], [], -9⟩, ⟨[0, 0, -1], [], 1⟩, ⟨[0, 0, 1, -1], [], -1⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, -1], [], -1⟩, ⟨[0, 0, 0, 1], [], -8⟩, ⟨[0, 0, -1, 1], [], 1⟩, ⟨[0, 0, 0, 1, 0, 0, 0, 0, -1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -8⟩, ⟨[0, 0, -1, 0, 0, 0, 0, 0, 1], [], 1⟩, ⟨[0, 0, 0, -1, 0, 0, 0, 0, 1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 1⟩],
    [⟨[0, 0, 0, -1], [], 4294967295⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1], [], 4294967295⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 1⟩]]

def exWrapAlt : List (List (List Lin)) :=
  [[],
    [],
    [[⟨[0, 0, 1], [], -4294967286⟩, ⟨[0, 0, 0, -1], [], 4294967295⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 1⟩]],
    [[⟨[0, 0, 0, -1], [], 4294967295⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1], [], 4294967295⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 1⟩]],
    [],
    []]

def exWrapPick : List (List (Nat × Int × Nat × Nat × Nat)) := [[], [(0, 1, 0, 0, 1)], [(0, 0, 0, 1, 1), (0, 1, 0, 1, 1), (0, -1, 0, 1, 1)], [], [], []]

def exWrapCong : List (List (Nat × Nat × Nat)) := [[], [], [(9, 32, 1)], [(9, 32, 1)], [(9, 32, 1)], [(9, 32, 1)]]

def exWrapLoop : LoopCert := ⟨258, [258, 260, 262, 264], 1, 9, [⟨[0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1, -16], 16⟩, ⟨[0, 0, 1, 16, 0, 0, 0, 0, -16, -16], 16⟩, ⟨[0, 0, 16, -16, 0, 0, 0, 0, 1, 16], -31⟩]⟩

def exWrapProofs : List (Nat × List Nat) :=
  [(1, []),
    (1, [0, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, []),
    (1, [0, 1, 0, 0, 0, 0, 0, 1]),
    (1, [0, 429496730]),
    (1, [0, 429496730]),
    (1, [2, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, []),
    (1, [0, 0, 1]),
    (1, [0, 0, 1]),
    (1, [0, 0, 0, 1]),
    (1, []),
    (1, [0, 0, 0, 1]),
    (1, [1]),
    (1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [0, 1, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 1]),
    (1, []),
    (1, []),
    (1, []),
    (1, [2, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1]),
    (1, [1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1]),
    (1, [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 0, 2]),
    (1, []),
    (1, []),
    (1, []),
    (1, [0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, []),
    (1, [0, 0, 0, 0, 1]),
    (1, []),
    (1, []),
    (1, [0, 0, 0, 0, 1]),
    (1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [0, 0, 0, 0, 0, 1, 0, 0, 0, 16]),
    (1, [0, 4294967295, 0, 4294967295, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 4294967295, 0, 4294967295, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, []),
    (1, [0, 73014444000, 0, 73014444000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 16]),
    (1, [0, 4294967292, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4294967292, 1]),
    (1, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]),
    (1, [0, 2147483648, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2147483648]),
    (1, [0, 2147483648, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2147483648]),
    (1, [0, 2147483644, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2147483644, 1]),
    (1, []),
    (1, []),
    (1, [0, 2147483644, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2147483644, 1]),
    (1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [0, 38654705648, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38654705648, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 16]),
    (1, [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, []),
    (1, [0, 18, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 16]),
    (1, [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, []),
    (1, [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 0, 0, 2]),
    (1, []),
    (1, [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 0, 0, 2]),
    (1, []),
    (1, []),
    (1, []),
    (1, [17, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 16]),
    (1, [1]),
    (1, [1]),
    (1, []),
    (1, []),
    (1, [0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [33, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 33, 0, 0, 0, 0, 0, 1, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 16]),
    (1, [0, 1]),
    (1, [0, 0, 1]),
    (1, [0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 1]),
    (1, [0, 16, 0, 16, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16]),
    (1, [0, 1]),
    (1, [0, 0, 1]),
    (1, [0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 17, 32]),
    (1, [4294967286, 0, 4294967286, 0, 4294967286, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 1, 0, 1, 0, 0, 0, 0, 1]),
    (1, [4294967294, 0, 4294967294, 0, 4294967294, 0, 0, 0, 0, 0, 1, 1]),
    (1, [4294967294, 0, 4294967294, 0, 4294967294, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [4294967287, 0, 4294967287, 0, 4294967287, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [4294967296, 0, 4294967296, 0, 4294967296, 0, 0, 0, 0, 1, 0, 0, 1]),
    (1, [4294967295, 0, 4294967295, 0, 4294967295, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [4294967287, 0, 4294967287, 0, 4294967287, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [4294967296, 0, 4294967296, 0, 4294967296, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [4294967295, 0, 4294967295, 0, 4294967295, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [4294967294, 0, 4294967294, 0, 4294967294, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [274877906833, 0, 274877906833, 0, 274877906833, 0, 0, 0, 0, 0, 15, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 32]),
    (1, [0, 0, 1]),
    (1, [0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 16, 1, 0, 0, 0, 0, 16]),
    (1, [])]

def exWrapFun0 : BFun := ⟨256, [256, 258, 260, 262, 264, 266], [], []⟩

def exWrapFun : BFun := { exWrapFun0 with rows := [loopRow exWrapFun0 exWrapLoop] }

def exWrapDFun : DFun :=
  ⟨exWrapKinds, exWrapInv, [exWrapLoop], [], exWrapProofs, [some 0, some 0, some 0, some 0, some 0, some 0], [], false, exWrapCong, exWrapAlt, exWrapPick⟩

def exWrapCert : Cert := ⟨1, [63, 8, 7, 6, 5, 3, 0], [6], 63⟩

theorem exWrap_binary : checkBinary 32 exWrapCode [exWrapFun] [exWrapCert] true = true := by decide

theorem exWrap_checks : checkData 32 false exWrapCode [exWrapFun] [exWrapDFun] = true := by decide

theorem exWrap_needs_alt :
    checkData 32 false exWrapCode [exWrapFun] [{ exWrapDFun with alt := [], pick := [] }] = false := by
  decide

/-- Every run of the data semantics of the example costs at most 63 cycles. -/
theorem exWrap_sound (d : Nat) (tot : Int)
    (h : DRun 32 false exWrapCode [exWrapFun] [exWrapDFun] d 0x100 tot) : tot ≤ 63 :=
  data_sound 32 false exWrapCode [exWrapFun] [exWrapCert] [exWrapDFun] exWrap_binary exWrap_checks
    d 0x100 0 tot h (by decide)

end


open ImperativeOptimization.Checker (Lin) in
section

/-! ### An example that needs the rounding of a sum

`movs r3, #15; mvns r3, r3; L: adds r3, #4; bne L; bx lr`: Clang's count from `2^32 - 16` up
by 4 to zero (`fft`, `fir2dim`). In the case of the wrap-around, the fact that continues the
loop is `r3 + 4 ≥ 2^32 + 1` on the flags' operands; with the congruences `r3 ≡ 0` and
`4 ≡ 0 (mod 4)` it is rounded to `r3 + 4 ≥ 2^32 + 4` (`tightenS`), which the bound
`r3 ≤ 2^32 - 4` contradicts. The bound, 19 cycles, has no trusted row; without the
congruences the certificate is rejected (`exZero_needs_cong`). -/

def exZeroCode : Code := ⟨0x100, #[0x230F, 0x43DB, 0x3304, 0xD1FD, 0x4770, 0x0, 0x0]⟩

def exZeroKinds : List FKind := [.none, .none, .none, .add, .add]

def exZeroInv : List (List Lin) :=
  [[],
    [⟨[0, 0, 0, 1], [], -15⟩, ⟨[0, 0, 0, -1], [], 15⟩],
    [⟨[0, 0, 0, 1], [], -4294967292⟩, ⟨[0, 0, 0, -1], [], 4294967280⟩],
    [⟨[0, 0, 0, -1], [], 4294967284⟩, ⟨[0, 0, 0, 1, 0, 0, 0, 0, -1], [], -4⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -4294967291⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1], [], 4294967280⟩, ⟨[0, 0, 0, -1, 0, 0, 0, 0, 1], [], 4⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -4⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 4⟩],
    [⟨[0, 0, 0, 1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -4294967292⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1], [], 4294967292⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -4⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 4⟩]]

def exZeroAlt : List (List (List Lin)) :=
  [[],
    [],
    [],
    [[⟨[0, 0, 0, 1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], -4294967292⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1], [], 4294967292⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], -4⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], 4⟩]],
    []]

def exZeroPick : List (List (Nat × Int × Nat × Nat × Nat)) := [[], [], [(0, -1, 0, 0, 1)], [], []]

def exZeroCong : List (List (Nat × Nat × Nat)) := [[], [(3, 32, 15)], [(3, 2, 0)], [(3, 2, 0), (8, 2, 0), (9, 32, 4)], [(3, 2, 0), (8, 2, 0), (9, 32, 4)]]

def exZeroLoop : LoopCert := ⟨260, [260, 262], 4, 12, [⟨[0, 0, 0, -1], 4294967292⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1], 4294967292⟩]⟩

def exZeroProofs : List (Nat × List Nat) :=
  [(1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [0, 268435456]),
    (1, []),
    (1, []),
    (1, []),
    (1, [2]),
    (1, []),
    (1, [0, 0, 0, 1]),
    (1, [0, 0, 1]),
    (1, [0, 0, 1]),
    (1, [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]),
    (1, [536870911, 0, 0, 536870911, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [536870911, 0, 0, 536870911, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 1]),
    (1, []),
    (1, [0, 1]),
    (1, [0, 0, 0, 1]),
    (1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 2, 0, 2]),
    (1, [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, []),
    (1, []),
    (1, []),
    (1, [0, 0, 1]),
    (1, [0, 0, 1]),
    (1, [1]),
    (1, []),
    (1, []),
    (1, []),
    (1, [0, 1, 0, 1, 0, 0, 0, 0, 1]),
    (1, [0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 1073741820, 0, 0, 1073741820, 0, 1073741820, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 1073741825, 0, 0, 1073741825, 0, 1073741825, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [858993456, 0, 0, 858993456, 0, 0, 858993456, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [858993460, 0, 0, 858993460, 0, 0, 858993460, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1073741820, 0, 1073741820, 0, 1073741820, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1073741825, 0, 1073741825, 0, 1073741825, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 4294967295, 0, 0, 4294967295, 0, 0, 4294967295, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 3, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 4294967292, 0, 0, 4294967292, 0, 0, 4294967292, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 4294967291, 0, 0, 4294967291, 0, 0, 4294967291, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 4, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 3, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 1]),
    (1, [0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 0, 1]),
    (1, [])]

def exZeroFun0 : BFun := ⟨256, [256, 258, 260, 262, 264], [], []⟩

def exZeroFun : BFun := { exZeroFun0 with rows := [loopRow exZeroFun0 exZeroLoop] }

def exZeroDFun : DFun :=
  ⟨exZeroKinds, exZeroInv, [exZeroLoop], [], exZeroProofs, [some 0, some 0, some 0, some 0, some 0], [], false, exZeroCong, exZeroAlt, exZeroPick⟩

def exZeroCert : Cert := ⟨1, [19, 18, 5, 4, 3, 0], [1], 19⟩

theorem exZero_binary : checkBinary 32 exZeroCode [exZeroFun] [exZeroCert] true = true := by decide

theorem exZero_checks : checkData 32 false exZeroCode [exZeroFun] [exZeroDFun] = true := by decide

theorem exZero_needs_cong :
    checkData 32 false exZeroCode [exZeroFun] [{ exZeroDFun with cong := [] }] = false := by
  decide

/-- Every run of the data semantics of the example costs at most 19 cycles. -/
theorem exZero_sound (d : Nat) (tot : Int)
    (h : DRun 32 false exZeroCode [exZeroFun] [exZeroDFun] d 0x100 tot) : tot ≤ 19 :=
  data_sound 32 false exZeroCode [exZeroFun] [exZeroCert] [exZeroDFun] exZero_binary exZero_checks
    d 0x100 0 tot h (by decide)

end

/-! ### An example: a jump through a table

`switch (r0) {0, 1, 2}` as Clang compiles it for the Cortex-M0: `cmp r0, #2; bhi 0x116;
add r0, pc; ldrb r0, [r0, #4]; lsls r0, r0, #1; add pc, r0`, a table of bytes `1, 2, 3`,
then `bx lr` at `0x110`, `0x112`, `0x114` (the cases) and `0x116` (the default). The check
evaluates the window for `r0 = 0, 1, 2` and finds the three targets; worst case
`1 + 1 + 1 + 2 + 1 + 3 + 3 = 12` cycles. The same certificate is refused without the data
check (`jt`), and with a target left out. -/

def exSwCode : Code :=
  ⟨0x100, #[0x2802, 0xD808, 0x4478, 0x7900, 0x0040, 0x4487, 0x0201, 0x0003, 0x4770, 0x4770, 0x4770, 0x4770]⟩

def exSwFun : BFun :=
  ⟨0x100, [0x100, 0x102, 0x104, 0x106, 0x108, 0x10A, 0x110, 0x112, 0x114, 0x116], [],
   [⟨0x100, 0x10A, [0x110, 0x112, 0x114], none, none⟩]⟩

def exSwCert : Cert := ⟨1, [12, 11, 10, 9, 7, 6, 3, 3, 3, 3, 0], [], 12⟩

def exSwD : DFun := { kinds := [], inv := [], loops := [], trusted := [], proofs := [] }

theorem exSw_checks : checkBinary 32 exSwCode [exSwFun] [exSwCert] true = true := by decide

theorem exSw_data : checkData 32 false exSwCode [exSwFun] [exSwD] = true := by decide

theorem exSw_needs_jt : checkBinary 32 exSwCode [exSwFun] [exSwCert] = false := by decide

theorem exSw_target_missing :
    checkData 32 false exSwCode [{ exSwFun with jumps := [⟨0x100, 0x10A, [0x110, 0x112], none, none⟩] }] [exSwD] = false := by
  decide

/-- Every run of the data semantics of the switch costs at most 12 cycles. -/
theorem exSw_sound (d : Nat) (tot : Int) (h : DRun 32 false exSwCode [exSwFun] [exSwD] d 0x100 tot) :
    tot ≤ 12 :=
  data_sound 32 false exSwCode [exSwFun] [exSwCert] [exSwD] exSw_checks exSw_data d 0x100 0 tot h (by decide)

/-- The same switch with the range check as `BLS` over a branch to the default case (Clang's
    form when the default case is out of reach of a conditional branch): `cmp r0, #2;
    bls 0x106; b 0x118; add r0, pc; ldrb r0, [r0, #4]; lsls r0, r0, #1; add pc, r0`, the table,
    the cases at `0x112`, `0x114`, `0x116`; worst case `1 + 3 + 1 + 2 + 1 + 3 + 3 = 14`. -/
def exLsCode : Code :=
  ⟨0x100, #[0x2802, 0xD900, 0xE008, 0x4478, 0x7900, 0x0040, 0x4487, 0x0201, 0x0003, 0x4770, 0x4770, 0x4770, 0x4770]⟩

def exLsFun : BFun :=
  ⟨0x100, [0x100, 0x102, 0x104, 0x106, 0x108, 0x10A, 0x10C, 0x112, 0x114, 0x116, 0x118], [],
   [⟨0x100, 0x10C, [0x112, 0x114, 0x116], none, none⟩]⟩

def exLsCert : Cert := ⟨1, [14, 13, 6, 10, 9, 7, 6, 3, 3, 3, 3, 0], [], 14⟩

theorem exLs_checks : checkBinary 32 exLsCode [exLsFun] [exLsCert] true = true := by decide

theorem exLs_data : checkData 32 false exLsCode [exLsFun] [exSwD] = true := by decide

theorem exLs_target_missing :
    checkData 32 false exLsCode [{ exLsFun with jumps := [⟨0x100, 0x10C, [0x112, 0x116], none, none⟩] }] [exSwD] = false := by
  decide

theorem exLs_sound (d : Nat) (tot : Int) (h : DRun 32 false exLsCode [exLsFun] [exSwD] d 0x100 tot) :
    tot ≤ 14 :=
  data_sound 32 false exLsCode [exLsFun] [exLsCert] [exSwD] exLs_checks exLs_data d 0x100 0 tot h (by decide)

/-! #### A switch without `CMP`

At `0x100`: `movs r1, #3; ands r0, r1; add r0, pc; ldrb r0, [r0, #4]; lsls r0, r0, #1;
add pc, r0`, a table of bytes `1, 2, 3, 4`, then `bx lr` at `0x110`, ..., `0x116`: Clang's
form of `switch (x & 3)` with every case present. The window starts at the `movs` (the
mask) and is bounded at the `ands` (`ix`); worst case 12 cycles. With the mask widened to
`7` the indices `4..7` read the code after the table, and the check refuses. -/

def exMaskCode : Code :=
  ⟨0x100, #[0x2103, 0x4008, 0x4478, 0x7900, 0x0040, 0x4487, 0x0201, 0x0403, 0x4770, 0x4770, 0x4770, 0x4770]⟩

def exMaskFun : BFun :=
  ⟨0x100, [0x100, 0x102, 0x104, 0x106, 0x108, 0x10A, 0x110, 0x112, 0x114, 0x116], [],
   [⟨0x100, 0x10A, [0x110, 0x112, 0x114, 0x116], some 0x102, none⟩]⟩

theorem exMask_checks : checkBinary 32 exMaskCode [exMaskFun] [exSwCert] true = true := by decide

theorem exMask_data : checkData 32 false exMaskCode [exMaskFun] [exSwD] = true := by decide

theorem exMask_wide :
    checkData 32 false ⟨0x100, #[0x2107, 0x4008, 0x4478, 0x7900, 0x0040, 0x4487, 0x0201, 0x0403,
      0x4770, 0x4770, 0x4770, 0x4770]⟩ [exMaskFun] [exSwD] = false := by decide

theorem exMask_needs_ix :
    checkData 32 false exMaskCode [{ exMaskFun with jumps := [⟨0x100, 0x10A, [0x110, 0x112, 0x114, 0x116], none, none⟩] }]
      [exSwD] = false := by decide

/-- Every data run of the switch without `CMP` costs at most 12 cycles. -/
theorem exMask_sound (d : Nat) (tot : Int) (h : DRun 32 false exMaskCode [exMaskFun] [exSwD] d 0x100 tot) :
    tot ≤ 12 :=
  data_sound 32 false exMaskCode [exMaskFun] [exSwCert] [exSwD] exMask_checks exMask_data d 0x100 0 tot h (by decide)

/-! #### A switch bounded by the invariant

`if (r0 == 0) t = 0; else t = 1; switch (t)`: at `0x100` `cmp r0, #0; beq 0x108; movs r1, #1;
b 0x10a; movs r1, #0`, then `add r1, pc; ldrb r1, [r1, #4]; lsls r1, r1, #1; add pc, r1`, a
table of bytes `0, 1`, and the cases `bx lr` at `0x114`, `movs r0, #5; bx lr` at `0x116`. No
instruction of the window bounds the index: the certified invariant at `0x10a` does
(`r1 <= 1`, `vr = some (1, 0, 1)`). The certificate was made by `benchmarks/cycles/ipet.py`
(`binloops.py`); worst case 17 cycles, as on `m0.py`. Without the bound, or with the bound
widened to 2 (the byte after the table is read), the check refuses. -/

def exPathCode : Code :=
  ⟨0x100, #[0x2800, 0xD001, 0x2101, 0xE000, 0x2100, 0x4479, 0x7909, 0x49, 0x448F, 0x100, 0x4770, 0x2005, 0x4770]⟩

def exPathFun : BFun :=
  ⟨0x100, [0x100, 0x102, 0x104, 0x106, 0x108, 0x10A, 0x10C, 0x10E, 0x110, 0x114, 0x116, 0x118], [],
   [⟨0x10A, 0x110, [0x114, 0x116], some 0x10A, some (1, 0, 1)⟩]⟩

def exPathCert : Cert := ⟨1, [17, 16, 15, 14, 12, 11, 10, 8, 7, 3, 4, 3, 0], [], 17⟩

def exPathKinds : List FKind := [.none, .sub, .sub, .none, .sub, .none, .none, .none, .none, .none, .none, .none]

def exPathInv : List (List Lin) :=
  [[],
    [⟨[1, 0, 0, 0, 0, 0, 0, 0, -1], [], 0⟩, ⟨[-1, 0, 0, 0, 0, 0, 0, 0, 1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0⟩],
    [⟨[-1], [], 1⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, -1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, -1], [], 1⟩, ⟨[-1, 0, 0, 0, 0, 0, 0, 0, 1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0⟩],
    [⟨[-1], [], 1⟩, ⟨[0, 1], [], -1⟩, ⟨[0, -1], [], 1⟩],
    [⟨[1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0⟩],
    [⟨[1, -1], [], -4294967294⟩, ⟨[0, 1], [], -1⟩, ⟨[-1, 1], [], 0⟩],
    [],
    [],
    [],
    [],
    [],
    [⟨[1], [], -5⟩, ⟨[-1], [], 5⟩]]

def exPathCong : List (List (Nat × Nat × Nat)) := [[], [(9, 32, 0)], [(9, 32, 0)], [(1, 32, 1)], [(9, 32, 0)], [], [], [], [(1, 1, 0)], [(1, 1, 0)], [(1, 1, 0)], [(0, 32, 5), (1, 1, 0)]]

def exPathProofs : List (Nat × List Nat) :=
  [(1, []),
    (1, []),
    (1, []),
    (1, [1, 0, 1, 0, 1]),
    (1, [1, 0, 0, 0, 1]),
    (1, [0, 0, 0, 0, 1]),
    (1, [1, 1, 0, 1, 2]),
    (1, [4294967295, 4294967295, 0, 4294967295, 4294967295, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [4294967295, 4294967295, 0, 4294967295, 4294967296, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [4294967295, 4294967295, 0, 4294967295, 4294967295, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 1]),
    (1, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (1, [0, 0, 1]),
    (1, [0, 0, 0, 1]),
    (1, [0, 0, 1]),
    (1, []),
    (1, []),
    (1, [0, 1, 0, 0, 0, 0, 0, 1]),
    (1, [0, 2147483648]),
    (1, []),
    (1, [1, 0, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, [2]),
    (1, [0, 0, 1, 0, 1]),
    (1, [0, 1]),
    (1, [1, 1]),
    (1, [0, 0, 1]),
    (1, []),
    (1, [0, 0, 0, 0, 0, 1]),
    (1, [0, 1, 0, 0, 0, 0, 1]),
    (1, [0, 4294967295]),
    (1, [0, 4294967296, 0, 0, 0, 1]),
    (1, [2, 0, 0, 0, 0, 0, 1]),
    (1, []),
    (1, [1, 0, 0, 0, 0, 1]),
    (1, []),
    (1, []),
    (1, [0, 715827883]),
    (1, []),
    (1, []),
    (1, [2])]

def exPathD : DFun :=
  { kinds := exPathKinds, inv := exPathInv, loops := [], trusted := [], proofs := exPathProofs,
    spOff := [some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0], cong := exPathCong }


theorem exPath_checks : checkBinary 32 exPathCode [exPathFun] [exPathCert] true = true := by decide

theorem exPath_data : checkData 32 false exPathCode [exPathFun] [exPathD] = true := by decide

theorem exPath_needs_bound :
    checkData 32 false exPathCode
      [{ exPathFun with jumps := [⟨0x10A, 0x110, [0x114, 0x116], some 0x10A, none⟩] }] [exPathD] = false := by
  decide

theorem exPath_wide :
    checkData 32 false exPathCode
      [{ exPathFun with jumps := [⟨0x10A, 0x110, [0x114, 0x116], some 0x10A, some (1, 0, 2)⟩] }] [exPathD] = false := by
  decide

/-- Every data run of the switch bounded by the invariant costs at most 17 cycles. -/
theorem exPath_sound (d : Nat) (tot : Int) (h : DRun 32 false exPathCode [exPathFun] [exPathD] d 0x100 tot) :
    tot ≤ 17 :=
  data_sound 32 false exPathCode [exPathFun] [exPathCert] [exPathD] exPath_checks exPath_data d 0x100 0 tot h
    (by decide)

end ImperativeOptimization.Thumb
