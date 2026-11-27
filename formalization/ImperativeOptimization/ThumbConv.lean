/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import ImperativeOptimization.ThumbData

/-!
# The calling convention, checked instead of assumed

`ThumbData` proves loop bounds on the machine code in a semantics where a call (`BL`) is one
step whose effect is given by `effect abi`: with `abi`, the callee preserves `r4`-`r11` and
SP, an assumption on the code of the callees (the AAPCS). This module removes it.

* `DRunL`: the *linked* data semantics. A run has an initial and a final state; at a `BL`,
  the callee runs from the caller's state, and the caller continues with the callee's final
  registers and SP. Besides the effects of `ThumbData` (taken without the assumption), it
  states two facts of the processor and one hypothesis on the program:
  - `PushPopOk`: `PUSH` stores its registers in ascending order below SP, `POP` loads them
    back (ARMv6-M, A6.7);
  - `SaveSafe` (the hypothesis, *no stack smashing*): the words where a function saves
    registers at its entry are not written by stores through registers other than SP, nor
    by the functions it calls.
* `convOk` (in `ThumbDataCore`, executable): the function writes none of `r8`-`r11`, saves
  the registers of `r4`-`r7` that it writes with one `PUSH` at its entry, restores them with a `POP` of the same list at
  every return, at the offset of SP where they were saved, and stores through SP only below
  them. The check follows `transJ`: the targets of the function's jumps through tables are
  transitions like the others.
* `conv_chain`: a function accepted by `convOk` returns with `r4`-`r11` and SP as it
  found them (along the transitions that `ThumbData.steps_good` gives every step);
  `drunL_drun`: hence a run of the linked semantics is a run of `ThumbData`'s
  semantics *with* the assumption, by induction on the depth of calls;
  **`data_sound_conv`**: the loop bounds and the cycle bound hold for every run of the
  linked semantics, without the assumption on callees.
-/

namespace ImperativeOptimization.Thumb

open ImperativeOptimization.Cycles

/-! ### The linked semantics -/

/-- The position of register `k` in the list of a `PUSH`/`POP` encoded in `h`. -/
def rankBits (h k : Nat) : Nat := popcount8 (h % 2 ^ k)

/-- `PUSH` stores the registers of its list in ascending order at `sp - 4n`, ..., `sp - 4`
    (`n`: the words pushed, `lr` last); `POP` loads them from `sp`, `sp + 4`, ... -/
def PushPopOk (c : Code) (a : Nat) (σ σ' : MState) : Prop :=
  match c.get a with
  | some h =>
    (isPushH h = true → ∀ k < 8, (h >>> k) % 2 = 1 →
      σ'.mem (aOf ((σ.sp : Int) - 4 * ((popcount8 h + (h >>> 8) % 2 : Nat) : Int) +
        4 * (rankBits h k : Int))) = σ.r k) ∧
    (h >>> 9 = 0b1011110 → ∀ k < 8, (h >>> k) % 2 = 1 →
      σ'.r k = σ.mem (aOf ((σ.sp : Int) + 4 * (rankBits h k : Int))))
  | none => True

/-- The saved words of a function entered with SP `SP0` that saved `n` words. -/
def savedAddr (SP0 n j : Nat) : Nat := aOf ((SP0 : Int) - 4 * (n : Int) + 4 * (j : Int))

/-- No stack smashing: a store through a register other than SP, or a call, leaves the
    saved words unchanged. -/
def SaveSafe (SP0 n : Nat) (s : StackE) (σ σ' : MState) : Prop :=
  s.mem = .other → ∀ j < n, σ'.mem (savedAddr SP0 n j) = σ.mem (savedAddr SP0 n j)

/-- A step of the linked semantics, from the state of `x` to `σ'`; `R g σ σo k`: the callee
    `g` runs from `σ` to `σo` with cost `k`. -/
def StepL (R : Nat → MState → MState → Int → Prop) (frame : Bool) (c : Code) (SP0 n : Nat)
    (x : DStep) (σ' : MState) : Prop :=
  EffOk (effect false c x.st.a) x.σ σ' ∧ StackOk frame SP0 (stackEffect false c x.st.a) x.σ σ' ∧
    PushPopOk c x.st.a x.σ σ' ∧ SaveSafe SP0 n (stackEffect false c x.st.a) x.σ σ' ∧
    (x.st.calls = [] → x.st.x = 0) ∧
    (∀ g, x.st.calls = [g] → ∃ σo, R g x.σ σo x.st.x ∧ (∀ i < 13, σ'.r i = σo.r i) ∧ σ'.sp = σo.sp)

/-- The steps of a function from the given address to a return, the last one leading to
    the final state `σf`. -/
def DChainL (R : Nat → MState → MState → Int → Prop) (frame : Bool) (c : Code) (SP0 n : Nat) :
    Option Nat → List DStep → MState → Prop
  | some a, [x], σf => x.st.a = a ∧ x.st.next = none ∧ StepL R frame c SP0 n x σf
  | some a, x :: y :: t, σf =>
      x.st.a = a ∧ StepL R frame c SP0 n x y.σ ∧ DChainL R frame c SP0 n x.st.next (y :: t) σf
  | _, _, _ => False

/-- Runs of the linked semantics of the function at entry `e`, from `σi` to `σo`, of cost
    `total`, with calls nested less than `d` deep. -/
def DRunL (mul : Nat) (c : Code) (fs : List BFun) (Ls : List DFun) :
    Nat → Nat → MState → MState → Int → Prop
  | 0, _, _, _, _ => False
  | d + 1, e, σi, σo, total => ∃ f L x t, dfAt fs Ls e = some (f, L) ∧ x.σ = σi ∧
      DChainL (DRunL mul c fs Ls d) L.frame c σi.sp (saveN c e) (some e) (x :: t) σo ∧
      XChain c (x :: t) ∧
      (∀ y ∈ x :: t, DOkM mul c f.jumps y.st.a y.j y.σ y.st.next y.st.w y.st.calls) ∧
      (∀ r ∈ L.trusted, ((x :: t).map fun y => coefPair r.coef y.st.a y.st.next).sum ≤ r.rhs) ∧
      total = ((x :: t).map fun y => (y.st.w : Int) + y.st.x).sum

theorem dchainL_mchain {R : Nat → MState → MState → Int → Prop} {frame : Bool} {c : Code}
    {SP0 n : Nat} : ∀ (s : List DStep) (o : Option Nat) (σf : MState),
      DChainL R frame c SP0 n o s σf → MChain o (s.map (·.st))
  | [], o, _, h => by cases o <;> simp [DChainL] at h
  | [x], o, σf, h => by
    cases o with
    | none => simp [DChainL] at h
    | some a =>
      obtain ⟨hxa, hn, _⟩ := h
      refine ⟨hxa, ?_⟩
      simp only [List.map_nil]
      rw [hn]; trivial
  | x :: z :: t, o, σf, h => by
    cases o with
    | none => simp [DChainL] at h
    | some a =>
      obtain ⟨hxa, _, hrest⟩ := h
      exact ⟨hxa, dchainL_mchain (z :: t) x.st.next σf hrest⟩

/-! ### Outside `BL`, the effects do not depend on the assumption -/

/-- The first halfword of a 32-bit instruction. -/
def isWide (h : Nat) : Prop := h >>> 11 = 0b11101 ∨ h >>> 11 = 0b11110 ∨ h >>> 11 = 0b11111

theorem effect_narrow {c : Code} {a h : Nat} (hc : c.get a = some h) (hw : ¬ isWide h) :
    effect true c a = effect false c a := by
  unfold isWide at hw; unfold effect; rw [hc]; simp only []; rw [ite_eq_right hw, ite_eq_right hw]

theorem stackEffect_narrow {c : Code} {a h : Nat} (hc : c.get a = some h) (hw : ¬ isWide h) :
    stackEffect true c a = stackEffect false c a := by
  unfold isWide at hw; unfold stackEffect; rw [hc]; simp only []; rw [ite_eq_right hw, ite_eq_right hw]

/-- A step allowed at a 32-bit instruction is a call of one function. -/
theorem wide_call {mul : Nat} {c : Code} {J : List JT} {a j : Nat} {σ : MState} {next : Option Nat} {w : Nat}
    {calls : List Nat} {h : Nat} (hok : DOkM mul c J a j σ next w calls) (hc : c.get a = some h)
    (hw : isWide h) (hJ : farAt J a = false) : ∃ t, calls = [t] := by
  obtain ⟨_, _, i, hi, hcase⟩ := hok
  rw [transF_of J i a hJ] at hcase
  unfold isWide at hw
  rcases hcase with ⟨htr, _⟩ | ⟨_, add, m, hpw, _⟩
  swap
  · exfalso
    unfold pcWrite at hpw
    rw [hc] at hpw
    by_cases hcnd : (h >>> 8 = 0b01000100 ∨ h >>> 8 = 0b01000110)
    · simp only [Nat.shiftRight_eq_div_pow] at hcnd hw
      omega
    · simp [hcnd] at hpw
  unfold decode at hi
  rw [hc] at hi
  simp only [] at hi
  rw [ite_eq_left hw] at hi
  split at hi
  · cases hi
  · split at hi
    · split at hi
      · cases hi
        rcases j with _ | j <;> simp [trans] at htr
        exact ⟨_, htr.2.2.symm⟩
      · cases hi; simp [trans, stopI] at htr
    · cases hi; simp [trans, stopI] at htr

/-- The calls of a step: none or one. -/
theorem trans_calls (i : Insn) (a : Nat) (p : Option Nat × Nat × List Nat) (hp : p ∈ trans i a) :
    p.2.2 = [] ∨ ∃ t, p.2.2 = [t] := by
  unfold trans at hp
  split at hp <;> simp at hp <;> rcases hp with rfl | rfl <;> simp

theorem transF_calls (J : List JT) (i : Insn) (a : Nat) (p : Option Nat × Nat × List Nat)
    (hp : p ∈ transF J i a) : p.2.2 = [] ∨ ∃ t, p.2.2 = [t] := by
  unfold transF at hp
  split at hp
  · split at hp
    · simp at hp; subst hp; simp
    · exact trans_calls i a p hp
  · exact trans_calls i a p hp

theorem calls_cases {mul : Nat} {c : Code} {J : List JT} {a j : Nat} {σ : MState} {next : Option Nat} {w : Nat}
    {calls : List Nat} (hok : DOkM mul c J a j σ next w calls) : calls = [] ∨ ∃ t, calls = [t] := by
  obtain ⟨_, _, i, _, hcase⟩ := hok
  rcases hcase with ⟨htr, _⟩ | ⟨_, _, _, _, _, _, hc⟩
  · exact transF_calls J i a _ (List.mem_of_getElem? htr)
  · exact Or.inl hc

/-- A function whose calling convention is checked has no far branch. -/
theorem convOk_nofar {mul : Nat} {c : Code} {f : BFun} {L : DFun} (h : convOk mul c f L = true)
    (a : Nat) : farAt f.jumps a = false := by
  unfold convOk at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
  unfold farAt
  simp only [List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and]
  intro t ht hf
  exact absurd hf (h.1.1 t ht)

/-! ### From the linked semantics to the semantics with the assumption -/

/-- What a callee guarantees: `r4`-`r11` and SP are restored. -/
def Preserves (σ σo : MState) : Prop := (∀ i, 4 ≤ i → i < 12 → σo.r i = σ.r i) ∧ σo.sp = σ.sp

theorem effect_wide {c : Code} {a h : Nat} (hc : c.get a = some h) (hw : isWide h) :
    effect true c a = ⟨anyRegs [0, 1, 2, 3, 12], .any⟩ := by
  unfold isWide at hw; unfold effect; rw [hc]; simp only []; rw [ite_eq_left hw]; simp

theorem stackEffect_wide {c : Code} {a h : Nat} (hc : c.get a = some h) (hw : isWide h) (abi : Bool) :
    stackEffect abi c a = ⟨if abi then .keep else .any, .other, none, false⟩ := by
  unfold isWide at hw; unfold stackEffect; rw [hc]; simp only []; rw [ite_eq_left hw]

/-- A step of the linked semantics is a step with the assumption on callees, when the
    callees preserve `r4`-`r11` and SP. -/
theorem stepL_step {R : Nat → MState → MState → Int → Prop} {frame : Bool} {c : Code}
    {SP0 n mul : Nat} {x : DStep} {σ' : MState}
    (hR : ∀ g σ σo k, R g σ σo k → Preserves σ σo)
    {J : List JT} (hs : StepL R frame c SP0 n x σ') (hok : DOkM mul c J x.st.a x.j x.σ x.st.next x.st.w x.st.calls)
    (hJ : farAt J x.st.a = false) :
    EffOk (effect true c x.st.a) x.σ σ' ∧ StackOk frame SP0 (stackEffect true c x.st.a) x.σ σ' := by
  obtain ⟨he, hst, _, _, _, hlink⟩ := hs
  cases hc : c.get x.st.a with
  | none =>
    have e1 : effect true c x.st.a = effect false c x.st.a := by unfold effect; rw [hc]
    have e2 : stackEffect true c x.st.a = stackEffect false c x.st.a := by
      unfold stackEffect; rw [hc]
    rw [e1, e2]; exact ⟨he, hst⟩
  | some h =>
    by_cases hw : isWide h
    · obtain ⟨g, hg⟩ := wide_call hok hc hw hJ
      obtain ⟨σo, hRo, hr, hsp⟩ := hlink g hg
      obtain ⟨hpr, hspr⟩ := hR _ _ _ _ hRo
      rw [effect_wide hc hw, stackEffect_wide hc hw true]
      rw [stackEffect_wide hc hw false] at hst
      obtain ⟨hwf, _, _, _⟩ := he
      refine ⟨⟨hwf, ?_, ?_, ?_⟩, ?_⟩
      · intro i hi hfind
        have h4 : 4 ≤ i ∧ i < 12 := by
          simp [anyRegs] at hfind
          omega
        rw [hr i hi, hpr i h4.1 h4.2]
      · intro i _ p hp v hv
        have hm := List.mem_of_find?_eq_some hp
        simp only [anyRegs, List.mem_map] at hm
        obtain ⟨_, _, rfl⟩ := hm
        simp [valOf] at hv
      · simp [flagsOfE]
      · simp only [StackOk] at hst ⊢
        obtain ⟨hws, _, hmem, hload⟩ := hst
        exact ⟨hws, by simp only [ite_true]; rw [hsp, hspr], hmem, hload⟩
    · rw [effect_narrow hc hw, stackEffect_narrow hc hw]; exact ⟨he, hst⟩

/-- A chain of the linked semantics is a chain with the assumption on callees. -/
theorem chainL_chain {R : Nat → MState → MState → Int → Prop} {frame : Bool} {c : Code}
    {SP0 n mul : Nat} {J : List JT} (hR : ∀ g σ σo k, R g σ σo k → Preserves σ σo) :
    ∀ (s : List DStep) (a : Nat) (σf : MState), DChainL R frame c SP0 n (some a) s σf →
      (∀ y ∈ s, DOkM mul c J y.st.a y.j y.σ y.st.next y.st.w y.st.calls) →
      (∀ y ∈ s, farAt J y.st.a = false) →
      DChain true frame c SP0 (some a) s
  | [], _, _, h, _, _ => by simp [DChainL] at h
  | [x], a, σf, h, _, _ => by
    obtain ⟨hxa, hn, _⟩ := h
    refine ⟨hxa, by simp, ?_⟩
    rw [hn]; trivial
  | x :: y :: t, a, σf, h, hok, hfar => by
    obtain ⟨hxa, hs, hrest⟩ := h
    have hstep := stepL_step hR hs (hok x (by simp)) (hfar x (by simp))
    refine ⟨hxa, ?_, ?_⟩
    · intro z hz
      simp at hz
      subst hz
      rw [← hxa]; exact hstep
    · cases hn : x.st.next with
      | none => rw [hn] at hrest; simp [DChainL] at hrest
      | some b =>
        rw [hn] at hrest
        exact chainL_chain hR (y :: t) b σf hrest (fun z hz => hok z (List.mem_cons_of_mem _ hz))
          (fun z hz => hfar z (List.mem_cons_of_mem _ hz))

/-! ### Register lists -/

theorem bit_low (h k : Nat) (hk : k < 8) : ((h % 256) >>> k) % 2 = (h >>> k) % 2 := by
  simp only [Nat.shiftRight_eq_div_pow]
  interval_cases k <;> omega

theorem rank_low (h k : Nat) (hk : k < 8) : rankBits (h % 256) k = rankBits h k := by
  unfold rankBits
  congr 1
  interval_cases k <;> omega

theorem popcount_low (h : Nat) : popcount8 (h % 256) = popcount8 h := by
  simp only [popcount8, List.range, List.range.loop, List.foldl, Nat.shiftRight_eq_div_pow]
  omega

theorem rank_lt (h k : Nat) (hk : k < 8) (hb : (h >>> k) % 2 = 1) :
    rankBits h k + 1 ≤ popcount8 h := by
  simp only [rankBits, popcount8, List.range, List.range.loop, List.foldl,
    Nat.shiftRight_eq_div_pow] at *
  interval_cases k <;> simp at * <;> omega

theorem mem_lowList (h k : Nat) : k ∈ lowList h ↔ k < 8 ∧ (h >>> k) % 2 = 1 := by
  simp only [lowList, List.mem_filter, List.mem_range, decide_eq_true_eq]

/-! ### The effects of `PUSH`, `POP` and `BX` -/

/-- The shifts of a halfword in a range of `2^9` values. -/
theorem shifts9 (h q : Nat) (hq : h >>> 9 = q) :
    h >>> 11 = q / 4 ∧ h >>> 12 = q / 8 ∧ h >>> 13 = q / 16 ∧ h >>> 10 = q / 2 ∧
      (h >>> 8 = 2 * q ∨ h >>> 8 = 2 * q + 1) := by
  simp only [Nat.shiftRight_eq_div_pow] at *
  omega

theorem effect_push {abi : Bool} {c : Code} {a h : Nat} (hc : c.get a = some h)
    (hp : isPushH h = true) : (effect abi c a).dst = [] := by
  simp only [isPushH, beq_iff_eq] at hp
  obtain ⟨h11, h12, h13, h10, h8 | h8⟩ := shifts9 h _ hp <;>
    simp [effect, hc, h11, h12, h13, h10, h8, hp]

theorem stackEffect_push_mem {abi : Bool} {c : Code} {a h : Nat} (hc : c.get a = some h)
    (hp : isPushH h = true) :
    (stackEffect abi c a).mem = .push (popcount8 h + (h >>> 8) % 2) := by
  simp only [isPushH, beq_iff_eq] at hp
  obtain ⟨h11, h12, h13, h10, h8 | h8⟩ := shifts9 h _ hp <;>
    simp [stackEffect, hc, h11, h12, h8, hp]

theorem effect_pop {abi : Bool} {c : Code} {a h : Nat} (hc : c.get a = some h)
    (hp : h >>> 9 = 0b1011110) : (effect abi c a).dst = anyRegs (lowList h) := by
  obtain ⟨h11, h12, h13, h10, h8 | h8⟩ := shifts9 h _ hp <;>
    simp [effect, hc, h11, h12, h13, h10, h8, hp]

theorem stackEffect_pop {abi : Bool} {c : Code} {a h : Nat} (hc : c.get a = some h)
    (hp : h >>> 9 = 0b1011110) :
    (stackEffect abi c a).sp = .add (((4 * (popcount8 h + (h >>> 8) % 2) : Nat) : Int)) := by
  obtain ⟨h11, h12, h13, h10, h8 | h8⟩ := shifts9 h _ hp <;>
    simp [stackEffect, hc, h11, h12, h8, hp]

theorem effect_bx {abi : Bool} {c : Code} {a h : Nat} (hc : c.get a = some h)
    (hb : h >>> 8 = 0b01000111) : (effect abi c a).dst = [] := by
  have h9 : h >>> 9 = 35 := by simp only [Nat.shiftRight_eq_div_pow] at *; omega
  obtain ⟨h11, h12, h13, h10, _⟩ := shifts9 h _ h9
  simp [effect, hc, h11, h10, hb]

theorem stackEffect_bx {abi : Bool} {c : Code} {a h : Nat} (hc : c.get a = some h)
    (hb : h >>> 8 = 0b01000111) : (stackEffect abi c a).sp = .keep := by
  have h9 : h >>> 9 = 35 := by simp only [Nat.shiftRight_eq_div_pow] at *; omega
  obtain ⟨h11, h12, h13, h10, _⟩ := shifts9 h _ h9
  simp [stackEffect, hc, h11, h12, h10, hb, h9]

/-! ### Small facts -/

theorem popcount_le (h : Nat) : popcount8 h ≤ 8 := by
  simp only [popcount8, List.range, List.range.loop, List.foldl]
  omega

theorem stackEffect_mem_same (c : Code) (a : Nat) :
    (stackEffect true c a).mem = (stackEffect false c a).mem := by
  cases hc : c.get a with
  | none => unfold stackEffect; rw [hc]
  | some h =>
    by_cases hw : isWide h
    · rw [stackEffect_wide hc hw true, stackEffect_wide hc hw false]
    · rw [stackEffect_narrow hc hw]

theorem decode_get {mul : Nat} {c : Code} {a : Nat} {i : Insn} (hd : decode mul c a = some i) :
    ∃ h, c.get a = some h := by
  unfold decode at hd
  cases hc : c.get a with
  | none => rw [hc] at hd; cases hd
  | some h => exact ⟨h, rfl⟩

/-- A transition to no successor is a return. -/
theorem trans_none {i : Insn} {a : Nat} {w : Nat} {calls : List Nat}
    (h : (none, w, calls) ∈ trans i a) : i.kind = .ret := by
  cases hk : i.kind <;> simp [trans, hk] at h ⊢

/-- A return has no successor. -/
theorem trans_ret {i : Insn} {a b : Nat} {w : Nat} {calls : List Nat} (hk : i.kind = .ret)
    (h : (some b, w, calls) ∈ trans i a) : False := by
  simp [trans, hk] at h

/-- The stack pointer follows its offsets. -/
theorem sp_next {da dn : Option Int} {frame : Bool} {SP0 SP1 : Nat} {st : StackE} {σ σ' : MState}
    (hok : spOk da st.sp dn = true) (hσ : ∀ d, da = some d → σ.sp = aOf ((SP0 : Int) + d))
    (hst : StackOk frame SP1 st σ σ') :
    ∀ d, dn = some d → σ'.sp = aOf ((SP0 : Int) + d) := by
  intro d hd
  subst hd
  obtain ⟨_, hspm, _, _⟩ := hst
  cases da with
  | none => cases he : st.sp <;> rw [he] at hok <;> simp [spOk] at hok
  | some d0 =>
    have h0 := hσ d0 rfl
    cases he : st.sp with
    | keep =>
      rw [he] at hok hspm; simp [spOk] at hok; rw [hspm, h0, hok]
    | add k =>
      rw [he] at hok hspm
      simp [spOk] at hok
      rw [hspm, h0, hok]
      simp only [aOf, U]
      omega
    | any => rw [he] at hok; simp [spOk] at hok

/-! ### A function that keeps the convention restores `r4`-`r11` and SP -/

/-- The invariant at instruction `a` in state `σ`, for a run entered in `σi`: SP follows its
    offsets; the registers of `r4`-`r7` not saved keep their entry values (all of them at the
    entry); after the entry, the saved words hold the entry values of the saved registers;
    `r8`-`r11` keep their entry values. -/
def ConvInv (c : Code) (f : BFun) (L : DFun) (σi : MState) (a : Nat) (σ : MState) : Prop :=
  a ∈ f.nodes ∧
  (∀ d, spAt f L a = some d → σ.sp = aOf ((σi.sp : Int) + d)) ∧
  (∀ k, 4 ≤ k → k < 8 → (a = f.entry ∨ (saveList c f.entry >>> k) % 2 = 0) → σ.r k = σi.r k) ∧
  (a ≠ f.entry → ∀ k, 4 ≤ k → k < 8 → (saveList c f.entry >>> k) % 2 = 1 →
    σ.mem (savedAddr σi.sp (saveN c f.entry) (rankBits (saveList c f.entry) k)) = σi.r k) ∧
  (∀ k, 8 ≤ k → k < 12 → σ.r k = σi.r k)

/-- The saved list, at an entry that pushes. -/
theorem save_push {c : Code} {e h : Nat} (hc : c.get e = some h) (hp : isPushH h = true) :
    saveList c e = h % 256 ∧ saveN c e = popcount8 h + (h >>> 8) % 2 := by
  simp [saveList, saveN, hc, hp]

/-- At an entry that does not push, nothing is saved. -/
theorem save_nopush {c : Code} {e : Nat} (hp : ∀ h, c.get e = some h → isPushH h = false) :
    saveList c e = 0 ∧ saveN c e = 0 := by
  cases hc : c.get e with
  | none => simp [saveList, saveN, hc]
  | some h => simp [saveList, saveN, hc, hp h hc]

/-- A saved register has a saved word. -/
theorem rank_lt_saveN {c : Code} {e k : Nat} (hk : k < 8)
    (hb : (saveList c e >>> k) % 2 = 1) : rankBits (saveList c e) k < saveN c e := by
  cases hc : c.get e with
  | none => simp [saveList, hc] at hb
  | some h =>
    by_cases hp : isPushH h = true
    · obtain ⟨hl, hn⟩ := save_push hc hp
      rw [hl] at hb ⊢; rw [hn]
      have := rank_lt (h % 256) k hk hb
      rw [popcount_low] at this
      omega
    · simp [saveList, hc, hp] at hb

theorem find_none_of {l : List (Nat × Val)} {k : Nat} (h : ∀ p ∈ l, p.1 ≠ k) :
    l.find? (fun p => p.1 == k) = none := by
  rw [List.find?_eq_none]
  intro p hp
  simpa using h p hp

theorem saveN_le (c : Code) (e : Nat) : saveN c e ≤ 9 := by
  have := popcount_le
  cases hc : c.get e with
  | none => simp [saveN, hc]
  | some h =>
    simp only [saveN, hc]
    split
    · have := popcount_le h; omega
    · omega

/-- **One step keeps the invariant.** -/
theorem conv_step {mul : Nat} {c : Code} {f : BFun} {L : DFun}
    {R : Nat → MState → MState → Int → Prop} {σi : MState} {a b : Nat} {x : DStep} {σ' : MState}
    (hcd : checkDFun mul true c f L = true) (hcv : convOk mul c f L = true)
    (hR : ∀ g σ σo k, R g σ σo k → Preserves σ σo) (hSP0 : σi.sp < U)
    (hJ : ConvInv c f L σi a x.σ) (hxa : x.st.a = a)
    (hs : StepL R L.frame c σi.sp (saveN c f.entry) x σ')
    (hokM : DOkM mul c f.jumps x.st.a x.j x.σ x.st.next x.st.w x.st.calls) (hg : Good mul c f x)
    (hn : x.st.next = some b) :
    ConvInv c f L σi b σ' := by
  obtain ⟨hcl, _, _, hnodes, _, _, hslok, _⟩ := checkDFun_spec hcd
  obtain ⟨ha, hsp, hregs, hslots, hhi⟩ := hJ
  obtain ⟨heff, hst⟩ := stepL_step hR hs hokM (convOk_nofar hcv _)
  obtain ⟨_, _, hpp, hsafe, _, _⟩ := hs
  obtain ⟨_, _, _, _, i, hdec, htr, _⟩ := hg
  rw [hxa] at hdec htr heff hst hpp hsafe
  have hmem : (x.st.next, x.st.w, x.st.calls) ∈ transJ f.jumps i a := List.mem_of_getElem? htr
  rw [hn] at hmem
  obtain ⟨h, hget⟩ := decode_get hdec
  have hb : b ∈ f.nodes := by
    obtain ⟨_, hcl2⟩ := closed_spec mul c f.jumps f.entry f.nodes hcl
    obtain ⟨i', hi', _, hsucc⟩ := hcl2 a ha
    rw [hdec] at hi'; cases hi'
    exact hsucc _ hmem b rfl
  have hcv' := hcv
  simp only [convOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hcv'
  have hcn := hcv'.2 a ha
  simp only [convNode, hdec, hget, Bool.and_eq_true, List.all_eq_true] at hcn
  obtain ⟨hne, hcase⟩ := hcn
  have hbe : b ≠ f.entry := by
    have := hne _ hmem; simpa using this
  have hnr : i.kind ≠ .ret := by
    intro hk
    have hc2 := hcase
    rw [ite_eq_left (by simp [hk])] at hc2
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hc2
    have hm2 : (some b, x.st.w, x.st.calls) ∈ trans i a := by
      simpa [transJ, hc2.1, transF_of _ _ _ (convOk_nofar hcv a)] using hmem
    exact trans_ret hk hm2
  rw [ite_eq_right (by simpa using hnr)] at hcase
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcase
  obtain ⟨_, _, i', hi', hspok⟩ := nodeOk_spec (hnodes a ha)
  rw [hdec] at hi'; cases hi'
  have hspb := sp_next (hspok _ hmem b rfl).2 hsp hst
  have hn9 := saveN_le c f.entry
  by_cases hpush : a = f.entry ∧ isPushH h = true
  · -- the entry pushes: the saved words get the entry values
    obtain ⟨hae, hph⟩ := hpush
    have hpe : c.get f.entry = some h := hae ▸ hget
    obtain ⟨hl, hnn⟩ := save_push hpe hph
    have hx0 : x.σ.sp = σi.sp := by
      have := hsp 0 (hae ▸ hcv'.1.2)
      rw [this]; simp only [aOf, U] at *; omega
    have hd : (effect true c a).dst = [] := effect_push hget hph
    refine ⟨hb, hspb, ?_, ?_, ?_⟩
    · intro k hk4 hk8 _
      rw [heff.2.1 k (by omega) (by rw [hd]; rfl)]
      exact hregs k hk4 hk8 (Or.inl hae)
    · intro _ k hk4 hk8 hbit
      rw [hl] at hbit ⊢
      rw [bit_low h k hk8] at hbit
      rw [rank_low h k hk8, hnn]
      have hw := (show PushPopOk c a x.σ σ' from hpp)
      simp only [PushPopOk, hget] at hw
      have := hw.1 hph k hk8 hbit
      rw [hx0] at this
      rw [← hregs k hk4 hk8 (Or.inl hae), ← this]
      simp only [savedAddr]
      congr 2
    · intro k hk8 hk12
      rw [heff.2.1 k (by omega) (by rw [hd]; rfl)]
      exact hhi k hk8 hk12
  · have hgen := hcase.resolve_left (by
      intro h'; exact hpush ⟨h'.1, h'.2⟩)
    obtain ⟨hdst, hmemc⟩ := hgen
    refine ⟨hb, hspb, ?_, ?_, ?_⟩
    · intro k hk4 hk8 hor
      have hbit : (saveList c f.entry >>> k) % 2 = 0 := hor.resolve_left hbe
      have hnone : (effect true c a).dst.find? (fun p => p.1 == k) = none := by
        apply find_none_of
        intro p hp hpk
        have := hdst p hp
        rw [hpk] at this
        simp only [decide_eq_true_eq] at this
        omega
      rw [heff.2.1 k (by omega) hnone]
      exact hregs k hk4 hk8 (Or.inr hbit)
    · intro _ k hk4 hk8 hbit
      have hr := rank_lt_saveN hk8 hbit
      by_cases hae : a = f.entry
      · -- an entry that does not push saves nothing
        have hnp : ∀ h', c.get f.entry = some h' → isPushH h' = false := by
          intro h' hh'
          rw [← hae, hget] at hh'
          cases hh'
          cases hp' : isPushH h
          · rfl
          · exact absurd ⟨hae, hp'⟩ hpush
        rw [(save_nopush hnp).1] at hbit
        simp at hbit
      have hold := hslots hae k hk4 hk8 hbit
      rw [← hold]
      cases hm : (stackEffect true c a).mem with
      | keep =>
        have := hst.2.2.1; rw [hm] at this; exact this _
      | storeSP imm rt =>
        rw [hm] at hmemc
        have hstm := hst.2.2.1; rw [hm] at hstm
        cases hd : spAt f L a with
        | none => rw [hd] at hmemc; simp at hmemc
        | some d =>
          rw [hd] at hmemc
          simp only [decide_eq_true_eq] at hmemc
          have hx := hsp d hd
          have hbd := (spAt_bound hslok a d hd).1
          apply hstm.2
          rw [hx]
          simp only [savedAddr, aOf, U] at *
          omega
      | push m =>
        rw [hm] at hmemc
        simp only [Bool.and_eq_true] at hmemc
        obtain ⟨hph, hmc⟩ := hmemc
        have hstm := hst.2.2.1; rw [hm] at hstm
        have hm' := stackEffect_push_mem (abi := true) hget hph
        rw [hm] at hm'
        cases hm'
        have hpc := popcount_le h
        cases hd : spAt f L a with
        | none => rw [hd] at hmc; simp at hmc
        | some d =>
          rw [hd] at hmc
          simp only [decide_eq_true_eq] at hmc
          have hx := hsp d hd
          have hbd := (spAt_bound hslok a d hd).1
          apply hstm
          intro j hj
          rw [hx]
          simp only [savedAddr, aOf, U] at *
          omega
      | other =>
        exact hsafe (by rw [← stackEffect_mem_same]; exact hm) _ hr
    · intro k hk8 hk12
      have hnone : (effect true c a).dst.find? (fun p => p.1 == k) = none := by
        apply find_none_of
        intro p hp hpk
        have := hdst p hp
        rw [hpk] at this
        simp only [decide_eq_true_eq] at this
        omega
      rw [heff.2.1 k (by omega) hnone]
      exact hhi k hk8 hk12

/-- An entry that saves `lr` pushes. -/
theorem saveLr_push {c : Code} {e : Nat} (h : saveLr c e = true) :
    ∃ h0, c.get e = some h0 ∧ isPushH h0 = true ∧ (h0 >>> 8) % 2 = 1 := by
  cases hc : c.get e with
  | none => simp [saveLr, hc] at h
  | some h0 =>
    simp only [saveLr, hc, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h0, rfl, h.1, h.2⟩

/-- **At a return, `r4`-`r11` and SP are back.** -/
theorem conv_ret {mul : Nat} {c : Code} {f : BFun} {L : DFun}
    {R : Nat → MState → MState → Int → Prop} {σi : MState} {a : Nat} {x : DStep} {σf : MState}
    (hcv : convOk mul c f L = true)
    (hR : ∀ g σ σo k, R g σ σo k → Preserves σ σo) (hSP0 : σi.sp < U)
    (hJ : ConvInv c f L σi a x.σ) (hxa : x.st.a = a)
    (hs : StepL R L.frame c σi.sp (saveN c f.entry) x σf)
    (hokM : DOkM mul c f.jumps x.st.a x.j x.σ x.st.next x.st.w x.st.calls) (hg : Good mul c f x)
    (hn : x.st.next = none) :
    Preserves σi σf := by
  obtain ⟨ha, hsp, hregs, hslots, hhi⟩ := hJ
  obtain ⟨heff, hst⟩ := stepL_step hR hs hokM (convOk_nofar hcv _)
  obtain ⟨_, _, hpp, _, _, _⟩ := hs
  obtain ⟨_, _, _, _, i, hdec, htr, _⟩ := hg
  rw [hxa] at hdec htr heff hst hpp
  have hmemJ : (x.st.next, x.st.w, x.st.calls) ∈ transJ f.jumps i a := List.mem_of_getElem? htr
  rw [hn] at hmemJ
  have hmem : (none, x.st.w, x.st.calls) ∈ trans i a := by
    simp only [transJ, List.mem_append] at hmemJ
    rcases hmemJ with h | h
    · rwa [transF_of _ _ _ (convOk_nofar hcv a)] at h
    · exfalso
      unfold jumpTr at h
      split at h <;> simp at h
  have hk := trans_none hmem
  obtain ⟨h, hget⟩ := decode_get hdec
  have hcv' := hcv
  simp only [convOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hcv'
  have hcn := hcv'.2 a ha
  simp only [convNode, hdec, hget, Bool.and_eq_true, List.all_eq_true] at hcn
  obtain ⟨_, hcase⟩ := hcn
  rw [ite_eq_left (by simp [hk])] at hcase
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcase
  have hn9 := saveN_le c f.entry
  rcases hcase.2 with ⟨⟨⟨⟨hpop, hpc⟩, hlist⟩, hlr⟩, hspa⟩ | ⟨⟨hbx, hn0⟩, hspa⟩
  · -- `POP {..., pc}`
    obtain ⟨h0, hge, hp0, hl0⟩ := saveLr_push hlr
    obtain ⟨hl, hnn⟩ := save_push hge hp0
    have hae : a ≠ f.entry := by
      intro hae
      rw [hae, hge] at hget
      cases hget
      simp only [isPushH, beq_iff_eq] at hp0
      omega
    have hx := hsp _ hspa
    refine ⟨fun k hk4 hk12 => ?_, ?_⟩
    · by_cases hk8 : ¬ k < 8
      · have hnone : (effect true c a).dst.find? (fun p => p.1 == k) = none := by
          rw [effect_pop hget hpop]
          apply find_none_of
          intro p hp hpk
          simp only [anyRegs, List.mem_map] at hp
          obtain ⟨j, hj, rfl⟩ := hp
          have := ((mem_lowList h j).mp hj).1
          simp only at hpk
          omega
        rw [heff.2.1 k (by omega) hnone]
        exact hhi k (by omega) hk12
      have hk8 : k < 8 := by omega
      by_cases hb : (saveList c f.entry >>> k) % 2 = 1
      · have hbh : (h >>> k) % 2 = 1 := by rw [← bit_low h k hk8, hlist]; exact hb
        have hw := (show PushPopOk c a x.σ σf from hpp)
        simp only [PushPopOk, hget] at hw
        rw [hw.2 hpop k hk8 hbh, ← hslots hae k hk4 hk8 hb, ← rank_low h k hk8, hlist, hx]
        have hr := rank_lt_saveN hk8 hb
        congr 1
        simp only [savedAddr, aOf, U] at *
        omega
      · have hb0 : (saveList c f.entry >>> k) % 2 = 0 := by omega
        have hnone : (effect true c a).dst.find? (fun p => p.1 == k) = none := by
          rw [effect_pop hget hpop]
          apply find_none_of
          intro p hp hpk
          simp only [anyRegs, List.mem_map] at hp
          obtain ⟨j, hj, rfl⟩ := hp
          simp only at hpk
          subst hpk
          have := ((mem_lowList h j).mp hj).2
          rw [← bit_low h j hk8, hlist] at this
          omega
        rw [heff.2.1 k (by omega) hnone]
        exact hregs k hk4 hk8 (Or.inr hb0)
    · have hspm := hst.2.1
      rw [stackEffect_pop hget hpop] at hspm
      simp only at hspm
      rw [hspm, hx, hnn, hpc]
      have hpl : popcount8 h = popcount8 h0 := by
        rw [← popcount_low h, hlist, hl, popcount_low]
      rw [hpl]
      simp only [aOf, U] at *
      omega
  · -- `BX LR`, nothing saved
    have hx := hsp _ hspa
    refine ⟨fun k hk4 hk12 => ?_, ?_⟩
    · by_cases hk8 : ¬ k < 8
      · have hnone : (effect true c a).dst.find? (fun p => p.1 == k) = none := by
          rw [effect_bx hget hbx]; rfl
        rw [heff.2.1 k (by omega) hnone]
        exact hhi k (by omega) hk12
      have hk8 : k < 8 := by omega
      have hb0 : (saveList c f.entry >>> k) % 2 = 0 := by
        by_contra hb
        have := rank_lt_saveN (e := f.entry) (c := c) hk8 (by omega)
        omega
      have hnone : (effect true c a).dst.find? (fun p => p.1 == k) = none := by
        rw [effect_bx hget hbx]; rfl
      rw [heff.2.1 k (by omega) hnone]
      exact hregs k hk4 hk8 (Or.inr hb0)
    · have hspm := hst.2.1
      rw [stackEffect_bx hget hbx] at hspm
      simp only at hspm
      rw [hspm, hx]
      simp only [aOf, U] at *
      omega

/-- **Along a run of the function, the convention holds at the return.** -/
theorem conv_chain {mul : Nat} {c : Code} {f : BFun} {L : DFun}
    {R : Nat → MState → MState → Int → Prop} {σi σf : MState}
    (hcd : checkDFun mul true c f L = true) (hcv : convOk mul c f L = true)
    (hR : ∀ g σ σo k, R g σ σo k → Preserves σ σo) (hSP0 : σi.sp < U) :
    ∀ (x : DStep) (t : List DStep) (a : Nat),
      DChainL R L.frame c σi.sp (saveN c f.entry) (some a) (x :: t) σf →
      (∀ y ∈ x :: t, DOkM mul c f.jumps y.st.a y.j y.σ y.st.next y.st.w y.st.calls) →
      (∀ y ∈ x :: t, Good mul c f y) →
      ConvInv c f L σi a x.σ → Preserves σi σf
  | x, [], a, h, hok, hg, hJ => by
    obtain ⟨hxa, hn, hs⟩ := h
    exact conv_ret hcv hR hSP0 hJ hxa hs (hok x (by simp)) (hg x (by simp)) hn
  | x, y :: t, a, h, hok, hg, hJ => by
    obtain ⟨hxa, hs, hrest⟩ := h
    cases hn : x.st.next with
    | none => rw [hn] at hrest; simp [DChainL] at hrest
    | some b =>
      rw [hn] at hrest
      have hJ' := conv_step hcd hcv hR hSP0 hJ hxa hs (hok x (by simp)) (hg x (by simp)) hn
      exact conv_chain hcd hcv hR hSP0 y t b hrest (fun z hz => hok z (List.mem_cons_of_mem _ hz))
        (fun z hz => hg z (List.mem_cons_of_mem _ hz)) hJ'

/-! ### Runs of the linked semantics -/

/-- Every step of a chain is a step of the linked semantics. -/
theorem chainL_steps {R : Nat → MState → MState → Int → Prop} {frame : Bool} {c : Code}
    {SP0 n : Nat} : ∀ (s : List DStep) (o : Option Nat) (σf : MState),
      DChainL R frame c SP0 n o s σf → ∀ y ∈ s, ∃ σ', StepL R frame c SP0 n y σ'
  | [], o, _, h => by cases o <;> simp [DChainL] at h
  | [x], o, σf, h => by
    cases o with
    | none => simp [DChainL] at h
    | some a =>
      obtain ⟨_, _, hs⟩ := h
      intro y hy; simp at hy; subst hy; exact ⟨σf, hs⟩
  | x :: z :: t, o, σf, h => by
    cases o with
    | none => simp [DChainL] at h
    | some a =>
      obtain ⟨_, hs, hrest⟩ := h
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨z.σ, hs⟩
      · exact chainL_steps (z :: t) x.st.next σf hrest y hy

theorem dfAt_conv {mul : Nat} {c : Code} {fs : List BFun} {Ls : List DFun}
    (hC : convAll mul c fs Ls = true) {e : Nat} {f : BFun} {L : DFun}
    (h : dfAt fs Ls e = some (f, L)) : convOk mul c f L = true := by
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
        simp only [convAll, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hC
        exact hC.2 (f', L') (List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hf, hl⟩))

/-- **A run of the linked semantics is a run with the assumption on callees, and returns
    with `r4`-`r11` and SP restored**, when the checker accepts the loop certificates (with the
    assumption) and the calling convention of every function. By induction on the depth of
    calls: the callees of a run satisfy the convention by the induction hypothesis, so that
    every call is a step of `ThumbData`'s semantics with the assumption. -/
theorem drunL_drun {mul : Nat} {c : Code} {fs : List BFun} {Ls : List DFun}
    (hD : checkData mul true c fs Ls = true) (hC : convAll mul c fs Ls = true) :
    ∀ d e σi σo tot, DRunL mul c fs Ls d e σi σo tot →
      DRun mul true c fs Ls d e σi tot ∧ Preserves σi σo := by
  intro d
  induction d with
  | zero => intro e σi σo tot h; simp [DRunL] at h
  | succ d ih =>
    intro e σi σo tot h
    obtain ⟨f, L, x, t, hdf, hxσ, hch, hX, hokM, htr, htot⟩ := h
    have hR : ∀ g σ σo k, DRunL mul c fs Ls d g σ σo k → Preserves σ σo :=
      fun g σ σo k h => (ih g σ σo k h).2
    obtain ⟨_, hcd, hentry⟩ := dfAt_spec hD hdf
    have hcv := dfAt_conv hC hdf
    have hchT := chainL_chain hR (x :: t) e σo hch hokM (fun _ _ => convOk_nofar hcv _)
    have hgood : ∀ y ∈ x :: t, Good mul c f y := by
      have hg := steps_good hcd (x :: t) (by rw [hentry]; simpa [headSp, hxσ] using hchT) hX hokM
      intro y hy
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hy
      exact hg k y hk
    have hSP0 : σi.sp < U := by rw [← hxσ]; exact (hokM x (by simp)).2.1.1
    refine ⟨⟨f, L, x :: t, hdf, ?_, hX, fun y hy i _ => ?_, ?_, htr, htot⟩, ?_⟩
    · simpa [headSp, hxσ] using hchT
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      rw [← hy, hxσ]
    · intro y hy
      refine ⟨hokM y hy, ?_⟩
      obtain ⟨σ', hs⟩ := chainL_steps (x :: t) (some e) σo hch y hy
      obtain ⟨_, _, _, _, hnil, hlink⟩ := hs
      rcases calls_cases (hokM y hy) with hc0 | ⟨g, hg⟩
      · rw [hc0]; exact hnil hc0
      · rw [hg]
        obtain ⟨σo', hRo, _, _⟩ := hlink g hg
        exact ⟨y.st.x, (ih g y.σ σo' y.st.x hRo).1, by simp [CallsWith]⟩
    · rw [← hentry] at hch
      have hJ : ConvInv c f L σi f.entry x.σ := by
        obtain ⟨hcl, _⟩ := checkDFun_spec hcd
        have hcv' := hcv
        simp only [convOk, Bool.and_eq_true, beq_iff_eq] at hcv'
        refine ⟨(closed_spec mul c f.jumps f.entry f.nodes hcl).1, ?_, ?_, ?_, ?_⟩
        · intro d hd
          rw [hcv'.1.2] at hd; cases hd
          rw [hxσ]; simp only [aOf, U] at *; omega
        · intro k _ _ _; rw [hxσ]
        · intro hne; exact absurd rfl hne
        · intro k _ _; rw [hxσ]
      exact conv_chain hcd hcv hR hSP0 x t f.entry hch hokM hgood hJ

/-- **Soundness on machine code without the assumption on callees**: if the checker accepts
    the cycle certificate, the loop certificates and the calling convention of every function,
    every run of the linked semantics of the function at entry `e` that starts with registers
    satisfying its precondition (none if its certificate gives none) costs at most its
    certified bound; the preconditions of the callees are proved at the calls. The loop rows
    left in `trusted` remain assumed; the callees' preservation of `r4`-`r11` and SP is
    proved, under the hypothesis `SaveSafe` (no stack smashing). -/
theorem data_sound_conv (mul : Nat) (c : Code) (fs : List BFun) (Cs : List Cert) (Ls : List DFun)
    (h : checkBinary mul c fs Cs true = true) (hD : checkData mul true c fs Ls = true)
    (hC : convAll mul c fs Ls = true)
    (d e i : Nat) (σi σo : MState) (tot : Int) (hrun : DRunL mul c fs Ls d e σi σo tot)
    (hpre : PreAt fs Ls e σi) (hfind : find (fs.map (·.entry)) e = some i) :
    tot ≤ ((Cs.map Cert.bound).getD i 0 : Nat) :=
  data_sound mul true c fs Cs Ls h hD d e i σi tot (drunL_drun hD hC d e σi σo tot hrun).1 hpre hfind

/-! ### Examples: the hypotheses are satisfiable, and the check refuses a broken convention -/

/-- The counting loop of `ThumbData` (`... bx lr`), with its offsets of SP. -/
def exDFunC : DFun := { exDFun with spOff := [some 0, some 0, some 0, some 0, some 0, some 0] }

theorem exConv_checks : convAll 32 exCode [exFunD] [exDFunC] = true := by decide

theorem exConvData_checks : checkData 32 true exCode [exFunD] [exDFunC] = true := by decide

/-- Every run of the linked semantics of the example costs at most 68 cycles. -/
theorem exConv_sound (d : Nat) (σi σo : MState) (tot : Int)
    (h : DRunL 32 exCode [exFunD] [exDFunC] d 0x100 σi σo tot) : tot ≤ 68 :=
  data_sound_conv 32 exCode [exFunD] [exCert] [exDFunC] exBinaryD_checks exConvData_checks
    exConv_checks d 0x100 0 σi σo tot h (preAt_nil _ _ _ _ (by decide)) (by decide)

/-- `push {r4, lr}; movs r4, #0; pop {r4, pc}`: saves `r4`, writes it, restores it. -/
def exSaveCode : Code := ⟨0x300, #[0xB510, 0x2400, 0xBD10]⟩
def exSaveFn : BFun := ⟨0x300, [0x300, 0x302, 0x304], [], []⟩
def exSaveD : DFun := { exDFun with spOff := [some 0, some (-8), some (-8)] }

theorem exSave_conv : convOk 32 exSaveCode exSaveFn exSaveD = true := by decide

/-- `movs r4, #0; bx lr`: writes `r4` without saving it; refused. -/
def exClobberCode : Code := ⟨0x300, #[0x2400, 0x4770]⟩
def exClobberFn : BFun := ⟨0x300, [0x300, 0x302], [], []⟩
def exClobberD : DFun := { exDFun with spOff := [some 0, some 0] }

theorem exClobber_refused : convOk 32 exClobberCode exClobberFn exClobberD = false := by decide

/-- The switch of `ThumbData` (`exSwCode`, a jump through a table, `bx lr` in every case):
    its convention is checked along the targets of the jump. -/
def exSwDC : DFun := { exSwD with spOff := List.replicate 10 (some 0) }

theorem exSwConv_checks : convAll 32 exSwCode [exSwFun] [exSwDC] = true := by decide

theorem exSwConvData_checks : checkData 32 true exSwCode [exSwFun] [exSwDC] = true := by decide

/-- Every run of the linked semantics of the switch costs at most 12 cycles. -/
theorem exSwConv_sound (d : Nat) (σi σo : MState) (tot : Int)
    (h : DRunL 32 exSwCode [exSwFun] [exSwDC] d 0x100 σi σo tot) : tot ≤ 12 :=
  data_sound_conv 32 exSwCode [exSwFun] [exSwCert] [exSwDC] exSw_checks exSwConvData_checks
    exSwConv_checks d 0x100 0 σi σo tot h (preAt_nil _ _ _ _ (by decide)) (by decide)

/-- The same switch whose case 0 branches to `movs r4, #1; bx lr`, reached only through the
    table: `r4` is written without being saved; refused. -/
def exSwClobberCode : Code :=
  ⟨0x100, #[0x2802, 0xD808, 0x4478, 0x7900, 0x0040, 0x4487, 0x0201, 0x0003, 0xE002, 0x4770,
    0x4770, 0x4770, 0x2401, 0x4770]⟩
def exSwClobberFn : BFun :=
  { exSwFun with nodes := exSwFun.nodes ++ [0x118, 0x11A] }

def exSwClobberD : DFun := { exSwD with spOff := List.replicate 12 (some 0) }

/-- The loop check accepts it (with the assumption on callees): the refusal is the
    convention's. -/
theorem exSwClobber_data : checkData 32 true exSwClobberCode [exSwClobberFn] [exSwClobberD] = true := by
  decide

theorem exSwClobber_refused : convOk 32 exSwClobberCode exSwClobberFn exSwClobberD = false := by
  decide

/-- `push {r4, lr}; movs r4, #0; pop {r5, pc}`: restores another register; refused. -/
def exMismatchCode : Code := ⟨0x300, #[0xB510, 0x2400, 0xBD20]⟩

theorem exMismatch_refused : convOk 32 exMismatchCode exSaveFn exSaveD = false := by decide

/-! ### A run of the linked semantics -/

/-- No `PUSH` and no `POP` at `a`. -/
def NoPP (c : Code) (a : Nat) : Prop := ∀ h, c.get a = some h → isPushH h = false ∧ h >>> 9 ≠ 0b1011110

theorem pushPop_of_noPP {c : Code} {a : Nat} (h : NoPP c a) (σ σ' : MState) : PushPopOk c a σ σ' := by
  unfold PushPopOk
  cases hc : c.get a with
  | none => trivial
  | some h0 =>
    obtain ⟨h1, h2⟩ := h h0 hc
    exact ⟨fun hp => absurd hp (by simp [h1]), fun hp => absurd hp h2⟩

/-- A chain of a function that saves nothing, calls nothing and neither pushes nor pops is a
    chain of the linked semantics. -/
theorem chainL_of_chain {R : Nat → MState → MState → Int → Prop} {frame : Bool} {c : Code}
    {SP0 : Nat} (σf : MState) :
    ∀ (s : List DStep) (a : Nat), DChain false frame c SP0 (some a) s →
      (∀ y ∈ s, NoPP c y.st.a ∧ y.st.calls = [] ∧ y.st.x = 0) →
      (∀ y ∈ s.getLast?, EffOk (effect false c y.st.a) y.σ σf ∧
        StackOk frame SP0 (stackEffect false c y.st.a) y.σ σf) →
      DChainL R frame c SP0 0 (some a) s σf
  | [], _, h, _, _ => by simp [DChain] at h
  | [x], a, h, hy, hl => by
    obtain ⟨hxa, _, hrest⟩ := h
    have hn : x.st.next = none := by
      cases hn : x.st.next with
      | none => rfl
      | some _ => rw [hn] at hrest; simp [DChain] at hrest
    obtain ⟨he, hs⟩ := hl x (by simp)
    obtain ⟨hpp, hc, hx⟩ := hy x (by simp)
    exact ⟨hxa, hn, he, hs, pushPop_of_noPP hpp _ _, fun _ j hj => absurd hj (Nat.not_lt_zero _),
      fun _ => hx, fun g hg => by rw [hc] at hg; cases hg⟩
  | x :: y :: t, a, h, hy, hl => by
    obtain ⟨hxa, hxy, hrest⟩ := h
    obtain ⟨he, hs⟩ := hxy y (by simp)
    rw [← hxa] at he hs
    obtain ⟨hpp, hc, hx⟩ := hy x (by simp)
    refine ⟨hxa, ⟨he, hs, pushPop_of_noPP hpp _ _, fun _ j hj => absurd hj (Nat.not_lt_zero _),
      fun _ => hx, fun g hg => by rw [hc] at hg; cases hg⟩, ?_⟩
    cases hn : x.st.next with
    | none => rw [hn] at hrest; simp [DChain] at hrest
    | some b =>
      rw [hn] at hrest
      exact chainL_of_chain σf (y :: t) b hrest (fun z hz => hy z (List.mem_cons_of_mem _ hz))
        (fun z hz => hl z (by simpa [List.getLast?_cons_cons] using hz))

/-- **The hypotheses of `exConv_sound` are satisfiable, and its bound is attained**: the
    counting loop has a run of the linked semantics of exactly 68 cycles. -/
theorem exConv_run :
    DRunL 32 exCode [exFunD] [exDFunC] 1 0x100 (mkS (regs0 0) f0) (mkS (regs0 10) (flagsSub 10 10)) 68 := by
  have hsave : saveN exCode 0x100 = 0 := by decide
  have hnopp : exRunC.all (fun y => match exCode.get y.1.a with
      | some h => !isPushH h && h >>> 9 != 0b1011110
      | none => true) = true := by decide
  have hcalls : exRunC.all (fun y => y.1.calls.isEmpty && y.1.x == 0) = true := by decide
  have hlast : effOkB (effect false exCode 0x10A) (regs0 10) (regs0 10) (flagsSub 10 10)
      (flagsSub 10 10) = true ∧ stackKeep (stackEffect false exCode 0x10A) = true := by decide
  refine ⟨exFunD, exDFunC, toD (cstep 0x100 (some 0x102) 1 0 0 f0), (exRunC.map toD).tail,
    rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsave]
    have hch := chainB_sound false exDFunC.frame exCode (mkS (regs0 0) f0).sp (some 0x100) exRunC exRun_chain
    refine chainL_of_chain _ (exRunC.map toD) 0x100 hch ?_ ?_
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      have h1 := List.all_eq_true.mp hnopp z hz
      have h2 := List.all_eq_true.mp hcalls z hz
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h2
      refine ⟨fun h hh => ?_, h2.1, h2.2⟩
      simp only [toD] at hh
      rw [hh] at h1
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h1
      exact h1
    · intro y hy
      have : (exRunC.map toD).getLast? = some (toD (cstep 0x10A none 3 0 10 (flagsSub 10 10))) := by
        rfl
      rw [this] at hy
      simp only [Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact ⟨effOkB_sound _ _ _ _ _ hlast.1, stackKeep_sound _ hlast.2 _ _ _ _ _ _⟩
  · have hsame : toD (cstep 0x100 (some 0x102) 1 0 0 f0) :: (exRunC.map toD).tail = exRunC.map toD := rfl
    rw [hsame]
    exact xchain_none exCode _ (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      simpa [toD] using List.all_eq_true.mp exRun_noX y hy)
  · intro y hy
    have : y ∈ exRunC.map toD := hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp this
    exact dOkB_sound 32 exCode z (List.all_eq_true.mp exRun_steps z hz)
  · intro r hr; simp [exDFunC, exDFun] at hr
  · exact exRun_cost.symm

end ImperativeOptimization.Thumb
