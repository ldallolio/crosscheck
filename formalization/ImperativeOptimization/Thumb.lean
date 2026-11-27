/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import ImperativeOptimization.Cycles
import ImperativeOptimization.ThumbCore

/-!
# Cycle bounds of Cortex-M0 machine code: soundness

The semantics of machine code used here follows the program counter. A run of the function
whose entry is at address `e` is a sequence of steps `(a, next, w, calls, x)` from `e`
until a return (`next = none`): the instruction at `a` allows the step (`Step`: one of its
successors `trans`, with its cycles and callees, as given by `decode`; an address without
code or a `stop` instruction allows any step), the calls made are runs of the callees of
smaller depth costing `x` in all, and the loop rows of the function hold on the counts of
the transitions. Its cost is the sum of the cycles and of the calls. Data are abstracted:
both successors of a conditional branch are allowed.

`binary_sound`: if `checkBinary` accepts, every such run of every function costs at most
the certified bound. The proof shows that the graphs built from the code contain every run
(`translate`) and applies `Cycles.program_sound`.

Trusted, as the specification of the processor: `decode` (the instruction encodings, the
classification of their effect on the program counter, the cycles of the Cortex-M0 with
zero-wait-state memory) and the semantics above (the processor executes the instruction at
the program counter; the cycles of a run are the sum of the cycles of its instructions;
interrupts are not taken). Also trusted: that the code given is that of the binary, and
that the rows hold on the executions (the loop bounds).
-/

namespace ImperativeOptimization.Thumb

open ImperativeOptimization.Cycles

/-- The instruction at `a` allows the step to `next` with `w` cycles calling `calls`; a
    jump listed in `J` goes to one of its targets (for `J = []`, the steps of `trans`, and a
    `stop` instruction does anything). -/
def Step (mul : Nat) (c : Code) (J : List JT) (a : Nat) (next : Option Nat) (w : Nat) (calls : List Nat) : Prop :=
  match decode mul c a with
  | some i => (i.kind = .stop ∧ jumpTr J a = []) ∨ (next, w, calls) ∈ transJ J i a
  | none => True

/-- A step of a run: address, next address, cycles, callees, cycles spent in the calls. -/
structure MStep where
  a : Nat
  next : Option Nat
  w : Nat
  calls : List Nat
  x : Int

/-- The steps follow each other from the given address until a return. -/
def MChain : Option Nat → List MStep → Prop
  | none, [] => True
  | some a, s :: t => s.a = a ∧ MChain s.next t
  | _, _ => False

/-- The function whose entry is `e` (the first one listed). -/
def fnAt (fs : List BFun) (e : Nat) : Option BFun :=
  (find (fs.map (·.entry)) e).bind (fs[·]?)

/-- Runs of the function at address `e`, of cost `c`, with calls nested less than `d` deep. -/
def MRun (mul : Nat) (c : Code) (fs : List BFun) : Nat → Nat → Int → Prop
  | 0, _, _ => False
  | d + 1, e, total => ∃ f s, fnAt fs e = some f ∧ MChain (some e) s ∧
      (∀ st ∈ s, Step mul c f.jumps st.a st.next st.w st.calls ∧ CallsWith (MRun mul c fs d) st.calls st.x) ∧
      (∀ r ∈ f.rows, (s.map (fun st => coefPair r.coef st.a st.next)).sum ≤ r.rhs) ∧
      total = (s.map (fun st => (st.w : Int) + st.x)).sum

/-! ### Lemmas on the list functions -/

theorem find_get : ∀ (l : List Nat) (t i : Nat), find l t = some i → l[i]? = some t
  | [], _, _, h => by simp [find] at h
  | x :: xs, t, i, h => by
    simp only [find] at h
    split at h
    · cases h; simp_all
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using find_get xs t j hj

theorem optMap_get {α β : Type} (f : α → Option β) : ∀ (l : List α) (L : List β) (i : Nat) (x : α),
    optMap f l = some L → l[i]? = some x → ∃ y, f x = some y ∧ L[i]? = some y
  | [], _, _, _, _, hx => by simp at hx
  | x' :: xs, L, i, x, h, hx => by
    simp only [optMap] at h
    split at h
    · rename_i y ys hy hys
      cases h
      cases i with
      | zero => simp at hx; subst hx; exact ⟨y, hy, by simp⟩
      | succ i =>
        obtain ⟨z, hz, hz'⟩ := optMap_get f xs ys i x hys (by simpa using hx)
        exact ⟨z, hz, by simpa using hz'⟩
    · cases h

theorem mem_medges (mul : Nat) (c : Code) (J : List JT) (a : Nat) (i : Insn) (p : Option Nat × Nat × List Nat)
    (hi : decode mul c a = some i) (hp : p ∈ transJ J i a) :
    ∀ nodes : List Nat, a ∈ nodes → (a, p.1, p.2.1, p.2.2) ∈ medges mul c J nodes
  | [], h => by simp at h
  | b :: bs, h => by
    simp only [medges, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · left; rw [hi]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
    · right; exact mem_medges mul c J a i p hi hp bs h

theorem coefOf_indexed {α : Type} (F : α → Int) : ∀ (L : List α) (s j : Nat),
    coefOf ((indexed s L).map (fun p => (p.1, F p.2))) j =
      if s ≤ j then ((L[j - s]?).map F).getD 0 else 0
  | [], s, j => by simp [indexed, coefOf]
  | x :: xs, s, j => by
    simp only [indexed, List.map_cons, coefOf]
    rw [coefOf_indexed F xs (s + 1) j]
    by_cases h : s = j
    · subst h; simp
    · by_cases h' : s + 1 ≤ j
      · have : j - s = (j - (s + 1)) + 1 := by omega
        simp [h, h', this, show s ≤ j by omega]
      · simp [h, h', show ¬ s ≤ j by omega]

theorem closed_spec (mul : Nat) (c : Code) (J : List JT) (e : Nat) (nodes : List Nat)
    (h : closed mul c J e nodes = true) :
    e ∈ nodes ∧ ∀ a ∈ nodes, ∃ i, decode mul c a = some i ∧ (i.kind ≠ .stop ∨ jumpTr J a ≠ []) ∧
      ∀ p ∈ transJ J i a, ∀ q, p.1 = some q → q ∈ nodes := by
  simp only [closed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, fun a ha => ?_⟩
  have := h.2 a ha
  split at this
  · rename_i i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    refine ⟨i, hi, this.1, fun p hp q hq => ?_⟩
    have := this.2 p hp
    rw [hq] at this
    simpa using this
  · cases this

theorem callsWith_transfer (entries : List Nat) (R1 R2 : Nat → Int → Prop)
    (hR : ∀ t j c, R1 t c → find entries t = some j → R2 j c) :
    ∀ (cs gs : List Nat) (x : Int), optMap (find entries) cs = some gs →
      CallsWith R1 cs x → CallsWith R2 gs x
  | [], gs, x, hg, h => by simp [optMap] at hg; subst hg; exact h
  | t :: ts, gs, x, hg, h => by
    simp only [optMap] at hg
    split at hg
    · rename_i j js hj hjs
      cases hg
      obtain ⟨c0, hc, hrest⟩ := h
      exact ⟨c0, hR t j c0 hc hj, callsWith_transfer entries R1 R2 hR ts js (x - c0) hjs hrest⟩
    · cases hg

/-! ### Machine runs are runs of the built graphs -/

/-- The walk of a machine run in the graph built from the code. -/
theorem chain_walk (mul : Nat) (c : Code) (entries : List Nat) (f : BFun) (G : Graph)
    (R1 R2 : Nat → Int → Prop) (hR : ∀ t j c, R1 t c → find entries t = some j → R2 j c)
    (hcl : closed mul c f.jumps f.entry f.nodes = true)
    (edges : List Edge) (hE : optMap (mkEdge entries f.nodes) (medges mul c f.jumps f.nodes) = some edges)
    (hG : G.edges = edges) :
    ∀ (s : List MStep) (o : Option Nat), MChain o s → (∀ q, o = some q → q ∈ f.nodes) →
      (∀ st ∈ s, Step mul c f.jumps st.a st.next st.w st.calls ∧ CallsWith R1 st.calls st.x) →
      ∃ gs : List (Nat × Int), Walk G (nid f.nodes o) gs (nid f.nodes none) ∧
        walkCost G gs = (s.map (fun st => (st.w : Int) + st.x)).sum ∧
        (∀ r : MRow, rowVal (mkRow (medges mul c f.jumps f.nodes) r) gs =
          (s.map (fun st => coefPair r.coef st.a st.next)).sum) ∧
        (∀ st ∈ gs, CallsWith R2 (callsOf G st.1) st.2)
  | [], o, hch, _, _ => by
    cases o with
    | none => exact ⟨[], by simp [Walk], by simp [walkCost], fun r => by simp [rowVal], by simp⟩
    | some q => simp [MChain] at hch
  | st :: t, o, hch, hin, hsteps => by
    cases o with
    | none => simp [MChain] at hch
    | some a =>
      obtain ⟨hsa, hrest⟩ := hch
      have ha : a ∈ f.nodes := hin a rfl
      obtain ⟨_, hcl2⟩ := closed_spec mul c f.jumps f.entry f.nodes hcl
      obtain ⟨i, hi, hstop, hsucc⟩ := hcl2 a ha
      obtain ⟨hstep, hcalls⟩ := hsteps st (by simp)
      have htr : (st.next, st.w, st.calls) ∈ transJ f.jumps i a := by
        simp only [Step] at hstep
        rw [hsa, hi] at hstep
        rcases hstep with h | h
        · rcases hstop with h' | h'
          · exact absurd h.1 h'
          · exact absurd h.2 h'
        · exact h
      have hme := mem_medges mul c f.jumps a i _ hi htr f.nodes ha
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hme
      obtain ⟨ed, hed, hk'⟩ := optMap_get _ _ edges k _ hE hk
      simp only [mkEdge] at hed
      split at hed
      · rename_i gs' hgs'
        cases hed
        obtain ⟨gs, hw, hcost, hrows, hc⟩ := chain_walk mul c entries f G R1 R2 hR hcl edges hE hG t
          st.next hrest (fun q hq => hsucc _ htr q hq) (fun s' hs' => hsteps s' (by simp [hs']))
        refine ⟨(k, st.x) :: gs, ?_, ?_, ?_, ?_⟩
        · exact ⟨_, by rw [hG]; exact hk', rfl, hw⟩
        · have : wOf G k = st.w := by simp [wOf, hG, hk']
          simp only [walkCost, List.map_cons, List.sum_cons, this, hcost]
        · intro r
          simp only [rowVal, List.map_cons, List.sum_cons]
          rw [hrows r]
          simp only [mkRow]
          have hci := coefOf_indexed (fun m : Nat × Option Nat × Nat × List Nat => coefPair r.coef m.1 m.2.1)
            (medges mul c f.jumps f.nodes) 0 k
          rw [hci]
          simp [hk, hsa]
        · intro s' hs'
          rcases List.mem_cons.mp hs' with rfl | hs'
          · have : callsOf G k = gs' := by simp [callsOf, hG, hk']
            rw [this]
            exact callsWith_transfer entries R1 R2 hR st.calls gs' st.x hgs' hcalls
          · exact hc s' hs'
      · cases hed

/-- Every machine run of a function is a run of its built graph, of the same cost. -/
theorem translate (mul : Nat) (c : Code) (fs : List BFun) (Ps : List Graph)
    (hP : optMap (buildFn mul c (fs.map (·.entry))) fs = some Ps) :
    ∀ d e i (tot : Int), MRun mul c fs d e tot → find (fs.map (·.entry)) e = some i →
      Run Ps d i tot := by
  intro d
  induction d with
  | zero => intro e i tot h; simp [MRun] at h
  | succ d ih =>
    intro e i tot h hfind
    obtain ⟨f, s, hf, hch, hsteps, hrows, rfl⟩ := h
    have hfi : fs[i]? = some f := by simpa [fnAt, hfind] using hf
    obtain ⟨G, hb, hPi⟩ := optMap_get _ fs Ps i f hP hfi
    have hentry : f.entry = e := by
      have := find_get _ e i hfind
      simp [hfi] at this
      exact this
    simp only [buildFn] at hb
    split at hb
    · rename_i hcl
      split at hb
      · rename_i edges hE
        cases hb
        obtain ⟨gs, hw, hcost, hrv, hc⟩ := chain_walk mul c (fs.map (·.entry)) f
          ⟨nid f.nodes (some f.entry), f.nodes.length, edges, f.rows.map (mkRow (medges mul c f.jumps f.nodes))⟩
          (MRun mul c fs d) (Run Ps d) ih hcl edges hE rfl s (some e) hch
          (fun q hq => by cases hq; rw [← hentry]; exact (closed_spec mul c _ _ _ hcl).1) hsteps
        refine ⟨_, gs, hPi, ?_, ?_, hc, hcost.symm⟩
        · simpa [hentry, nid] using hw
        · intro r hr
          obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
          rw [hrv r']
          exact hrows r' hr'
      · cases hb
    · cases hb

/-- **Soundness on machine code**: if `checkBinary` accepts, every run of the function at
    entry `e` (the `i`-th of the program) costs at most its certified bound. -/
theorem binary_sound (mul : Nat) (c : Code) (fs : List BFun) (Cs : List Cert) (jt : Bool)
    (h : checkBinary mul c fs Cs jt = true) (d e i : Nat) (tot : Int)
    (hrun : MRun mul c fs d e tot) (hfind : find (fs.map (·.entry)) e = some i) :
    tot ≤ ((Cs.map Cert.bound).getD i 0 : Nat) := by
  simp only [checkBinary, Bool.and_eq_true] at h
  replace h := h.2
  split at h
  · rename_i Ps hP
    exact program_sound Ps Cs h d i tot (translate mul c fs Ps hP d e i tot hrun hfind)
  · cases h

theorem step_of {mul : Nat} {c : Code} {J : List JT} {a : Nat} {i : Insn} {n : Option Nat} {w : Nat}
    {cs : List Nat} (h : decode mul c a = some i) (hm : (n, w, cs) ∈ transJ J i a) : Step mul c J a n w cs := by
  simp [Step, h, hm]

/-- Without far branches, `transF` is `trans`. -/
theorem transF_of (J : List JT) (i : Insn) (a : Nat) (h : farAt J a = false) : transF J i a = trans i a := by
  unfold transF; split <;> simp [h]

theorem transF_nil (i : Insn) (a : Nat) : transF [] i a = trans i a := transF_of [] i a (by simp [farAt])

/-- Without jumps (the checks of `checkBinary` without `jt`), `transJ` is `trans`. -/
theorem transJ_nil (i : Insn) (a : Nat) : transJ [] i a = trans i a := by
  simp [transJ, jumpTr, transF_nil]

/-! ### An example: a counting loop in machine code

At `0x100`: `movs r0, #0; cmp r0, #10; bge 0x10a; adds r0, #1; b 0x102; bx lr`, a loop of
at most 10 iterations (row: the back edge `0x108 → 0x102` at most 10 times per entry
`0x100 → 0x102`). Worst case: `1 + 10·(1 + 1 + 1 + 3) + (1 + 3) + 3 = 68` cycles. -/

def exCode : Code := ⟨0x100, #[0x2000, 0x280A, 0xDA01, 0x3001, 0xE7FB, 0x4770]⟩

def exFun : BFun :=
  ⟨0x100, [0x100, 0x102, 0x104, 0x106, 0x108, 0x10A], [⟨[(0x108, 0x102, 1), (0x100, 0x102, -10)], 0⟩], []⟩

/-- Potentials: worst cycles from each instruction to the return, the loop paid by the
    multiplier 6 on its entry. -/
def exCert : Cert := ⟨1, [68, 7, 6, 5, 4, 3, 0], [6], 68⟩

theorem exBinary_checks : checkBinary 32 exCode [exFun] [exCert] = true := by decide

theorem exBinary_tight : checkBinary 32 exCode [exFun] [⟨1, [67, 7, 6, 5, 4, 3, 0], [6], 67⟩] = false := by
  decide

/-- The hypotheses are satisfiable: the run with no iteration (`r0 ≥ 10` at once is not
    what the code computes, but the semantics abstracts data), 1 + 1 + 3 + 3 = 8 cycles. -/
theorem exBinary_run : MRun 32 exCode [exFun] 1 0x100 8 := by
  refine ⟨exFun, [⟨0x100, some 0x102, 1, [], 0⟩, ⟨0x102, some 0x104, 1, [], 0⟩,
    ⟨0x104, some 0x10A, 3, [], 0⟩, ⟨0x10A, none, 3, [], 0⟩], rfl, ?_, ?_, ?_, by decide⟩
  · simp [MChain]
  · intro st hst
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl
    · exact ⟨step_of (i := ⟨2, .seq, 1, 1⟩) (by decide) (by decide), rfl⟩
    · exact ⟨step_of (i := ⟨2, .seq, 1, 1⟩) (by decide) (by decide), rfl⟩
    · exact ⟨step_of (i := ⟨2, .cond 0x10A, 3, 1⟩) (by decide) (by decide), rfl⟩
    · exact ⟨step_of (i := ⟨2, .ret, 3, 3⟩) (by decide) (by decide), rfl⟩
  · intro r hr
    simp [exFun] at hr; subst hr; decide

example : (8 : Int) ≤ 68 := binary_sound 32 exCode [exFun] [exCert] false exBinary_checks 1 0x100 0 8
  exBinary_run (by decide)

end ImperativeOptimization.Thumb
