/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic
import ImperativeOptimization.CyclesCore

/-!
# Cycle bounds of binary control-flow graphs: soundness of the check

Runs of a program of control-flow graphs (`CyclesCore`): a run of function `f` is a walk
from its entry to its exit, given as a list of steps `(e, x)` (the edge taken, and the
cycles spent in the functions called on it), such that the edge counts of the walk satisfy
the function's rows (`RowsHold`) and the calls made on each step are runs of the callees of
smaller depth (`Run`). Its cost is the sum of the edge weights and of the calls' costs.

The certificate is the dual of the IPET linear program; the argument is weak duality:
along a walk the potentials telescope (`walk_bound`) and the multiplied rows sum to the
rows' values on the walk (`sum_dot`), which are at most their right-hand sides.

What is modelled, and so trusted when the theorem is applied to a binary: that the graph and
the weights describe the machine code and its timing (every execution of the function is a
walk of the graph, and costs the sum of the weights of its edges and of its calls), and that
the rows hold on every execution (loop bounds: back edges taken at most `N` times per entry
of the loop, summed over the entries). Only completed runs are bounded.
-/

namespace ImperativeOptimization.Cycles

/-- The weight of edge `e` (0 if there is none). -/
def wOf (G : Graph) (e : Nat) : Nat := (G.edges[e]?.map (·.w)).getD 0

/-- The functions called on edge `e`. -/
def callsOf (G : Graph) (e : Nat) : List Nat := (G.edges[e]?.map (·.calls)).getD []

/-- A walk from node `u` to node `v` along the edges named by the steps. -/
def Walk (G : Graph) : Nat → List (Nat × Int) → Nat → Prop
  | u, [], v => u = v
  | u, (e, _) :: s, v => ∃ ed, G.edges[e]? = some ed ∧ ed.src = u ∧ Walk G ed.dst s v

/-- The cost of a walk: edge weights plus the cycles of the calls. -/
def walkCost (G : Graph) : List (Nat × Int) → Int
  | [] => 0
  | (e, x) :: s => (wOf G e : Int) + x + walkCost G s

/-- The value `Σₑ aₑ·xₑ` of a row on the edge counts of a walk. -/
def rowVal (r : Row) : List (Nat × Int) → Int
  | [] => 0
  | (e, _) :: s => coefOf r.coef e + rowVal r s

/-- The rows hold on the walk. -/
def RowsHold (G : Graph) (s : List (Nat × Int)) : Prop := ∀ r ∈ G.rows, rowVal r s ≤ r.rhs

/-- `x` is the total cost of calls of the functions `gs`, each a run with property `R`. -/
def CallsWith (R : Nat → Int → Prop) : List Nat → Int → Prop
  | [], x => x = 0
  | g :: gs, x => ∃ c, R g c ∧ CallsWith R gs (x - c)

/-- Runs of function `f` of cost `c`, with calls nested at most `d - 1` deep. -/
def Run (P : List Graph) : Nat → Nat → Int → Prop
  | 0, _, _ => False
  | d + 1, f, c => ∃ G s, P[f]? = some G ∧ Walk G G.entry s G.exit ∧ RowsHold G s ∧
      (∀ st ∈ s, CallsWith (Run P d) (callsOf G st.1) st.2) ∧ c = walkCost G s

/-! ### The sums -/

theorem dot_add (ms : List Nat) (rs : List Row) (f g : Row → Int) :
    dot ms rs (fun r => f r + g r) = dot ms rs f + dot ms rs g := by
  induction ms generalizing rs with
  | nil => simp [dot]
  | cons m ms ih =>
    cases rs with
    | nil => simp [dot]
    | cons r rs => simp only [dot, ih]; ring

theorem dot_zero (ms : List Nat) (rs : List Row) : dot ms rs (fun _ => 0) = 0 := by
  induction ms generalizing rs with
  | nil => simp [dot]
  | cons m ms ih => cases rs with
    | nil => simp [dot]
    | cons r rs => simp [dot, ih]

theorem dot_mono (ms : List Nat) (rs : List Row) (f g : Row → Int)
    (h : ∀ r ∈ rs, f r ≤ g r) : dot ms rs f ≤ dot ms rs g := by
  induction ms generalizing rs with
  | nil => simp [dot]
  | cons m ms ih =>
    cases rs with
    | nil => simp [dot]
    | cons r rs =>
      simp only [dot]
      have h1 : (m : Int) * f r ≤ (m : Int) * g r :=
        Int.mul_le_mul_of_nonneg_left (h r (by simp)) (by omega)
      have h2 := ih rs (fun r' hr' => h r' (by simp [hr']))
      linarith

/-- The multiplied rows, summed along a walk, are the multiplied rows' values. -/
theorem sum_dot (ms : List Nat) (rs : List Row) : ∀ s : List (Nat × Int),
    (s.map (fun st => dot ms rs (fun r => coefOf r.coef st.1))).sum =
      dot ms rs (fun r => rowVal r s)
  | [] => by simp [rowVal, dot_zero]
  | (e, x) :: s => by
    simp only [List.map_cons, List.sum_cons, rowVal]
    rw [sum_dot ms rs s, dot_add]

theorem allEdges_get (p : Nat → Edge → Bool) : ∀ (i : Nat) (es : List Edge) (k : Nat) (e : Edge),
    allEdges p i es = true → es[k]? = some e → p (i + k) e = true
  | _, [], _, _, _, h => by simp at h
  | i, e' :: es, 0, e, h, hk => by
    simp only [allEdges, Bool.and_eq_true] at h
    simp at hk; subst hk; simpa using h.1
  | i, e' :: es, k + 1, e, h, hk => by
    simp only [allEdges, Bool.and_eq_true] at h
    have := allEdges_get p (i + 1) es k e h.2 (by simpa using hk)
    rwa [show i + 1 + k = i + (k + 1) by omega] at this

theorem callsWith_le (bounds : List Nat) (R : Nat → Int → Prop)
    (hR : ∀ g c, R g c → c ≤ bounds.getD g 0) :
    ∀ gs x, CallsWith R gs x → x ≤ callBound bounds gs
  | [], x, h => by simp [CallsWith] at h; simp [callBound, h]
  | g :: gs, x, h => by
    obtain ⟨c, hc, hrest⟩ := h
    have h1 := hR g c hc
    have h2 := callsWith_le bounds R hR gs (x - c) hrest
    simp only [callBound]; push_cast; linarith

/-! ### One function -/

/-- Along a walk, the potentials telescope: the scaled cost plus the potential difference is
    at most the multiplied rows summed along the walk. -/
theorem walk_bound (bounds : List Nat) (G : Graph) (C : Cert) (R : Nat → Int → Prop)
    (hR : ∀ g c, R g c → c ≤ bounds.getD g 0)
    (hE : allEdges (edgeOk bounds G C) 0 G.edges = true) (v : Nat) :
    ∀ (s : List (Nat × Int)) (u : Nat), Walk G u s v →
      (∀ st ∈ s, CallsWith R (callsOf G st.1) st.2) →
      (C.scale : Int) * walkCost G s + potOf C v - potOf C u ≤
        (s.map (fun st => dot C.mult G.rows (fun r => coefOf r.coef st.1))).sum
  | [], u, hw, _ => by simp [Walk] at hw; subst hw; simp [walkCost]
  | (e, x) :: s, u, hw, hc => by
    obtain ⟨ed, hed, hsrc, hrest⟩ := hw
    have ih := walk_bound bounds G C R hR hE v s ed.dst hrest (fun st hst => hc st (by simp [hst]))
    have hok := allEdges_get _ 0 G.edges e ed hE hed
    simp only [Nat.zero_add, edgeOk, decide_eq_true_eq] at hok
    have hx : x ≤ callBound bounds ed.calls := by
      have := callsWith_le bounds R hR _ x (hc (e, x) (by simp))
      simpa [callsOf, hed] using this
    have hw : (wOf G e : Int) = ed.w := by simp [wOf, hed]
    simp only [walkCost, List.map_cons, List.sum_cons, hw]
    subst hsrc
    have hD : (0 : Int) ≤ C.scale := by omega
    have := Int.mul_le_mul_of_nonneg_left (show (ed.w : Int) + x ≤ ed.w + callBound bounds ed.calls by
      linarith) hD
    push_cast at hok
    nlinarith

/-- **Soundness for one function**: if its certificate is accepted with the claimed bounds,
    every walk from entry to exit on which the rows hold, with calls bounded by the claimed
    bounds, costs at most the claimed bound. -/
theorem cycles_sound (bounds : List Nat) (G : Graph) (C : Cert) (R : Nat → Int → Prop)
    (hR : ∀ g c, R g c → c ≤ bounds.getD g 0) (hC : checkFn bounds G C = true)
    (s : List (Nat × Int)) (hw : Walk G G.entry s G.exit) (hrows : RowsHold G s)
    (hc : ∀ st ∈ s, CallsWith R (callsOf G st.1) st.2) :
    walkCost G s ≤ C.bound := by
  simp only [checkFn, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨hD, hE⟩, hX⟩ := hC
  have h1 := walk_bound bounds G C R hR hE G.exit s G.entry hw hc
  rw [sum_dot] at h1
  have h2 := dot_mono C.mult G.rows (fun r => rowVal r s) (·.rhs) hrows
  have h3 : (C.scale : Int) * walkCost G s ≤ (C.scale : Int) * C.bound := by linarith
  exact le_of_mul_le_mul_left h3 (by exact_mod_cast hD)

/-! ### Programs -/

/-- **Soundness for a program**: if `checkProgram` accepts, every completed run of every
    function costs at most the claimed bound (by induction on the depth of calls, so the
    claims of recursive functions are covered too). -/
theorem program_sound (P : List Graph) (Cs : List Cert) (h : checkProgram P Cs = true) :
    ∀ (d f : Nat) (c : Int), Run P d f c → c ≤ ((Cs.map Cert.bound).getD f 0 : Nat) := by
  simp only [checkProgram, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  intro d
  induction d with
  | zero => intro f c hr; simp [Run] at hr
  | succ d ih =>
    intro f c hr
    obtain ⟨G, s, hG, hw, hrows, hc, rfl⟩ := hr
    have hf : f < Cs.length := by
      have := (List.getElem?_eq_some_iff.mp hG).1; omega
    have hmem : (G, Cs[f]) ∈ P.zip Cs := by
      rw [List.mem_iff_getElem?]
      exact ⟨f, by simp [List.getElem?_zip_eq_some, hG]⟩
    have hok : checkFn (Cs.map Cert.bound) G Cs[f] = true := hall _ hmem
    have := cycles_sound (Cs.map Cert.bound) G Cs[f] (Run P d) ih hok s hw hrows hc
    simpa [List.getD_eq_getElem?_getD, hf] using this

/-! ### An example: a loop of at most 10 iterations

Nodes: 0 entry, 1 loop header, 2 body, 3 exit. Edges: `0 → 1` (2 cycles), `1 → 2`
(1 cycle, test not taken), `2 → 1` (5 cycles, back edge), `1 → 3` (3 cycles, exit taken).
Row: `x₂ − 10·x₀ ≤ 0`. The bound is `2 + 10·(1 + 5) + 3 = 65`: potentials
`π = (65, 3, 2, 0)` and multiplier 6 (the cost of one iteration; the entry edge pays for the 10). -/

def exLoop : Graph :=
  ⟨0, 3, [⟨0, 1, 2, []⟩, ⟨1, 2, 1, []⟩, ⟨2, 1, 5, []⟩, ⟨1, 3, 3, []⟩],
    [⟨[(2, 1), (0, -10)], 0⟩]⟩

def exLoopCert : Cert := ⟨1, [65, 3, 2, 0], [6], 65⟩

theorem exLoop_checks : checkProgram [exLoop] [exLoopCert] = true := by decide

/-- A bound below the worst case is rejected. -/
theorem exLoop_tight : checkProgram [exLoop] [⟨1, [64, 3, 2, 0], [6], 64⟩] = false := by decide

/-- The hypotheses are satisfiable: a run with two iterations, of cost `2 + 2·6 + 3 = 17`. -/
theorem exLoop_run : Run [exLoop] 1 0 17 := by
  refine ⟨exLoop, [(0, 0), (1, 0), (2, 0), (1, 0), (2, 0), (3, 0)], rfl, ?_, ?_, ?_, ?_⟩
  · exact ⟨_, rfl, rfl, _, rfl, rfl, _, rfl, rfl, _, rfl, rfl, _, rfl, rfl, _, rfl, rfl, rfl⟩
  · intro r hr; simp [exLoop] at hr; subst hr; decide
  · intro st hst; simp at hst
    rcases hst with h | h | h | h | h | h <;> subst h <;> rfl
  · decide

example : (17 : Int) ≤ 65 := program_sound _ _ exLoop_checks 1 0 17 exLoop_run

end ImperativeOptimization.Cycles
