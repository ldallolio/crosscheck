/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic
import ImperativeOptimization.ResponseCore

/-!
# Response time of a computation under sporadic interrupts

The classical response-time bound for fixed-priority preemptive scheduling (Joseph and
Pandya 1986; Audsley et al. 1993), in the form needed for one computation preempted by
interrupt handlers: if the computation needs `C` time slots, handler `k` needs at most
`Ch k` slots per activation and is activated at most once every `Th k` slots, then the
computation completes within any `R` with `C + Σₖ Ch k · ⌈R / Th k⌉ ≤ R`.

Model (discrete time from the start of the computation, slot `0`):
* `run s : Option ℕ` is what the processor does in slot `s`: `none` idle, `some 0` the
  computation, `some (k+1)` handler `k`;
* the processor is not idle while the computation is unfinished (work conserving);
* each slot of handler `k` belongs to an activation released at or before it
  (`job k s ∈ rel k`, `job k s ≤ s`), and an activation runs at most `Ch k` slots;
* activations of handler `k` are separated by at least `Th k > 0` slots (sporadic).

The activations of a handler form a set of slots that may be infinite (a periodic interrupt
never stops). Activations released before slot `0` are not represented: the theorem assumes that no
handler work is pending when the computation starts. The priority order is not needed for
this upper bound (only that the processor does not idle while the computation is pending).
-/

namespace ImperativeOptimization.Interrupts

/-- Slots before `t` in which `run` does `x`. -/
def slots (run : ℕ → Option ℕ) (x : ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun s => run s = some x)

open Classical in
/-- The activations of `rel` released before `t`. The set `rel` may be infinite (a handler
    activated forever); only finitely many of its elements are below `t`. -/
noncomputable def before (rel : Set ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun r => r ∈ rel)

theorem mem_before {rel : Set ℕ} {t r : ℕ} : r ∈ before rel t ↔ r ∈ rel ∧ r < t := by
  unfold before
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_comm

/-- Activations of a sporadic handler released before `t`: at most `⌈t / T⌉`. -/
theorem sporadic_count (rel : Set ℕ) (T t : ℕ) (hT : 0 < T)
    (hsep : ∀ a ∈ rel, ∀ b ∈ rel, a < b → a + T ≤ b) :
    (before rel t).card ≤ ceilDiv t T := by
  -- `r ↦ r / T` is injective on the releases and maps those before `t` below `⌈t/T⌉`
  have key : ∀ a ∈ rel, ∀ b ∈ rel, a < b → a / T ≠ b / T := by
    intro a ha b hb hab heq
    have h1 := Nat.div_add_mod a T
    have h2 := Nat.div_add_mod b T
    have h3 := Nat.mod_lt b hT
    have h4 := hsep a ha b hb hab
    rw [heq] at h1
    omega
  have hinj : Set.InjOn (fun r => r / T) ((before rel t) : Set ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_before] at ha hb
    simp only at hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key a ha.1 b hb.1 h hab
    · exact key b hb.1 a ha.1 h hab.symm
  have himg : (before rel t).image (fun r => r / T) ⊆ Finset.range (ceilDiv t T) := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨r, hr', rfl⟩ := hx
    obtain ⟨_, hr⟩ := mem_before.mp hr'
    simp only [Finset.mem_range, ceilDiv]
    have e : t + T - 1 = (t - 1) + T := by omega
    rw [e, Nat.add_div_right _ hT]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  calc (before rel t).card
      = ((before rel t).image (fun r => r / T)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (ceilDiv t T)).card := Finset.card_le_card himg
    _ = ceilDiv t T := Finset.card_range _

/-- The slots of a handler before `t` are at most `Ch` per activation released before `t`. -/
theorem handler_demand (run : ℕ → Option ℕ) (k : ℕ) (rel : Set ℕ) (job : ℕ → ℕ) (Ch t : ℕ)
    (hjob : ∀ s, run s = some (k + 1) → job s ∈ rel ∧ job s ≤ s)
    (hcost : ∀ r, ((Finset.range t).filter (fun s => run s = some (k + 1) ∧ job s = r)).card ≤ Ch) :
    (slots run (k + 1) t).card ≤ Ch * (before rel t).card := by
  have h1 := Finset.card_le_mul_card_image (f := job) (slots run (k + 1) t) Ch (by
    intro r _
    calc ((slots run (k + 1) t).filter (fun s => job s = r)).card
        = ((Finset.range t).filter (fun s => run s = some (k + 1) ∧ job s = r)).card := by
          congr 1; ext s; simp [slots, and_assoc]
      _ ≤ Ch := hcost r)
  have h2 : (slots run (k + 1) t).image job ⊆ before rel t := by
    intro r hr
    simp only [Finset.mem_image, slots, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨s, ⟨hs, hrun⟩, rfl⟩ := hr
    have := hjob s hrun
    exact mem_before.mpr ⟨this.1, by omega⟩
  calc (slots run (k + 1) t).card ≤ Ch * ((slots run (k + 1) t).image job).card := h1
    _ ≤ Ch * (before rel t).card := Nat.mul_le_mul_left _ (Finset.card_le_card h2)

/-- A system of interrupt handlers `hs`, with their worst-case costs, minimal inter-arrival
    times, activations, and the attribution of each handler slot to an activation. -/
structure Handlers where
  hs : Finset ℕ
  Ch : ℕ → ℕ
  Th : ℕ → ℕ
  rel : ℕ → Set ℕ
  job : ℕ → ℕ → ℕ

/-- A schedule `run` of a computation that needs `C` slots, preempted by the handlers `H`. -/
structure Admissible (H : Handlers) (run : ℕ → Option ℕ) (C : ℕ) : Prop where
  /-- each slot is idle, the computation, or a handler of `H` -/
  slot : ∀ s, run s = none ∨ run s = some 0 ∨ ∃ k ∈ H.hs, run s = some (k + 1)
  /-- the processor is not idle while the computation is unfinished -/
  busy : ∀ s, (slots run 0 s).card < C → run s ≠ none
  /-- handlers are sporadic -/
  period : ∀ k ∈ H.hs, 0 < H.Th k
  sep : ∀ k ∈ H.hs, ∀ a ∈ H.rel k, ∀ b ∈ H.rel k, a < b → a + H.Th k ≤ b
  /-- a handler runs only for an activation released at or before the slot -/
  job : ∀ k ∈ H.hs, ∀ s, run s = some (k + 1) → H.job k s ∈ H.rel k ∧ H.job k s ≤ s
  /-- an activation runs at most `Ch k` slots -/
  cost : ∀ k ∈ H.hs, ∀ t r,
    ((Finset.range t).filter (fun s => run s = some (k + 1) ∧ H.job k s = r)).card ≤ H.Ch k

/-- The demand of the computation and the handlers over a window of length `R`. -/
def demand (H : Handlers) (C R : ℕ) : ℕ := C + ∑ k ∈ H.hs, H.Ch k * ceilDiv R (H.Th k)

theorem slots_mono (run : ℕ → Option ℕ) (x : ℕ) {s t : ℕ} (h : s ≤ t) :
    (slots run x s).card ≤ (slots run x t).card := by
  apply Finset.card_le_card
  intro u
  simp only [slots, Finset.mem_filter, Finset.mem_range]
  exact fun hu => ⟨by omega, hu.2⟩

/-- **Response-time bound.** If `demand H C R ≤ R`, the computation has completed
    (received its `C` slots) within the first `R` slots. -/
theorem response_time_bound (H : Handlers) (run : ℕ → Option ℕ) (C R : ℕ)
    (hA : Admissible H run C) (hR : demand H C R ≤ R) :
    C ≤ (slots run 0 R).card := by
  by_contra hlt
  push Not at hlt
  -- every slot before R is busy
  have hcover : Finset.range R ⊆ slots run 0 R ∪ H.hs.biUnion (fun k => slots run (k + 1) R) := by
    intro s hs
    have hsR := Finset.mem_range.mp hs
    have hb := hA.busy s (lt_of_le_of_lt (slots_mono run 0 hsR.le) hlt)
    rcases hA.slot s with h | h | ⟨k, hk, h⟩
    · exact absurd h hb
    · exact Finset.mem_union_left _ (by simp [slots, hsR, h])
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk, by simp [slots, hsR, h]⟩)
  have hh : ∀ k ∈ H.hs, (slots run (k + 1) R).card ≤ H.Ch k * ceilDiv R (H.Th k) := by
    intro k hk
    calc (slots run (k + 1) R).card ≤ H.Ch k * (before (H.rel k) R).card :=
          handler_demand run k (H.rel k) (H.job k) (H.Ch k) R (hA.job k hk) (hA.cost k hk R)
      _ ≤ H.Ch k * ceilDiv R (H.Th k) :=
          Nat.mul_le_mul_left _ (sporadic_count _ _ _ (hA.period k hk) (hA.sep k hk))
  have hcard : R ≤ (slots run 0 R).card + ∑ k ∈ H.hs, H.Ch k * ceilDiv R (H.Th k) := by
    calc R = (Finset.range R).card := (Finset.card_range R).symm
      _ ≤ (slots run 0 R ∪ H.hs.biUnion (fun k => slots run (k + 1) R)).card :=
          Finset.card_le_card hcover
      _ ≤ (slots run 0 R).card + (H.hs.biUnion (fun k => slots run (k + 1) R)).card :=
          Finset.card_union_le _ _
      _ ≤ (slots run 0 R).card + ∑ k ∈ H.hs, (slots run (k + 1) R).card :=
          Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ (slots run 0 R).card + ∑ k ∈ H.hs, H.Ch k * ceilDiv R (H.Th k) :=
          Nat.add_le_add_left (Finset.sum_le_sum hh) _
  unfold demand at hR
  omega

/-- The usual iteration `R₀ = C`, `Rₙ₊₁ = demand Rₙ`: a fixed point is a valid `R`. -/
def rtaIter (H : Handlers) (C : ℕ) : ℕ → ℕ
  | 0 => C
  | n + 1 => demand H C (rtaIter H C n)

theorem rtaIter_fixed (H : Handlers) (C n : ℕ) (h : rtaIter H C (n + 1) = rtaIter H C n) :
    demand H C (rtaIter H C n) ≤ rtaIter H C n := by
  simp only [rtaIter] at h; omega

/-- Example: a computation of 100 slots, a handler of cost 10 every 50 slots and one of
    cost 3 every 20. The iteration gives `100, 135, 151, 164, 167, 167`: the computation
    completes within 167 slots (`100 + 10·⌈167/50⌉ + 3·⌈167/20⌉ = 100 + 40 + 27`). -/
def exH : Handlers := ⟨{0, 1}, fun k => if k = 0 then 10 else 3, fun k => if k = 0 then 50 else 20,
  fun _ => ∅, fun _ _ => 0⟩

theorem exH_iter : rtaIter exH 100 4 = 167 ∧ rtaIter exH 100 5 = 167 := by decide

theorem exH_demand : demand exH 100 167 ≤ 167 := by decide

/-- The hypotheses can be met: one handler activation at slot 0 (cost 1, period 5), then
    the computation (3 slots); `R = 4` satisfies the condition, and the computation has its
    3 slots within the first 4. -/
def oneH : Handlers := ⟨{0}, fun _ => 1, fun _ => 5, fun _ => {0}, fun _ _ => 0⟩

def oneRun (s : ℕ) : Option ℕ := if s = 0 then some 1 else some 0

theorem oneRun_admissible : Admissible oneH oneRun 3 where
  slot s := by unfold oneRun; split <;> simp [oneH]
  busy s _ := by unfold oneRun; split <;> simp
  period k _ := by simp [oneH]
  sep k _ a ha b hb hab := by simp [oneH] at ha hb; omega
  job k hk s h := by
    simp [oneH] at hk ⊢
  cost k hk t r := by
    simp [oneH] at hk ⊢; subst hk
    calc ((Finset.range t).filter (fun s => oneRun s = some (0 + 1) ∧ 0 = r)).card
        ≤ ({0} : Finset ℕ).card := by
          apply Finset.card_le_card
          intro s hs
          rw [Finset.mem_filter] at hs
          simp only [oneRun] at hs
          split at hs <;> simp_all
      _ = 1 := rfl

theorem oneRun_completes : 3 ≤ (slots oneRun 0 4).card :=
  response_time_bound oneH oneRun 3 4 oneRun_admissible (by decide)

/-- The hypotheses can be met by a handler that never stops: an activation every 5 slots
    (cost 1), each served in its slot of release; the computation runs in the other slots.
    The set of activations is infinite. -/
def perH : Handlers := ⟨{0}, fun _ => 1, fun _ => 5, fun _ => {r | r % 5 = 0}, fun _ s => s⟩

def perRun (s : ℕ) : Option ℕ := if s % 5 = 0 then some 1 else some 0

theorem perRun_admissible (C : ℕ) : Admissible perH perRun C where
  slot s := by unfold perRun; split <;> simp [perH]
  busy s _ := by unfold perRun; split <;> simp
  period k _ := by simp [perH]
  sep k _ a ha b hb hab := by simp [perH] at ha hb ⊢; omega
  job k hk s h := by
    simp only [perH, Finset.mem_singleton] at hk
    subst hk
    simp only [perRun] at h
    split at h
    · simpa [perH]
    · simp at h
  cost k hk t r := by
    calc ((Finset.range t).filter (fun s => perRun s = some (k + 1) ∧ perH.job k s = r)).card
        ≤ ({r} : Finset ℕ).card := by
          apply Finset.card_le_card
          intro s hs
          rw [Finset.mem_filter] at hs
          simp only [perH] at hs
          simp [hs.2.2]
      _ = 1 := rfl

/-- With that handler, a computation of 8 slots completes within the first 10. -/
theorem perRun_completes : 8 ≤ (slots perRun 0 10).card :=
  response_time_bound perH perRun 8 10 (perRun_admissible 8) (by decide)

/-! ### The executable check -/

theorem sumTo_eq (f : ℕ → ℕ) (n : ℕ) : sumTo f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo, ih, Finset.sum_range_succ]

/-- The handlers of a list `(cₖ, Tₖ)`, with any activations and attribution. -/
def ofList (hs : List (ℕ × ℕ)) (rel : ℕ → Set ℕ) (job : ℕ → ℕ → ℕ) : Handlers :=
  ⟨Finset.range hs.length, fun k => (hs.getD k (0, 1)).1, fun k => (hs.getD k (0, 1)).2, rel, job⟩

/-- **Soundness of the check.** If `rtaHolds C hs R`, every admissible schedule of a
    computation of `C` slots under the handlers `hs` gives the computation its `C` slots
    within the first `R`. -/
theorem rtaHolds_sound (C : ℕ) (hs : List (ℕ × ℕ)) (R : ℕ) (h : rtaHolds C hs R = true)
    (rel : ℕ → Set ℕ) (job : ℕ → ℕ → ℕ) (run : ℕ → Option ℕ)
    (hA : Admissible (ofList hs rel job) run C) : C ≤ (slots run 0 R).card := by
  apply response_time_bound _ run C R hA
  simp only [rtaHolds, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [demand, ofList, interference, sumTo_eq] at h ⊢
  exact h.2

/-- A claim checked for a cost bound `C` also holds for any smaller cost. -/
theorem rtaHolds_mono {C C' : ℕ} {hs : List (ℕ × ℕ)} {R : ℕ} (hC : C' ≤ C)
    (h : rtaHolds C hs R = true) : rtaHolds C' hs R = true := by
  simp only [rtaHolds, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, by omega⟩

theorem rtaSearch_sound (C : ℕ) (hs : List (ℕ × ℕ)) (limit fuel R₀ R : ℕ)
    (h : rtaSearch C hs limit fuel R₀ = some R) : C + interference hs R ≤ R := by
  induction fuel generalizing R₀ with
  | zero => simp [rtaSearch] at h
  | succ n ih =>
    simp only [rtaSearch] at h
    split at h
    · cases h
    · split at h
      · next he => cases h; omega
      · exact ih _ h

theorem exList : rtaHolds 100 [(10, 50), (3, 20)] 167 = true := by decide

end ImperativeOptimization.Interrupts
