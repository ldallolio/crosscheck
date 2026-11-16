/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Tactic

/-!
# Fork-join: work, span, and greedy scheduling of independent tasks

A fork-join block runs independent tasks of costs `w₁, …, wₙ` and joins. Its *work* is
`Σ wᵢ` (its cost on one processor) and its *span* is `max wᵢ` (its duration with a
processor per task). On `p` processors, a greedy (list) scheduler starts each task, in
order, on a processor that becomes free first, i.e. one of least load. Graham's bound
(Graham 1966) states that the resulting makespan `M` satisfies `p·M ≤ Σ wᵢ + p·max wᵢ`,
i.e. `M ≤ work/p + span`; it is proved here, together with its monotonicity in the costs,
so that certified cost bounds `Bᵢ ≥ wᵢ` of the tasks give `M ≤ (Σ Bᵢ)/p + max Bᵢ`.

Model: tasks are independent (no shared variables, locks or communication), a processor
runs one task at a time without preemption, and a task's duration on a processor is its
cost. A task scheduled later in the list is at the head of the list below.
-/

namespace ImperativeOptimization.ForkJoin

/-- `maxL ws = max wᵢ` (0 for no task). -/
def maxL : List ℕ → ℕ
  | [] => 0
  | w :: ws => max w (maxL ws)

/-- `Greedy p ws L`: scheduling the tasks `ws` (the last one at the head) greedily on `p`
    processors gives the loads `L`. -/
inductive Greedy (p : ℕ) : List ℕ → (Fin p → ℕ) → Prop
  | nil : Greedy p [] (fun _ => 0)
  | cons {ws : List ℕ} {L : Fin p → ℕ} {w : ℕ} (m : Fin p) :
      Greedy p ws L → (∀ i, L m ≤ L i) → Greedy p (w :: ws) (Function.update L m (L m + w))

/-- **Graham's bound.** The loads sum to the work, and every load (so the makespan) is at
    most `work / p + span`. -/
theorem greedy_bound {p : ℕ} {ws : List ℕ} {L : Fin p → ℕ} (h : Greedy p ws L) :
    (∑ i, L i = ws.sum) ∧ ∀ i, p * L i ≤ ws.sum + p * maxL ws := by
  induction h with
  | nil => simp
  | @cons ws L w m _ hmin ih =>
    obtain ⟨hsum, hle⟩ := ih
    have hpm : p * L m ≤ ∑ i, L i := by
      have := Finset.card_nsmul_le_sum Finset.univ L (L m) (fun i _ => hmin i)
      simpa [Finset.card_univ, Fintype.card_fin] using this
    have hsum' : ∑ i, Function.update L m (L m + w) i = (w :: ws).sum := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ m)]
      have := Finset.add_sum_erase Finset.univ L (Finset.mem_univ m)
      simp only [List.sum_cons]
      rw [Finset.sdiff_singleton_eq_erase]
      omega
    refine ⟨hsum', fun i => ?_⟩
    simp only [List.sum_cons, maxL]
    by_cases hi : i = m
    · subst hi
      simp only [Function.update_self]
      have : p * w ≤ p * max w (maxL ws) := Nat.mul_le_mul_left _ (le_max_left _ _)
      rw [Nat.mul_add]
      omega
    · rw [Function.update_of_ne hi]
      have := hle i
      have : p * maxL ws ≤ p * max w (maxL ws) := Nat.mul_le_mul_left _ (le_max_right _ _)
      omega

/-- A greedy schedule exists for any list of tasks on at least one processor. -/
theorem greedy_exists {p : ℕ} (hp : 0 < p) (ws : List ℕ) : ∃ L, Greedy p ws L := by
  induction ws with
  | nil => exact ⟨_, Greedy.nil⟩
  | cons w ws ih =>
    obtain ⟨L, hL⟩ := ih
    obtain ⟨m, _, hm⟩ := Finset.exists_min_image Finset.univ L ⟨⟨0, hp⟩, Finset.mem_univ _⟩
    exact ⟨_, Greedy.cons (w := w) m hL (fun i => hm i (Finset.mem_univ i))⟩

theorem maxL_mono {ws bs : List ℕ} (h : List.Forall₂ (· ≤ ·) ws bs) : maxL ws ≤ maxL bs := by
  induction h with
  | nil => exact le_refl _
  | cons hab _ ih => exact max_le_max hab ih

theorem sum_mono {ws bs : List ℕ} (h : List.Forall₂ (· ≤ ·) ws bs) : ws.sum ≤ bs.sum := by
  induction h with
  | nil => exact le_refl _
  | cons hab _ ih => simp only [List.sum_cons]; omega

/-- **Fork-join with certified task bounds.** If the actual costs `ws` of the tasks are at
    most their bounds `bs`, every processor's load under a greedy schedule is at most
    `(Σ bᵢ)/p + max bᵢ`. -/
theorem forkjoin_bound {p : ℕ} {ws bs : List ℕ} {L : Fin p → ℕ} (h : Greedy p ws L)
    (hle : List.Forall₂ (· ≤ ·) ws bs) (i : Fin p) : p * L i ≤ bs.sum + p * maxL bs := by
  have := (greedy_bound h).2 i
  have h1 := sum_mono hle
  have h2 : p * maxL ws ≤ p * maxL bs := Nat.mul_le_mul_left _ (maxL_mono hle)
  omega

/-- For the loads of a greedy schedule, `work ≤ p · makespan` (for every schedule, and for
    the span: `makespan_lower`). -/
theorem load_lower {p : ℕ} {ws : List ℕ} {L : Fin p → ℕ} (h : Greedy p ws L) :
    ws.sum ≤ p * Finset.univ.sup L := by
  rw [← (greedy_bound h).1]
  have := Finset.sum_le_card_nsmul Finset.univ L (Finset.univ.sup L)
    (fun i hi => Finset.le_sup hi)
  simpa [Finset.card_univ, Fintype.card_fin] using this

/-- The load of processor `i` when task `j` (of cost `w j`) runs on processor `a j`. -/
def loadOf {p n : ℕ} (w : Fin n → ℕ) (a : Fin n → Fin p) (i : Fin p) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => a j = i), w j

/-- **Lower bounds for every schedule.** Whatever the assignment `a` of the tasks to the
    `p` processors, the makespan (the largest load) is at least `work / p` and at least
    the cost of every task (so at least the span). Graham's bound is thus within a factor
    two of the best schedule. -/
theorem makespan_lower {p n : ℕ} (w : Fin n → ℕ) (a : Fin n → Fin p) :
    (∑ j, w j ≤ p * Finset.univ.sup (loadOf w a)) ∧
    ∀ j, w j ≤ Finset.univ.sup (loadOf w a) := by
  constructor
  · calc ∑ j, w j = ∑ i, loadOf w a i := by
          unfold loadOf
          exact (Finset.sum_fiberwise Finset.univ a w).symm
      _ ≤ ∑ _i : Fin p, Finset.univ.sup (loadOf w a) :=
          Finset.sum_le_sum (fun i _ => Finset.le_sup (f := loadOf w a) (Finset.mem_univ i))
      _ = p * Finset.univ.sup (loadOf w a) := by simp
  · intro j
    have h1 : w j ≤ loadOf w a (a j) := by
      unfold loadOf
      exact Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, rfl⟩)
    exact h1.trans (Finset.le_sup (f := loadOf w a) (Finset.mem_univ (a j)))

/-- Example: tasks of costs 4, 3, 3, 2 on 2 processors (scheduled 2, 3, 3, 4): loads 7 and
    5; the bound gives `2·7 ≤ 12 + 2·4`. -/
theorem example_bound : ∃ L : Fin 2 → ℕ, Greedy 2 [4, 3, 3, 2] L ∧ ∀ i, 2 * L i ≤ 12 + 2 * 4 := by
  obtain ⟨L, hL⟩ := greedy_exists (p := 2) (by norm_num) [4, 3, 3, 2]
  exact ⟨L, hL, fun i => by simpa [maxL] using (greedy_bound hL).2 i⟩

end ImperativeOptimization.ForkJoin
