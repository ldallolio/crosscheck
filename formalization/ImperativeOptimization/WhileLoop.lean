/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Logic.Function.Iterate
import ImperativeOptimization.State
import ImperativeOptimization.FixedPoint
import ImperativeOptimization.OperationalSemantics

namespace ImperativeOptimization

/-!
# While loops: big-step semantics versus trace minimisation

This module connects the optimisation view of a loop (find the minimal iteration
count `n̄` whose state falsifies the continuation condition) with a standard
inductive big-step semantics of `while cond do body`.

* `whileBigStep_iff_minimalExit` : the big-step semantics relates `s₀` to `s̄`
  iff `s̄` is the state reached at the minimal exiting iteration.
* `while_trace_semantics` : the same statement phrased with the trace valuation
  `evalTrace` and the iterated body trace `t^n`.
* `runTrace_cost_le` : worst-case step bound for bodies whose emitted trace
  depends on the state (data-dependent branching).
-/

variable {Instr S : Type}

/-- Standard big-step semantics of `while cond do f`, where the body `f` is a
    partial state transition (`none` = fault / undefined). -/
inductive WhileBigStep (cond : S → Bool) (f : S → Option S) : S → S → Prop
  | exit {s : S} : cond s = false → WhileBigStep cond f s s
  | step {s s' s'' : S} : cond s = true → f s = some s' →
      WhileBigStep cond f s' s'' → WhileBigStep cond f s s''

/-- `n` is the minimal exiting iteration from `s₀`, reaching the terminal state `sf`:
    the `n`-th iterate is defined and falsifies `cond`, while every earlier
    iterate is defined and satisfies `cond`. -/
def MinimalExit (cond : S → Bool) (f : S → Option S) (s₀ : S) (n : ℕ) (sf : S) : Prop :=
  (extendToPointed f)^[n] (some s₀) = some sf ∧ cond sf = false ∧
  ∀ k < n, ∃ s, (extendToPointed f)^[k] (some s₀) = some s ∧ cond s = true

/-- `⊥` is absorbing for the iterated pointed extension. -/
theorem extendToPointed_iterate_none (f : S → Option S) (n : ℕ) :
    (extendToPointed f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih

theorem WhileBigStep.minimalExit {cond : S → Bool} {f : S → Option S} {s₀ sf : S}
    (h : WhileBigStep cond f s₀ sf) : ∃ n, MinimalExit cond f s₀ n sf := by
  induction h with
  | exit hc => exact ⟨0, rfl, hc, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | @step s s' s'' hc hf _ ih =>
    rcases ih with ⟨n, h1, h2, h3⟩
    refine ⟨n + 1, ?_, h2, ?_⟩
    · rw [Function.iterate_succ_apply]
      show (extendToPointed f)^[n] (f s) = some s''
      rw [hf]
      exact h1
    · intro k hk
      cases k with
      | zero => exact ⟨s, rfl, hc⟩
      | succ k =>
        rcases h3 k (by omega) with ⟨x, hx1, hx2⟩
        refine ⟨x, ?_, hx2⟩
        rw [Function.iterate_succ_apply]
        show (extendToPointed f)^[k] (f s) = some x
        rw [hf]
        exact hx1

theorem MinimalExit.whileBigStep {cond : S → Bool} {f : S → Option S} :
    ∀ (n : ℕ) {s₀ sf : S}, MinimalExit cond f s₀ n sf → WhileBigStep cond f s₀ sf := by
  intro n
  induction n with
  | zero =>
    intro s₀ sf h
    rcases h with ⟨h1, h2, _⟩
    have hs : s₀ = sf := Option.some.inj h1
    subst hs
    exact WhileBigStep.exit h2
  | succ n ih =>
    intro s₀ sf h
    rcases h with ⟨h1, h2, h3⟩
    rcases h3 0 (Nat.succ_pos n) with ⟨x, hx1, hx2⟩
    have hx : s₀ = x := Option.some.inj hx1
    subst hx
    rw [Function.iterate_succ_apply] at h1
    change (extendToPointed f)^[n] (f s₀) = some sf at h1
    cases hf : f s₀ with
    | none =>
      rw [hf, extendToPointed_iterate_none] at h1
      cases h1
    | some s' =>
      rw [hf] at h1
      refine WhileBigStep.step hx2 hf (ih ⟨h1, h2, ?_⟩)
      intro k hk
      rcases h3 (k + 1) (by omega) with ⟨y, hy1, hy2⟩
      rw [Function.iterate_succ_apply] at hy1
      change (extendToPointed f)^[k] (f s₀) = some y at hy1
      rw [hf] at hy1
      exact ⟨y, hy1, hy2⟩

/-- **Loop execution as minimisation.** The big-step semantics of a while loop
    coincides with evaluation at the minimal exiting iteration count. -/
theorem whileBigStep_iff_minimalExit (cond : S → Bool) (f : S → Option S) (s₀ sf : S) :
    WhileBigStep cond f s₀ sf ↔ ∃ n, MinimalExit cond f s₀ n sf :=
  ⟨fun h => h.minimalExit, fun ⟨n, h⟩ => MinimalExit.whileBigStep n h⟩

/-- The minimal exiting iteration count and the terminal state are unique. -/
theorem MinimalExit.unique {cond : S → Bool} {f : S → Option S} {s₀ sf sf' : S} {n n' : ℕ}
    (h : MinimalExit cond f s₀ n sf) (h' : MinimalExit cond f s₀ n' sf') :
    n = n' ∧ sf = sf' := by
  rcases h with ⟨h1, h2, h3⟩
  rcases h' with ⟨h1', h2', h3'⟩
  have hn : n = n' := by
    rcases Nat.lt_trichotomy n n' with hlt | heq | hgt
    · rcases h3' n hlt with ⟨x, hx1, hx2⟩
      rw [h1] at hx1
      have hx : sf = x := Option.some.inj hx1
      subst hx
      rw [h2] at hx2
      cases hx2
    · exact heq
    · rcases h3 n' hgt with ⟨x, hx1, hx2⟩
      rw [h1'] at hx1
      have hx : sf' = x := Option.some.inj hx1
      subst hx
      rw [h2'] at hx2
      cases hx2
  subst hn
  rw [h1] at h1'
  exact ⟨rfl, Option.some.inj h1'⟩

/-- Determinism of the big-step semantics. -/
theorem WhileBigStep.deterministic {cond : S → Bool} {f : S → Option S} {s₀ sf sf' : S}
    (h : WhileBigStep cond f s₀ sf) (h' : WhileBigStep cond f s₀ sf') : sf = sf' := by
  rcases h.minimalExit with ⟨n, hn⟩
  rcases h'.minimalExit with ⟨n', hn'⟩
  exact (hn.unique hn').2

/-- The trace valuation is the pointed extension of its restriction to defined states. -/
theorem evalTrace_eq_extend (interp : Instr → S → Option S) (t : Trace Instr) :
    evalTrace interp t = extendToPointed (fun s => evalTrace interp t (some s)) := by
  funext x
  cases x with
  | none => exact evalTrace_none interp t
  | some s => rfl

/-- **Extensional equivalence (trace form).** For a loop whose body is the trace `t`,
    the big-step semantics relates `s₀` to `sf` iff `sf = ⟦t^n⟧(s₀)` for the minimal
    `n` such that `⟦t^n⟧(s₀)` is defined and falsifies the continuation condition. -/
theorem while_trace_semantics (interp : Instr → S → Option S) (t : Trace Instr)
    (cond : S → Bool) (s₀ sf : S) :
    WhileBigStep cond (fun s => evalTrace interp t (some s)) s₀ sf ↔
      ∃ n, evalTrace interp (t ^[n]) (some s₀) = some sf ∧ cond sf = false ∧
        ∀ k < n, ∃ s, evalTrace interp (t ^[k]) (some s₀) = some s ∧ cond s = true := by
  rw [whileBigStep_iff_minimalExit]
  unfold MinimalExit
  simp only [evalTrace_iter, ← evalTrace_eq_extend]

/- =========================================================================
   Total bodies: link with `MinimalIter` / `LoopConstraint`
   ========================================================================= -/

theorem extendToPointed_iterate_total (g : S → S) (n : ℕ) (s : S) :
    (extendToPointed (fun x => some (g x)))^[n] (some s) = some (g^[n] s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (g s)

/-- For a total body `g`, big-step execution agrees with iterating `g` the minimal
    number of times. -/
theorem whileBigStep_total_iff (cond : S → Bool) (g : S → S) (s₀ sf : S) :
    WhileBigStep cond (fun s => some (g s)) s₀ sf ↔
      ∃ n, MinimalIter cond g s₀ n ∧ sf = g^[n] s₀ := by
  rw [whileBigStep_iff_minimalExit]
  constructor
  · rintro ⟨n, h1, h2, h3⟩
    rw [extendToPointed_iterate_total] at h1
    have hs : g^[n] s₀ = sf := Option.some.inj h1
    refine ⟨n, ⟨by rw [hs]; exact h2, fun k hk => ?_⟩, hs.symm⟩
    rcases h3 k hk with ⟨x, hx1, hx2⟩
    rw [extendToPointed_iterate_total] at hx1
    rw [Option.some.inj hx1]
    exact hx2
  · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
    exact ⟨n, extendToPointed_iterate_total g n s₀, h1,
      fun k hk => ⟨_, extendToPointed_iterate_total g k s₀, h2 k hk⟩⟩

/-- Soundness of `solveLoop`: if `n̄` is a loop solution, the big-step semantics
    reaches exactly the state computed by `solveLoop`. -/
theorem solveLoop_sound (lc : LoopConstraint S) (s₀ : S) (n_bar : ℕ)
    (h : isLoopSolution lc s₀ n_bar) :
    WhileBigStep lc.cond (fun s => some (lc.stepState s)) s₀ (solveLoop lc s₀ n_bar).1 :=
  (whileBigStep_total_iff lc.cond lc.stepState s₀ _).mpr ⟨n_bar, h, rfl⟩

/- =========================================================================
   State-dependent body traces and the worst-case step bound
   ========================================================================= -/

/-- Executed trace of `n` iterations of a body whose emitted path trace `τ s`
    depends on the current state `s` (data-dependent branching), with state
    update `f`. -/
def runTrace (τ : S → Trace Instr) (f : S → S) : ℕ → S → Trace Instr
  | 0, _ => []
  | n + 1, s => τ s ++ runTrace τ f n (f s)

/-- For a straight-line body (state-independent trace) `runTrace` is `t^n`. -/
theorem runTrace_const (t : Trace Instr) (f : S → S) (n : ℕ) (s : S) :
    runTrace (fun _ => t) f n s = t ^[n] := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    show t ++ runTrace (fun _ => t) f n (f s) = t ^[n + 1]
    rw [ih, traceIter_succ]

/-- **Worst-case step bound.** If every path through the body costs at most `W`,
    then `n` iterations cost at most `n · W`. -/
theorem runTrace_cost_le (τ : S → Trace Instr) (f : S → S) (W : ℕ)
    (hW : ∀ s, cost (τ s) ≤ W) (n : ℕ) (s : S) :
    cost (runTrace τ f n s) ≤ n * W := by
  induction n generalizing s with
  | zero => simp [runTrace, cost]
  | succ n ih =>
    show cost (τ s ++ runTrace τ f n (f s)) ≤ (n + 1) * W
    rw [cost_additive]
    have h1 := hW s
    have h2 := ih (f s)
    have h3 : (n + 1) * W = n * W + W := by ring
    omega

/-- Worst-case step bound for an arbitrary weighted cost norm. -/
theorem runTrace_wcost_le (ω : Instr → ℕ) (τ : S → Trace Instr) (f : S → S) (W : ℕ)
    (hW : ∀ s, wcost ω (τ s) ≤ W) (n : ℕ) (s : S) :
    wcost ω (runTrace τ f n s) ≤ n * W := by
  induction n generalizing s with
  | zero => simp [runTrace, wcost]
  | succ n ih =>
    show wcost ω (τ s ++ runTrace τ f n (f s)) ≤ (n + 1) * W
    rw [wcost_append]
    have h1 := hW s
    have h2 := ih (f s)
    have h3 : (n + 1) * W = n * W + W := by ring
    omega

end ImperativeOptimization
