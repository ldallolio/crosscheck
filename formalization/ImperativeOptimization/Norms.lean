/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import Mathlib.Tactic
import ImperativeOptimization.Dominance
import ImperativeOptimization.Ranking

/-!
# Subadditive cost norms

The upper bounds of the trace layer are stated in the paper for every subadditive cost norm
(`def:subadditive-norm`): `‖ε‖ = 0` and `‖u · v‖ ≤ ‖u‖ + ‖v‖`. The other modules prove them
for the instruction count `cost` and the weighted cost `wcost`; this module proves them for an
arbitrary subadditive norm, of which both are instances:

* `CostNorm.flatten_le`: `‖t₁ ⋯ tₙ‖ ≤ Σⱼ ‖tⱼ‖`;
* `CostNorm.runTrace_le` (`prop:worst-case-step`);
* `CostNorm.condTrace_le` (`prop:tropical-dominance`) and `CostNorm.blocks_le`, `k` sequential
  conditional blocks whatever state each is entered in (`prop:tropical-collapse`);
* `CostNorm.wcet_bound` (`thm:lyapunov-bound`, second part).

It also proves the parts of `prop:poset-properties`, `thm:minimal-trace` and `prop:min_x`
about the prefix order that are not in `Trace` and `WhileLoop`: `ε` is the least element, the
strict order is well-founded (`order_nil`, `order_wf`), the minimal exiting iteration gives the
least exiting trace (`minimal_iteration_least`), and the executed traces of a loop form a
prefix chain (`runTrace_prefix`).
-/

namespace ImperativeOptimization

variable {Instr S : Type}

/-- A subadditive cost norm on traces (paper: `def:subadditive-norm`). -/
structure CostNorm (Instr : Type) where
  norm : Trace Instr → ℕ
  norm_nil : norm [] = 0
  norm_append : ∀ u v : Trace Instr, norm (u ++ v) ≤ norm u + norm v

/-- The instruction count is a subadditive cost norm. -/
def costNorm : CostNorm Instr where
  norm := cost
  norm_nil := rfl
  norm_append u v := by rw [cost_additive]

/-- The weighted cost is a subadditive cost norm. -/
def wcostNorm (ω : Instr → ℕ) : CostNorm Instr where
  norm := wcost ω
  norm_nil := wcost_nil ω
  norm_append u v := by rw [wcost_append]

namespace CostNorm

/-- Subadditivity over a list of traces: `‖t₁ ⋯ tₙ‖ ≤ Σⱼ ‖tⱼ‖`. -/
theorem flatten_le (N : CostNorm Instr) :
    ∀ ts : List (Trace Instr), N.norm ts.flatten ≤ (ts.map N.norm).sum
  | [] => by simp [N.norm_nil]
  | t :: ts => by
    simp only [List.flatten_cons, List.map_cons, List.sum_cons]
    exact le_trans (N.norm_append t ts.flatten) (Nat.add_le_add_left (flatten_le N ts) _)

/-- Worst-case step bound for a subadditive norm (paper: `prop:worst-case-step`). -/
theorem runTrace_le (N : CostNorm Instr) (τ : S → Trace Instr) (f : S → S) (W : ℕ)
    (hW : ∀ s, N.norm (τ s) ≤ W) : ∀ (n : ℕ) (s : S), N.norm (runTrace τ f n s) ≤ n * W
  | 0, s => by simp [runTrace, N.norm_nil]
  | n + 1, s => by
    simp only [runTrace]
    have h1 := N.norm_append (τ s) (runTrace τ f n (f s))
    have h2 := runTrace_le N τ f W hW n (f s)
    have h3 := hW s
    calc N.norm (τ s ++ runTrace τ f n (f s)) ≤ W + n * W := by omega
      _ = (n + 1) * W := by ring

/-- Branch rule for a subadditive norm (paper: `prop:tropical-dominance`). -/
theorem condTrace_le (N : CostNorm Instr) (c : S → Bool) (t_c t_then t_else : Trace Instr)
    (s : S) :
    N.norm (condTrace c t_c t_then t_else s) ≤ N.norm t_c + max (N.norm t_then) (N.norm t_else) := by
  unfold condTrace
  refine le_trans (N.norm_append _ _) (Nat.add_le_add_left ?_ _)
  cases c s <;> simp

/-- A conditional block: guard, guard trace, `then` trace, `else` trace. -/
structure Block (Instr S : Type) where
  test : S → Bool
  guard : Trace Instr
  thenT : Trace Instr
  elseT : Trace Instr

/-- Tropical branch collapsing for `k` sequential conditional blocks and a subadditive norm
    (paper: `prop:tropical-collapse`): if the `j`-th part of the executed trace is the trace
    of the `j`-th block in some state (each block may be entered in a different state), the
    whole trace costs at most `Σⱼ (‖t_{c_j}‖ + max(‖t_then‖, ‖t_else‖))`. -/
theorem blocks_le (N : CostNorm Instr) :
    ∀ (bs : List (Block Instr S)) (ts : List (Trace Instr)),
      List.Forall₂ (fun t b => ∃ s, t = condTrace b.test b.guard b.thenT b.elseT s) ts bs →
      N.norm ts.flatten ≤
        (bs.map (fun b => N.norm b.guard + max (N.norm b.thenT) (N.norm b.elseT))).sum
  | [], [], _ => by simp [N.norm_nil]
  | b :: bs, t :: ts, h => by
    obtain ⟨⟨s, rfl⟩, hts⟩ := List.forall₂_cons.mp h
    simp only [List.flatten_cons, List.map_cons, List.sum_cons]
    exact le_trans (N.norm_append _ _)
      (Nat.add_le_add (N.condTrace_le b.test b.guard b.thenT b.elseT s) (blocks_le N bs ts hts))
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- Lyapunov cost dominance bound for a subadditive norm (paper: `thm:lyapunov-bound`,
    second part): a run of `n` iterations under a ranking potential costs at most
    `N̄(s₀) · W`. -/
theorem wcet_bound (N : CostNorm Instr) (τ : S → Trace Instr) (W : ℕ)
    (hW : ∀ s, N.norm (τ s) ≤ W)
    (cond : S → Bool) (f : S → S) (V : S → ℤ) (Δ : ℤ) (hΔ : 0 < Δ)
    (h_decr : ∀ s, cond s = true → V (f s) ≤ V s - Δ)
    (h_pos : ∀ s, cond s = true → 0 < V s)
    (s₀ : S) (n : ℕ) (h_run : ∀ k < n, cond (f^[k] s₀) = true) :
    N.norm (runTrace τ f n s₀) ≤ rankBound (V s₀) Δ * W :=
  le_trans (N.runTrace_le τ f W hW n s₀)
    (Nat.mul_le_mul_right W (ranking_bound cond f V Δ hΔ h_decr h_pos s₀ n h_run))

end CostNorm

/-! ### The prefix order -/

/-- `ε` is the least element of `⊑` (paper: `prop:poset-properties`). -/
theorem order_nil (t : Trace Instr) : ([] : Trace Instr) ⊑ t := ⟨t, rfl⟩

/-- The strict prefix order is well-founded (paper: `prop:poset-properties`). -/
theorem order_wf : WellFounded (fun u w : Trace Instr => u ⊑ w ∧ u ≠ w) := by
  refine Subrelation.wf ?_ (InvImage.wf (fun t : Trace Instr => t.length) wellFounded_lt)
  intro u w ⟨⟨v, hv⟩, hne⟩
  show u.length < w.length
  subst hv
  rcases v with _ | ⟨a, v⟩
  · exact absurd (List.append_nil u).symm hne
  · simp

/-- The minimal exiting iteration gives the least exiting trace (paper: `thm:minimal-trace`):
    `t^n̄ ⊑ t^n` for every exiting `n`. -/
theorem minimal_iteration_least (evalTrace : Trace Instr → Option S → Option S) (t : Trace Instr)
    (cond : S → Bool) (s₀ : S) {n_bar n : ℕ}
    (hmin : ∀ k < n_bar, ¬ ExitsAt evalTrace t cond s₀ k) (hn : ExitsAt evalTrace t cond s₀ n) :
    (t ^[n_bar]) ⊑ (t ^[n]) := by
  apply iter_monotone
  by_contra h
  exact hmin n (by omega) hn

/-- The executed traces of a loop form a prefix chain (paper: `prop:min_x`): fewer iterations
    give a prefix, so the trace of the minimal exiting iteration is the least exiting one. -/
theorem runTrace_prefix (τ : S → Trace Instr) (f : S → S) :
    ∀ {n m : ℕ} (s : S), n ≤ m → runTrace τ f n s ⊑ runTrace τ f m s
  | 0, _, _, _ => order_nil _
  | n + 1, 0, _, h => absurd h (by omega)
  | n + 1, m + 1, s, h => by
    obtain ⟨v, hv⟩ := runTrace_prefix τ f (n := n) (m := m) (f s) (by omega)
    exact ⟨v, by simp only [runTrace, hv, List.append_assoc]⟩

end ImperativeOptimization
