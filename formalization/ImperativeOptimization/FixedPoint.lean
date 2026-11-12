/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import Mathlib.Logic.Function.Iterate
import ImperativeOptimization.Trace

namespace ImperativeOptimization

variable {Instr S : Type}

/--
Semantic evaluation map `evalTrace` interpreting traces as state transformations.
-/
def evalTrace (interp : Instr → S → Option S) : Trace Instr → Option S → Option S
  | [], s => s
  | i :: is, some s => match interp i s with
                      | some s' => evalTrace interp is (some s')
                      | none => none
  | _ :: _, none => none

theorem evalTrace_none (interp : Instr → S → Option S) (t : Trace Instr) :
    evalTrace interp t none = none := by
  cases t with
  | nil => rfl
  | cons i is => rfl

theorem evalTrace_concat (interp : Instr → S → Option S) (t₁ t₂ : Trace Instr) (s : Option S) :
    evalTrace interp (t₁ ++ t₂) s = evalTrace interp t₂ (evalTrace interp t₁ s) := by
  induction t₁ generalizing s with
  | nil => rfl
  | cons i is ih =>
    cases s with
    | none =>
      rw [evalTrace_none, evalTrace_none, evalTrace_none]
    | some s' =>
      change (match interp i s' with
        | some s'' => evalTrace interp (is ++ t₂) (some s'')
        | none => none) = evalTrace interp t₂ (match interp i s' with
        | some s'' => evalTrace interp is (some s'')
        | none => none)
      cases h : interp i s' with
      | none =>
        rw [evalTrace_none]
      | some s'' =>
        exact ih (some s'')

/-- The valuation of an iterated trace is the iterated valuation:
    `⟦t^n⟧ = ⟦t⟧^n` (monoid homomorphism restricted to powers). -/
theorem evalTrace_iter (interp : Instr → S → Option S) (t : Trace Instr) (n : ℕ)
    (s : Option S) :
    evalTrace interp (t ^[n]) s = (evalTrace interp t)^[n] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show evalTrace interp ((t ^[n]) ++ t) s = _
    rw [evalTrace_concat, ih, Function.iterate_succ_apply']

/-- One-step unfolding of the valuation of `t^n`: `⟦t^(m+1)⟧ s₀ = ⟦t⟧ (⟦t^m⟧ s₀)`.
    (Auxiliary; the paper's extensional equivalence theorem is `while_trace_semantics`
    in `WhileLoop`.) -/
theorem solution_soundness
    (interp : Instr → S → Option S) (t : Trace Instr) (n : ℕ) (s₀ : S) :
    evalTrace interp (t ^[n]) (some s₀) =
      match n with
      | 0 => some s₀
      | m + 1 => evalTrace interp t (evalTrace interp (t ^[m]) (some s₀)) := by
  cases n with
  | zero => rfl
  | succ m =>
    dsimp [traceIter]
    rw [evalTrace_concat]

end ImperativeOptimization
