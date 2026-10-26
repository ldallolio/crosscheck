import Mathlib.Data.Option.Basic

namespace ImperativeOptimization

/--
The state space `S` represents memory configurations (e.g., `Var → Val`).
Undefinition or divergence is modeled using a pointed domain `PointedState S := Option S`,
where `none` represents ⊥_f.
-/
abbrev PointedState (S : Type) : Type := Option S

/-- A strictly partial state transition relation on `S`. -/
def PartialTransition (S : Type) : Type := S → Option S

/-- Extends a partial transition function `f` to a total operator `f_⊥ : S_⊥ → S_⊥`. -/
def extendToPointed {S : Type} (f : PartialTransition S) : PointedState S → PointedState S
  | none => none
  | some s => f s

/-- Identity state transition operator. -/
def stateId {S : Type} : PointedState S → PointedState S := id

/-- Composition of state transition operators. -/
def stateComp {S : Type} (f g : PointedState S → PointedState S) : PointedState S → PointedState S :=
  g ∘ f

end ImperativeOptimization