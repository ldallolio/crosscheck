/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/

/-!
# Response-time claims: the executable check (no mathlib)

A claim: a computation of cost at most `C`, preempted by handlers `(cₖ, Tₖ)` (cost at most
`cₖ` per activation, at least `Tₖ` between activations), completes within `R`. The check is
`C + Σₖ cₖ·⌈R/Tₖ⌉ ≤ R` with every `Tₖ > 0`; `Interrupts.rtaHolds_sound` relates it to
`Interrupts.response_time_bound`.
-/

namespace ImperativeOptimization.Interrupts

/-- `⌈a / b⌉` for `b > 0`. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- `Σ_{k < n} f k`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- The handlers' interference over a window of length `R`. -/
def interference (hs : List (Nat × Nat)) (R : Nat) : Nat :=
  sumTo (fun k => (hs.getD k (0, 1)).1 * ceilDiv R (hs.getD k (0, 1)).2) hs.length

/-- The claim `C + Σₖ cₖ·⌈R/Tₖ⌉ ≤ R`, every `Tₖ > 0`. -/
def rtaHolds (C : Nat) (hs : List (Nat × Nat)) (R : Nat) : Bool :=
  hs.all (fun h => decide (0 < h.2)) && decide (C + interference hs R ≤ R)

/-- The least `R` of the iteration from `C`, if it is reached within `fuel` steps and is at
    most `limit`. -/
def rtaSearch (C : Nat) (hs : List (Nat × Nat)) (limit : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, R =>
    let R' := C + interference hs R
    if R' > limit then none else if R' = R then some R else rtaSearch C hs limit fuel R'

end ImperativeOptimization.Interrupts
