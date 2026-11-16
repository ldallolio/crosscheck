/-
Copyright (c) 2026 Luca Dall'Olio. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Luca Dall'Olio
-/
import ImperativeOptimization.MiniCCore

/-!
# Mini-C with early exits and `switch`: definitions

`JStmt` extends the statements of mini-C (`MStmt`, which have no jumps) with `break`,
`continue` and `return` inside loops and with `switch`, as they appear in C. Its meaning
is given directly in `ImperativeOptimization.MiniCJump` (`JExec`, `JPre`: big-step
semantics with outcomes, the usual way of giving C's jumps a meaning). Here:

* `elim`: the elimination of the jumps with *flag variables* (`break` and `continue`
  store 1 into a flag of their loop, `return` into a function-wide flag; the loop tests
  read the flags; what follows a jump is moved into the branches that do not jump) and of
  `switch` (each case group under a test of an unknown value), producing an `MStmt`. This
  is the form in which the certificate generator writes these constructs, and it is the
  rewriting the exporter of the plugin did before (now done here, by the checker);
* `validateJ`: the program of the certificate is the lowering of `elim j`.

`MiniCJump.validatedJ_sound` shows that every execution and execution prefix of `j`, in
the direct semantics, costs at most the bound of the validated certificate: the
elimination is proved, not trusted.

The flag variables (`?break<d>`, `?continue<d>`, `?return`) and the variable of the
unknown test of a `switch` (`?case<d>`) are *ghost* variables: the source never reads or
writes them, which `elim` checks syntactically (`MStmt.vars`), and along a nesting path
they are distinct. No mathlib: compiled into the checker program.
-/

namespace ImperativeOptimization.MiniC
open Checker

/-- Statements of mini-C with early exits.
* `basic s`: a statement without jumps (it may contain loops and conditionals);
* `loop w cs body inc fb fc`: `while (cs) { body; inc }` (a `for` loop is its
  initialisation, a `basic` statement, followed by such a loop; `continue` runs `inc`);
  `fb`, `fc` are the flag variables of its `break` and `continue` (not part of the
  meaning, used by `elim` only);
* `brk w`, `cont w`: a jump costing `w`; `ret s`: `return`, after `s` (the evaluation of
  the returned value and the cost of the return);
* `switch w sc gs`: a test costing `w` that enters one of the case groups `gs` (or none)
  and falls through the following ones up to a `break`; which group is entered is not
  modelled (the value is not compared with the labels). `sc` is the ghost variable of
  the unknown test, used by `elim` only;
* `fall gs`: the groups `gs` run in sequence up to a jump (used to state the meaning of
  `switch`; `elim` rejects it);
* `doLoop w cs body fb fc`: `do { body } while (cs)`; `elim` accepts it when its body has
  no `break` or `continue` of its own, as `body` followed by the loop `while (cs) body`. -/
inductive JStmt where
  | basic (s : MStmt)
  | seq (a b : JStmt)
  | ite (w : Nat) (c : MCond) (a b : JStmt)
  | loop (w : Nat) (cs : List MCond) (body : JStmt) (inc : Option MStmt) (fb fc : Option Nat)
  | brk (w : Nat)
  | cont (w : Nat)
  | ret (s : MStmt)
  | switch (w : Nat) (sc : Nat) (gs : List JStmt)
  | fall (gs : List JStmt)
  | doLoop (w : Nat) (cs : List MCond) (body : JStmt) (fb fc : Option Nat)
  deriving Repr

/-! ### Variables of mini-C statements -/

def MExp.vars : MExp → List Nat
  | .var x => [x]
  | .lit _ => []
  | .add a b => a.vars ++ b.vars
  | .sub a b => a.vars ++ b.vars
  | .mul a b => a.vars ++ b.vars
  | .neg a => a.vars
  | .other => []

def MCond.vars : MCond → List Nat
  | .cmp _ a b => a.vars ++ b.vars
  | .not c => c.vars
  | .other => []

/-- Every variable a statement names (read or written). The variables that the lowering
    adds itself are `choiceVar` (tests of unknown value) and `costVar` (statements that
    only cost). -/
def MStmt.vars : MStmt → List Nat
  | .skip => []
  | .assign _ x e => x :: e.vars
  | .divStore _ x _ y _ old => x :: y.vars ++ old.toList
  | .assignU _ x _ e => x :: e.vars
  | .call _ args => args.foldr (fun a acc => a.1 :: a.2.2.vars ++ acc) []
  | .cost _ => []
  | .seq a b => a.vars ++ b.vars
  | .ite _ c a b => c.vars ++ a.vars ++ b.vars
  | .while _ cs body => cs.foldr (fun c acc => c.vars ++ acc) [] ++ body.vars
  | .for_ init _ cs inc body =>
      init.vars ++ cs.foldr (fun c acc => c.vars ++ acc) [] ++ inc.vars ++ body.vars

/-! ### Scans (the same as the exporter's) -/

mutual
/-- A `return` anywhere inside. -/
def JStmt.hasRet : JStmt → Bool
  | .basic _ => false
  | .seq a b => a.hasRet || b.hasRet
  | .ite _ _ a b => a.hasRet || b.hasRet
  | .loop _ _ body _ _ _ => body.hasRet
  | .brk _ => false
  | .cont _ => false
  | .ret _ => true
  | .switch _ _ gs => JStmt.hasRetL gs
  | .fall gs => JStmt.hasRetL gs
  | .doLoop _ _ body _ _ => body.hasRet
def JStmt.hasRetL : List JStmt → Bool
  | [] => false
  | g :: gs => g.hasRet || JStmt.hasRetL gs
end

mutual
/-- A `break` that leaves `j` (not one of a loop or `switch` inside `j`). -/
def JStmt.escB : JStmt → Bool
  | .basic _ => false
  | .seq a b => a.escB || b.escB
  | .ite _ _ a b => a.escB || b.escB
  | .loop .. => false
  | .brk _ => true
  | .cont _ => false
  | .ret _ => false
  | .switch .. => false
  | .fall gs => JStmt.escBL gs
  | .doLoop .. => false
def JStmt.escBL : List JStmt → Bool
  | [] => false
  | g :: gs => g.escB || JStmt.escBL gs
end

mutual
/-- A `continue` that leaves `j` (not one of a loop inside `j`; a `switch` does not stop
    it). -/
def JStmt.escC : JStmt → Bool
  | .basic _ => false
  | .seq a b => a.escC || b.escC
  | .ite _ _ a b => a.escC || b.escC
  | .loop .. => false
  | .brk _ => false
  | .cont _ => true
  | .ret _ => false
  | .switch _ _ gs => JStmt.escCL gs
  | .fall gs => JStmt.escCL gs
  | .doLoop .. => false
def JStmt.escCL : List JStmt → Bool
  | [] => false
  | g :: gs => g.escC || JStmt.escCL gs
end

/-- Does `j` leave the statement list it is in? (A loop or `switch` handles its own
    jumps.) -/
def JStmt.ends (j : JStmt) : Bool := j.hasRet || j.escB || j.escC

/-! ### Elimination of jumps -/

/-- The constructs around the statement being translated: a loop (with the flags of its
    jumps, if it has such jumps) or a `switch`; `rr`: it contains a `return` (the return
    flag was cleared before it); `gh`: its ghost variables. -/
structure Frame where
  isSw : Bool
  fb : Option Nat
  fc : Option Nat
  rr : Bool
  gh : List Nat
  deriving Repr

def ghostsOf (ctx : List Frame) : List Nat := ctx.foldr (fun fr acc => fr.gh ++ acc) []

/-- The `continue` flag of the innermost loop. -/
def nearestCnt : List Frame → Option Nat
  | [] => none
  | fr :: ctx => if fr.isSw then nearestCnt ctx else fr.fc

def flagSet (w f : Nat) (k : Int) : MStmt := .assign w f (.lit k)
def clearTest (f : Nat) : MCond := .cmp .le (.var f) (.lit 0)
/-- `if (f <= 0) a` (a test of weight 0: not code of the source). -/
def unlessF (f : Nat) (a : MStmt) : MStmt := .ite 0 (clearTest f) a .skip

def MStmt.isSkip : MStmt → Bool
  | .skip => true
  | _ => false

/-- `s₁; …; sₙ`. -/
def seqs : List MStmt → MStmt
  | [] => .skip
  | [s] => s
  | s :: ss => .seq s (seqs ss)

def disjoint (l m : List Nat) : Bool := l.all (fun x => !m.contains x)
def nodup : List Nat → Bool
  | [] => true
  | x :: l => !l.contains x && nodup l

/-- The ghost variables of a new construct are fresh along the nesting path. -/
def freshGh (r : Nat) (ctx : List Frame) (gh : List Nat) : Bool :=
  nodup gh && disjoint gh (r :: choiceVar :: costVar :: ghostsOf ctx)

/-- The functions that `s` calls have numbers below `n`. -/
def MStmt.callsBelow (n : Nat) : MStmt → Bool
  | .call f _ => decide (f < n)
  | .seq a b => a.callsBelow n && b.callsBelow n
  | .ite _ _ a b => a.callsBelow n && b.callsBelow n
  | .while _ _ body => body.callsBelow n
  | .for_ init _ _ inc body => init.callsBelow n && inc.callsBelow n && body.callsBelow n
  | _ => true

/-- A statement of the source may name no ghost variable (`G`) and not the variable of
    statements that only cost, and calls only functions numbered below `n` (those before
    it in the certificate file). -/
def cleanS (n : Nat) (G : List Nat) (s : MStmt) : Bool :=
  disjoint s.vars (costVar :: G) && s.callsBelow n
def cleanC (G : List Nat) (c : MCond) : Bool := disjoint c.vars (costVar :: G)

/-- One case group under the unknown test `sc`: `sc := ?; if (sc <= 0) g`. -/
def groupOf (sc : Nat) (g : MStmt) : MStmt :=
  .seq (.assign 0 sc .other) (.ite 0 (clearTest sc) g .skip)

/-- The case groups in sequence, each under the unknown test. -/
def chainOf (sc : Nat) : List MStmt → MStmt
  | [] => .skip
  | g :: gs => .seq (groupOf sc g) (chainOf sc gs)

/-- The loop of a `loop` node, once its flags are cleared: the test is the C test and
    `f <= 0` for each exit flag; the body clears the `continue` flag, runs, then runs
    the increment if no exit flag is set. -/
def whileOf (w : Nat) (cs : List MCond) (exits : List Nat) (fc : Option Nat) (bd : MStmt)
    (inc : Option MStmt) : MStmt :=
  .while w (cs ++ exits.map clearTest)
    (.seq (match fc with | some f => flagSet 0 f 0 | none => .skip)
      (.seq bd (match inc with
        | some u => exits.foldl (fun u f => unlessF f u) u
        | none => .skip)))

/-- What follows a construct that may have set the return flag `r` or the `continue`
    flag `c` runs only if they are 0. -/
def guardTail (r : Option Nat) (c : Option Nat) (k : MStmt) : MStmt :=
  if k.isSkip then .skip
  else
    let k1 := match c with | some f => unlessF f k | none => k
    match r with | some f => unlessF f k1 | none => k1

mutual
/-- `tr r n G ctx j k`: the statement `j` followed by `k` (its continuation: what follows
    `j` in its statement list, already translated), jumps eliminated, in the context
    `ctx`. `r`: the return flag; `G`: every ghost variable of the function. `none`: not
    translatable (a jump without a flag or outside its construct, ghost variables that are
    not fresh, a source statement that names a ghost variable, a loop left by a jump
    without a test of its own, `fall`). -/
def tr (r n : Nat) (G : List Nat) : List Frame → JStmt → MStmt → Option MStmt
  | _, .basic s, k => if cleanS n G s then some (.seq s k) else none
  | ctx, .seq a b, k => do
      let kb ← tr r n G ctx b k
      tr r n G ctx a kb
  | ctx, .ite w c a b, k =>
      if !cleanC G c then none
      else if (JStmt.ite w c a b).ends then do
        let ta ← tr r n G ctx a k
        let tb ← tr r n G ctx b k
        pure (.ite w c ta tb)
      else do
        let ta ← tr r n G ctx a .skip
        let tb ← tr r n G ctx b .skip
        pure (.seq (.ite w c ta tb) k)
  | ctx, .brk w, _ => match ctx with
      | fr :: _ => if fr.isSw then some (.cost w) else fr.fb.map (fun f => flagSet w f 1)
      | [] => none
  | ctx, .cont w, _ => (nearestCnt ctx).map (fun f => flagSet w f 1)
  | ctx, .ret s, _ =>
      if !cleanS n G s then none
      else match ctx with
        | [] => some s
        | _ => some (.seq s (flagSet 0 r 1))
  | ctx, .loop w cs body inc fb fc, k =>
      let b := body.escB
      let c := body.escC
      let rets := body.hasRet
      let fb' := if b then fb else none
      let fc' := if c then fc else none
      if (b && fb'.isNone) || (c && fc'.isNone) then none
      else if !freshGh r ctx (fb'.toList ++ fc'.toList) then none
      else if !(cs.all (cleanC G)) || !(match inc with | some u => cleanS n G u | none => true) then none
      else
        let exits := fb'.toList ++ (if rets then [r] else [])
        if !exits.isEmpty && cs.isEmpty then none
        else do
          let bd ← tr r n G (⟨false, fb', fc', rets, fb'.toList ++ fc'.toList⟩ :: ctx) body .skip
          pure (.seq (seqs (exits.map (fun f => flagSet 0 f 0)))
            (.seq (whileOf w cs exits fc' bd inc)
              (guardTail (if rets then some r else none) none k)))
  | ctx, .switch w sc gs, k =>
      let rets := JStmt.hasRetL gs
      let ec := JStmt.escCL gs
      if !freshGh r ctx [sc] then none
      else if ec && (nearestCnt ctx).isNone then none
      else do
        let groups ← trL r n G (⟨true, none, none, rets, [sc]⟩ :: ctx) gs
        pure (.seq (if rets then flagSet 0 r 0 else .skip)
          (.seq (.seq (.cost w) (chainOf sc groups))
            (guardTail (if rets then some r else none) (if ec then nearestCnt ctx else none) k)))
  | _, .fall _, _ => none
  | ctx, .doLoop w cs body _ _, k =>
      -- `body; while (cs) body`, for a body without `break` or `continue` of its own
      -- (the translation of a `loop` node with these values, written out so that the
      -- recursion is on `body`)
      if body.escB || body.escC then none
      else if !(cs.all (cleanC G)) then none
      else
        let rets := body.hasRet
        let exits := if rets then [r] else []
        if !exits.isEmpty && cs.isEmpty then none
        else do
          let bd ← tr r n G (⟨false, none, none, rets, []⟩ :: ctx) body .skip
          tr r n G ctx body (.seq (seqs (exits.map (fun f => flagSet 0 f 0)))
            (.seq (whileOf w cs exits none bd none)
              (guardTail (if rets then some r else none) none k)))
/-- Each case group, translated with an empty continuation. -/
def trL (r n : Nat) (G : List Nat) (ctx : List Frame) : List JStmt → Option (List MStmt)
  | [] => some []
  | g :: gs => do
      let g' ← tr r n G ctx g .skip
      let gs' ← trL r n G ctx gs
      pure (g' :: gs')
end

mutual
/-- The ghost variables of `j`. -/
def JStmt.ghosts : JStmt → List Nat
  | .basic _ => []
  | .seq a b => a.ghosts ++ b.ghosts
  | .ite _ _ a b => a.ghosts ++ b.ghosts
  | .loop _ _ body _ fb fc => fb.toList ++ fc.toList ++ body.ghosts
  | .brk _ => []
  | .cont _ => []
  | .ret _ => []
  | .switch _ sc gs => sc :: JStmt.ghostsL gs
  | .fall gs => JStmt.ghostsL gs
  | .doLoop _ _ body fb fc => fb.toList ++ fc.toList ++ body.ghosts
def JStmt.ghostsL : List JStmt → List Nat
  | [] => []
  | g :: gs => g.ghosts ++ JStmt.ghostsL gs
end

/-- The ghost variables of a function whose return flag is `r`. -/
def ghostSet (r : Nat) (j : JStmt) : List Nat := r :: j.ghosts

/-- The function body `j`, jumps eliminated; it may call the functions numbered below
    `n`. -/
def elim (r n : Nat) (j : JStmt) : Option MStmt := tr r n (ghostSet r j) [] j .skip

/-- The program of the certificate `c` of the function numbered `n` is the lowering of `j`
    once its jumps are eliminated; the return flag is `r`. -/
def validateJ (n : Nat) (c : ACmd) (r : Nat) (j : JStmt) : Bool :=
  !(ghostSet r j).contains choiceVar && !(ghostSet r j).contains costVar &&
  match elim r n j with
  | some s => validate c s
  | none => false

/-! ### Programs that do not touch the ghost variables -/

/-- The coefficients of `l` on the variables `G` are zero. -/
def zeroOn (G : List Nat) (l : List Int) : Bool := G.all (fun i => coeff l i == 0)

/-- The program `c` reads no variable of `G` (its expressions and tests have zero
    coefficients there), writes no variable of `W` and calls only functions numbered
    below `n`. Used for the functions that a validated function can call (those numbered
    below it): they must not touch its ghost variables. -/
def quietCmd (n : Nat) (G W : List Nat) : ACmd → Bool
  | .skip => true
  | .assign _ x a => !W.contains x && zeroOn G a.sv
  | .havoc _ x => !W.contains x
  | .havocC _ x cs => !W.contains x && cs.all (fun g => zeroOn G g.sv)
  | .seq a _ _ _ b => quietCmd n G W a && quietCmd n G W b
  | .ite _ g _ _ a b => zeroOn G g.sv && quietCmd n G W a && quietCmd n G W b
  | .while _ g _ _ _ _ _ _ _ _ b => zeroOn G g.sv && quietCmd n G W b
  | .whileAnd _ gs _ _ _ _ _ _ _ _ b => gs.all (fun g => zeroOn G g.sv) && quietCmd n G W b
  | .whileLog _ gs _ _ _ _ _ _ _ b => gs.all (fun g => zeroOn G g.sv) && quietCmd n G W b
  | .whileGrow _ gs _ _ _ _ _ _ _ b => gs.all (fun g => zeroOn G g.sv) && quietCmd n G W b
  | .weaken _ _ _ _ _ c => quietCmd n G W c
  | .dead _ c => quietCmd n G W c
  | .call _ f _ _ _ _ => decide (f < n)

end ImperativeOptimization.MiniC
