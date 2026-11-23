/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.HaltCanon

@[expose] public section

/-! # The `reduce_from` tactic

`reduce_from h via r` closes a goal about a problem `q` from a halting reduction `h` to a problem
`p` and a link `r` from `p` to `q`. The goal decides the layer:

* `SynthHaltReduction q`: `h.comp r`, a proved `h` or `r` first made synthetic (`toSynthHalt`,
  `toSynth`).
* `HaltReduction q`, with `h` proved: `h.trans r`; a synthetic `r` is upgraded with `ofSynth`,
  leaving its computability.
* `HaltHard q`, with `h` proved: `⟨h.trans r⟩`, likewise.
* `¬ ComputablePred q`, with `h` proved: `HaltHard.not_computablePred ⟨h.trans r⟩`.
* `¬ MachineDecidable enc q`, with `h` proved: `HaltHard.not_machineDecidable ⟨h.trans r⟩ _`,
  leaving `Computable enc`.

The source may also be a negative result `h : ¬ ComputablePred p`. Then the goals are
`¬ ComputablePred q` (`ComputableReduction.not_computablePred`, or `not_computablePred_of_reduces`
for a synthetic link, leaving its computability) and `¬ MachineDecidable enc q` (leaving
`Computable enc`); any other goal is an error, because a negative result carries no reduction.

A proved goal with a synthetic source is an error: a halting reduction is upgraded at its root, from
canonical machines (`HaltCanon`), not by a computability proof. The goals the tactic leaves, the
computability of an upgraded link and of the encoding, are tried with `assumption` and `fun_prop`;
whatever these do not close stays open. For a link `r`, `r.f` is first reduced to the function `r`
was built from, with that function kept folded (`unfoldField`), so that its own `fun_prop` lemma
applies: the links `PCP.synthFromMPCP`, `PCP.synthAlphabetLift`, `MatMort.synthFromPCP`,
`EmpCFG.synthCodeFromPCP` and `AmbigCFG.synthCodeFromPCP` are upgraded with no goal left. A link
function that is an `abbrev` is unfolded by `fun_prop` itself, so it should be a `def` with a lemma.

`h` is a term, possibly applied, so a source needs no registration. Reductions are recognised by
their type after unfolding abbreviations: `SynthReduction` (with `SynthHaltReduction` and the
former names `Undecidable`, `ManyOneReduces`) and `ComputableReduction` (with `HaltReduction`).
-/

namespace DiagonaLean.Foundations.Computability.ReduceFrom

open Lean Meta Elab Tactic

/-- Whether a reduction is synthetic or proved. -/
inductive Layer | synth | proved
  deriving BEq

/-- The layer of a reduction, from its type. -/
def layerOf? (ty : Expr) : MetaM (Option Layer) := do
  let ty ← whnfR (← instantiateMVars ty)
  if ty.isAppOf ``DiagonaLean.Synthetic.Definitions.SynthReduction then return some .synth
  if ty.isAppOf ``ComputableReduction then return some .proved
  return none

/-- The shapes of goal `reduce_from` accepts. -/
inductive Goal | synth | proved | hard | notComputable | notMachine

/-- The shape of the goal, if `reduce_from` accepts it. -/
def goalOf? (tgt : Expr) : MetaM (Option Goal) := do
  let tgt ← instantiateMVars tgt
  if tgt.isAppOfArity ``Not 1 then
    let inner ← whnfR tgt.appArg!
    if inner.isAppOf ``ComputablePred then return some .notComputable
    if inner.isAppOf ``DiagonaLean.Synthetic.Definitions.MachineDecidable then
      return some .notMachine
    return none
  let t ← whnfR tgt
  if t.isAppOf ``DiagonaLean.Synthetic.Definitions.SynthReduction then return some .synth
  if t.isAppOf ``ComputableReduction then return some .proved
  if t.isAppOfArity ``Nonempty 1 then
    if (← whnfR t.appArg!).isAppOf ``ComputableReduction then return some .hard
  return none

/-- The layer of the term `stx`, or an error naming it. Only the head of its type matters, so the
term is elaborated with its instances postponed (a link's source alphabet may be implicit, fixed
only by the goal) and the elaboration is discarded. -/
def layerOfTerm (stx : Term) (role : String) : TacticM Layer := withoutModifyingState do
  let e ← withoutRecover <| elabTerm stx none (mayPostpone := true)
  match ← layerOf? (← inferType e) with
  | some l => return l
  | none => throwError "reduce_from: the {role} `{stx}` is not a reduction: its type is{indentExpr
      (← inferType e)}\nexpected a `SynthReduction` (`⪯_s`, `SynthHaltReduction`) or a \
      `ComputableReduction` (`HaltReduction`)"

/-- The source of `reduce_from`: a reduction of one of the two layers, or a negative result
`¬ ComputablePred p`. -/
inductive Source | red (l : Layer) | neg

/-- The source `stx`: a negative result `¬ ComputablePred p`, or a reduction (as `layerOfTerm`). -/
def sourceOfTerm (stx : Term) : TacticM Source := withoutModifyingState do
  let e ← withoutRecover <| elabTerm stx none (mayPostpone := true)
  let ty ← instantiateMVars (← inferType e)
  if ty.isAppOfArity ``Not 1 then
    if (← whnfR ty.appArg!).isAppOf ``ComputablePred then return .neg
  match ← layerOf? ty with
  | some l => return .red l
  | none => throwError "reduce_from: the source `{stx}` is neither a reduction nor a negative \
      result: its type is{indentExpr ty}\nexpected a `SynthReduction` (`⪯_s`, \
      `SynthHaltReduction`), a `ComputableReduction` (`HaltReduction`) or `¬ ComputablePred p`"

/-- The two predicates a reduction or a negative result is about: for `p ⪯ q`, the pair `(p, q)`;
for `¬ ComputablePred p`, the pair `(p, p)`. Both are the last arguments of the type. -/
def endsOf? (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty ← whnfR (← instantiateMVars ty)
  let args := ty.getAppArgs
  if ty.isAppOfArity ``Not 1 then
    let inner ← whnfR ty.appArg!
    if inner.isAppOf ``ComputablePred then
      return some (inner.appArg!, inner.appArg!)
    return none
  if (ty.isAppOf ``DiagonaLean.Synthetic.Definitions.SynthReduction ||
      ty.isAppOf ``ComputableReduction) && args.size ≥ 2 then
    return some (args[args.size - 2]!, args[args.size - 1]!)
  return none

/-- Check that the source reduces to the predicate the link starts from, and say which is which
otherwise; `refine` would report only a mismatch inside a library term. Skipped when a type cannot
be read, and when the two sides cannot be unified because of unresolved metavariables. -/
def checkChain (h r : Term) : TacticM Unit := withoutModifyingState do
  let eh ← withoutRecover <| elabTerm h none (mayPostpone := true)
  let er ← withoutRecover <| elabTerm r none (mayPostpone := true)
  let some (_, qh) ← endsOf? (← inferType eh) | return
  let some (pr, _) ← endsOf? (← inferType er) | return
  let qh ← instantiateMVars qh
  let pr ← instantiateMVars pr
  unless ← isDefEq qh pr do
    throwError "reduce_from: the source `{h}` reduces to{indentExpr qh}\nbut the link `{r}` \
      starts from{indentExpr pr}"

/-- Run `tac` on each of `gs`, keeping the goals it does not close. -/
def tryOn (gs : List MVarId) (tac : TacticM Unit) : TacticM (List MVarId) := do
  let mut left := []
  for g in gs do
    if ← g.isAssigned then continue
    let s ← saveState
    setGoals [g]
    try
      tac
      if !(← getGoals).isEmpty then
        s.restore
        left := left ++ [g]
    catch _ =>
      s.restore
      left := left ++ [g]
  return left

/-- Reduce a projection `r.f` of a reduction to the function it was built from, unfolding only the
definitions that `r` is built from, one step at a time. The function itself stays folded (a named
function such as `matImage`, not its body), so that `fun_prop` can use its lemma. -/
partial def unfoldField (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  if fuel = 0 then return e
  let e ← whnfCore e
  match e.getAppFn with
  | .const n _ =>
    -- a projection function applied to its structure: unfold it to a primitive projection
    let some info ← getProjectionFnInfo? n | return e
    if e.getAppNumArgs ≤ info.numParams then return e
    let some e' ← delta? e (· == n) | return e
    unfoldField e'.headBeta (fuel - 1)
  | .proj S i r =>
    -- a stuck primitive projection: unfold the structure by one step
    let r' ← match ← unfoldDefinition? r with
      | some r' => pure r'
      | none => unfoldField r (fuel - 1)
    if r' == r then return e
    unfoldField (mkAppN (.proj S i r') e.getAppArgs) (fuel - 1)
  | _ => return e

/-- On a goal `Computable e` or `Primrec e`, unfold `e` to its function: a link's field `r.f`
reduces to the function it was built from, which `fun_prop` can then read. -/
def unfoldFunction : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let some (f, mk) := (if tgt.isAppOf ``Computable || tgt.isAppOf ``Primrec then
      some (tgt.appArg!, fun e => mkApp tgt.appFn! e) else none)
    | throwError "not a computability goal"
  let f' ← unfoldField f
  if f' == f then throwError "nothing to unfold"
  replaceMainGoal [← g.change (mk f')]

end DiagonaLean.Foundations.Computability.ReduceFrom

open DiagonaLean.Foundations.Computability.ReduceFrom Lean Elab Tactic in
/-- `reduce_from h via r`: close a goal about `q` from a halting reduction `h` to `p` and a link `r`
from `p` to `q`. The goal decides whether the result is synthetic or proved; see the module
docstring of `Foundations.Computability.ReduceFrom`. -/
elab "reduce_from " h:term:max " via " r:term : tactic => withMainContext do
  let some goal ← goalOf? (← getMainTarget) | throwError "reduce_from: the goal{indentExpr
      (← getMainTarget)}\nis not one of `SynthHaltReduction q`, `HaltReduction q`, `HaltHard q`, \
      `¬ ComputablePred q`, `¬ MachineDecidable enc q`"
  let hs ← sourceOfTerm h
  let rl ← layerOfTerm r "link"
  checkChain h r
  let term : Term ← match hs with
  | .neg =>
    let neg : Term ← if rl == .proved then
        `(DiagonaLean.Foundations.Computability.ComputableReduction.not_computablePred $r $h)
      else `(DiagonaLean.Foundations.Computability.not_computablePred_of_reduces $r ?_ $h)
    (match goal with
    | .notComputable => pure neg
    | .notMachine =>
      `(DiagonaLean.Foundations.Computability.not_machineDecidable_of_not_computablePred ?_ $neg)
    | _ => throwError "reduce_from: the source `{h}` is a negative result (`¬ ComputablePred`), \
        so it proves only a goal `¬ ComputablePred q` or `¬ MachineDecidable enc q`; the other \
        goals need a halting reduction as the source.")
  | .red hl =>
    match goal with
      | .synth =>
        let hS ← if hl == .proved then
          `(DiagonaLean.Foundations.Computability.HaltReduction.toSynthHalt $h) else pure h
        let rS ← if rl == .proved then
          `(DiagonaLean.Foundations.Computability.ComputableReduction.toSynth $r) else pure r
        `(DiagonaLean.Synthetic.Definitions.SynthHaltReduction.comp $hS $rS)
      | _ =>
        if hl == .synth then
          throwError "reduce_from: the source `{h}` is a synthetic halting reduction, but the goal \
            needs a proved one. A halting reduction is upgraded at its root, by a reduction from \
            `HaltCanon` proved computable, not by a computability proof of the link."
        let rP ← if rl == .synth then
          `(DiagonaLean.Foundations.Computability.ComputableReduction.ofSynth $r ?_) else pure r
        let core ← `(DiagonaLean.Foundations.Computability.HaltReduction.trans $h $rP)
        match goal with
        | .proved => pure core
        | .hard => `(⟨$core⟩)
        | .notComputable =>
          `(DiagonaLean.Foundations.Computability.HaltHard.not_computablePred ⟨$core⟩)
        | _ => `(DiagonaLean.Foundations.Computability.HaltHard.not_machineDecidable ⟨$core⟩ ?_)
  let others := (← getGoals).drop 1
  let before := (← getGoals).length
  withoutRecover <| evalTactic (← `(tactic| refine $term))
  let new := (← getGoals).take ((← getGoals).length - (before - 1))
  let left ← tryOn new do
    try evalTactic (← `(tactic| first | assumption | fun_prop))
    catch _ =>
      unfoldFunction
      evalTactic (← `(tactic| fun_prop))
  setGoals (left ++ others)
