/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # The `upgrade` tactic

`upgrade s`, with `s : SynthHaltReduction q` a synthetic halting reduction, closes a hard goal about
`q` (`HaltReduction q`, `HaltHard q`, `¬ ComputablePred q`, `¬ MachineDecidable enc q`). It is the
"synthetic first, computable later" workflow: a problem is first reduced synthetically, and the
proved result is read off its synthetic one.

A synthetic chain starts from `HaltProblem`, which is not `Primcodable`, so its first link cannot be
proved computable. The tactic therefore *cuts* the chain at the last problem that already has a
proved halting reduction, and upgrades only the synthetic links after it.

It reads the value of `s` as a tree, from the last link back:

* at each level, with target problem `p`, it looks for a proved halting reduction to `p`: by the
  naming convention (`Ns.synthFoo a…` ↦ `Ns.foo a…`, same explicit arguments), then a hypothesis
  `HaltReduction p`, then a `HaltSource p` instance; the first found is the cut;
* otherwise it splits `SynthHaltReduction.comp h r` (or `SynthReduction.trans h r`) and looks in
  `h`, takes the argument of `HaltReduction.toSynthHalt` as the proved root, or unfolds the head
  definition one step.

After the cut, each synthetic link becomes a proved one: `⟨f, spec⟩` becomes `⟨f, ?_, spec⟩` with
the goal `Computable f`; `ComputableReduction.toSynth c` becomes `c`; any other link `r` becomes
`ComputableReduction.ofSynth r ?_` with the goal `Computable r.f`. The goals are tagged as in the
chains of `hard_reduce_from`: `computable_f` for a link function named `f` (`computable_i`, the
position after the cut from 1, otherwise; `computable` for one link). Each is tried with
`assumption` and `fun_prop` (after reducing `r.f` to the named function); what they do not close
stays open, in chain order.

Errors: no problem of the chain has a proved halting reduction (the message names the problems of
the chain, from the first); or a link after the cut is between types with no `Primcodable` instance
(as grammars of Mathlib), so it cannot be proved computable.

## Main declarations

* `Upgrade.cut`: the proved root and the synthetic links after it.
* the tactic `upgrade s`.
-/

namespace DiagonaLean.Foundations.Computability.Upgrade

open Lean Meta Elab Tactic DiagonaLean.Foundations.Computability.ReduceFrom
open DiagonaLean.Synthetic.Definitions (SynthReduction SynthHaltReduction)

/-- The two problems of a reduction type `p ⪯_s q` or `p ⪯ q` (after unfolding abbreviations). -/
def problemsOf (ty : Expr) : MetaM (Option (Expr × Expr)) := endsOf? ty

/-- The target problem of the synthetic reduction `e`. -/
def targetOf (e : Expr) : MetaM (Option Expr) := do
  return (← problemsOf (← inferType e)).map (·.2)

/-- The name of the proved counterpart of a synthetic declaration, by the naming convention:
`Ns.synthFoo` ↦ `Ns.foo`. -/
def provedName? : Name → Option Name
  | .str pre s =>
    if s.startsWith "synth" && s.length > 5 then
      let rest := (s.drop 5).toString
      some (.str pre (rest.decapitalize))
    else none
  | _ => none

/-- The explicit arguments of the application `e` of a constant. -/
def explicitArgs (e : Expr) : MetaM (Array Expr) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let mut out := #[]
  let mut ty ← inferType fn
  for a in args do
    let ty' ← whnf ty
    let .forallE _ _ b bi := ty' | return out
    if bi.isExplicit then out := out.push a
    ty := b.instantiate1 a
  return out

/-- A proved halting reduction to the problem `p`, if one is found: `Ns.foo a…` for `e = Ns.synthFoo
a…`, a hypothesis, or a `HaltSource p` instance. -/
def provedFor? (e p : Expr) : MetaM (Option Expr) := do
  let some expected ← observing? (mkAppM ``HaltReduction #[p]) | return none
  -- by name
  if let .const n _ := e.getAppFn then
    if let some n' := provedName? n then
      if (← getEnv).contains n' then
        let r ← observing? do
          let c ← mkAppM n' (← explicitArgs e)
          unless ← withNewMCtxDepth (isDefEq (← inferType c) expected) do failure
          instantiateMVars c
        if let some c := r then
          if !c.hasExprMVar then return some c
  -- a hypothesis
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← withNewMCtxDepth (isDefEq d.type expected) then return some d.toExpr
  -- a registered source
  let some cls ← observing? (mkAppM ``HaltSource #[p]) | return none
  let some inst ← synthInstance? cls | return none
  observing? (mkAppOptM ``HaltSource.red #[none, none, some p, some inst])

/-- The result of `cut`: a proved halting reduction and the synthetic links after it, in order; or,
when none is found, the problems of the chain from the first. -/
abbrev CutResult := Except (List Expr) (Expr × List Expr)

/-- Cut the synthetic halting reduction `e` at the last problem with a proved halting reduction. -/
partial def cut (e : Expr) (fuel : Nat := 32) : MetaM CutResult := do
  let e := (← instantiateMVars e).headBeta.cleanupAnnotations
  let some p ← targetOf e | return .error []
  if let some c ← provedFor? e p then return .ok (c, [])
  let split? : Option (Expr × Expr) :=
    if e.isAppOfArity ``SynthHaltReduction.comp 6 then some (e.getArg! 4, e.getArg! 5)
    else if e.isAppOfArity ``SynthReduction.trans 8 then some (e.getArg! 6, e.getArg! 7)
    else none
  if let some (h, r) := split? then
    return match ← cut h fuel with
      | .ok (c, ls) => .ok (c, ls ++ [r])
      | .error ps => .error (ps ++ [p])
  if e.isAppOfArity ``HaltReduction.toSynthHalt 4 then return .ok (e.getArg! 3, [])
  if fuel > 0 then
    if let some e' ← unfoldDefinition? e then
      match ← cut e' (fuel - 1) with
      | .ok r => return .ok r
      | .error ps => if ps.length > 1 then return .error ps
  return .error [p]

/-- The tag of the computability goal of the `i`-th link (from 1) of `links`, as `computableTag`. -/
def linkTag (names : List (Option Name)) (i : Nat) : Name :=
  if names.length ≤ 1 then `computable else
  match names[i - 1]? with
  | some (some n) =>
    if (names.filter (· == some n)).length == 1 then
      .mkSimple s!"computable_{n.components.getLast?.getD n}"
    else .mkSimple s!"computable_{i}"
  | _ => .mkSimple s!"computable_{i}"

/-- The function of a link `⟨f, spec⟩`, if `f` is a constant: its name. -/
def linkName? (r : Expr) : Option Name :=
  let r := r.cleanupAnnotations
  if r.isAppOfArity ``SynthReduction.mk 6 then (r.getArg! 4).getAppFn.constName? else none

/-- The proved link for the synthetic link `r`, and the computability goal it leaves, if any. -/
def upgradeLink (r : Expr) (tag : Name) : MetaM (Expr × Option MVarId) := do
  let r := (← instantiateMVars r).cleanupAnnotations
  let fail {α} (e : Exception) : MetaM α := do
    let ends : MessageData := match ← problemsOf (← inferType r) with
      | some (p, q) => m!" from{indentExpr p}\nto{indentExpr q}\n"
      | none => m!" "
    throwError "upgrade: the synthetic link{ends}cannot be made proved: its types need a \
      `Primcodable` instance for `Computable` to be stated.\n{e.toMessageData}"
  if r.isAppOfArity ``ComputableReduction.toSynth 7 then return (r.getArg! 6, none)
  if r.isAppOfArity ``SynthReduction.mk 6 then
    let f := r.getArg! 4
    try
      let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Computable #[f]) tag
      return (← mkAppM ``ComputableReduction.mk #[f, g, r.getArg! 5], some g.mvarId!)
    catch e => fail e
  try
    let f ← mkAppM ``SynthReduction.f #[r]
    let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Computable #[f]) tag
    return (← mkAppM ``ComputableReduction.ofSynth #[r, g], some g.mvarId!)
  catch e => fail e

/-- `upgrade s` on a hard goal: see the module docstring. -/
def run (s : Term) : TacticM Unit := withMainContext do
  let some goal ← goalOf? (← getMainTarget) | throwError "upgrade: the goal{indentExpr
      (← getMainTarget)}\nis not one of `HaltReduction q`, `HaltHard q`, `¬ ComputablePred q`, \
      `¬ MachineDecidable enc q`"
  if let .synth := goal then
    throwError "upgrade: the goal{indentExpr (← getMainTarget)}\nis synthetic; `upgrade` proves \
      the proved goals from a synthetic reduction."
  let e ← Term.withSynthesize <| withoutRecover <| elabTerm s none
  let e ← instantiateMVars e
  match ← layerOf? (← inferType e) with
  | some .synth => pure ()
  | _ => throwError "upgrade: `{s}` is not a synthetic halting reduction; its type is{indentExpr
      (← inferType e)}"
  let (root, links) ← match ← cut e with
    | .ok r => pure r
    | .error ps =>
      let chain := MessageData.joinSep (ps.map fun p => m!"{p}") " ⪯_s "
      throwError "upgrade: no problem of the chain of `{s}` has a proved halting reduction. The \
        chain:{indentD m!"HaltProblem ⪯_s {chain}"}\nLooked for, at each problem `p`: the proved \
        counterpart by name (`foo` for `synthFoo`), a hypothesis `HaltReduction p`, and an \
        instance `HaltSource p`. Give one of these for some problem of the chain."
  let names := links.map linkName?
  let mut core := root
  let mut gs : List MVarId := []
  for r in links, i in [1:links.length + 1] do
    let (l, g?) ← upgradeLink r (linkTag names i)
    core ← mkAppM ``HaltReduction.trans #[core, l]
    if let some g := g? then gs := gs ++ [g]
  let coreStx ← Term.exprToSyntax core
  let term : Term ← match goal with
    | .proved => pure coreStx
    | .hard => `(⟨$coreStx⟩)
    | .notComputable =>
      `(DiagonaLean.Foundations.Computability.HaltHard.not_computablePred ⟨$coreStx⟩)
    | _ => `(DiagonaLean.Foundations.Computability.HaltHard.not_machineDecidable ⟨$coreStx⟩ ?_)
  let others := (← getGoals).drop 1
  let before := (← getGoals).length
  try withoutRecover <| evalTactic (← `(tactic| refine $term))
  catch ex => throwError "upgrade: `{s}` does not reduce to the problem of the goal.\n\
    {ex.toMessageData}"
  let new := (← getGoals).take ((← getGoals).length - (before - 1))
  let open_ ← tryOn (gs ++ new) do
    try evalTactic (← `(tactic| first | assumption | fun_prop))
    catch _ =>
      unfoldFunction
      evalTactic (← `(tactic| fun_prop))
  setGoals (open_ ++ others)

end DiagonaLean.Foundations.Computability.Upgrade

/-- `upgrade s`: from a synthetic halting reduction `s : SynthHaltReduction q`, prove
`HaltReduction q`, `HaltHard q`, `¬ ComputablePred q` or `¬ MachineDecidable enc q`. The chain of
`s` is cut at the last problem with a proved halting reduction (`foo` for `synthFoo`, a hypothesis,
or `HaltSource`), and the synthetic links after it are upgraded, one goal `Computable f` per link
(tried with `fun_prop`). See `Foundations.Computability.Upgrade`. -/
elab "upgrade " s:term:max : tactic => DiagonaLean.Foundations.Computability.Upgrade.run s
