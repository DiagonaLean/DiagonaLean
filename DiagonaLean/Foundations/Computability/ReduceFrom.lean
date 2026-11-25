/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.HaltCanon
import DiagonaLean.Synthetic.ReductionCheck

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
applies: a link such as `PCP.synthAlphabetLift`, built from `liftInstance`, is upgraded with no
goal left. A link
function that is an `abbrev` is unfolded by `fun_prop` itself, so it should be a `def` with a lemma.

`h` is a term, possibly applied, so a source needs no registration. Reductions are recognised by
their type after unfolding abbreviations: `SynthReduction` (with `SynthHaltReduction` and the
former names `Undecidable`, `ManyOneReduces`) and `ComputableReduction` (with `HaltReduction`).

## The link as a function and a proof: `synth_reduce_from`

On a goal `SynthHaltReduction q`, the link may be given as its two parts, as the original
`reduceFromPCP` did. The tactic is `synth_reduce_from`, the synthetic one; `reduce_from … via`
stays the one for every goal.

* `synth_reduce_from h with f`: leaves `forward` (`x`, `hp : p x ⊢ q (f x)`) and `backward`
  (`x`, `hq : q (f x) ⊢ p x`).
* `synth_reduce_from h with f unfold`: the same, with both problems unfolded one step (`hp`
  becomes the existential of PCP, say); kept folded, with a message, when the unfolding is
  recursive or very large.
* `synth_reduce_from h with f using spec`: the link is `⟨f, spec⟩`, with `spec : p ⪯_s[f] q`.
* `synth_reduce_from h with f using fwd bwd`: the two directions as the lemmas of the reduction
  files, `fwd : p x → q (f x)` and `bwd : q (f x) → p x`.
* `synth_reduce_from h via r`: `reduce_from h via r`, for a synthetic goal only.

The function is checked at tactic time, for the message: it may not use a `noncomputable`
definition, `implemented_by`, `extern`, `opaque`, `partial`, `unsafe` or classical choice, one level
deep; `#check_reductions` and the compiler check the rest. Proved goals take `reduce_from … via`.

## Hard goals: `hard_reduce_from`

On a hard goal (`HaltReduction q`, `HaltHard q`, `¬ ComputablePred q`, `¬ MachineDecidable enc q`)
the same forms build a proved link `⟨f, computable, proof⟩`: `hard_reduce_from h with f`,
`with f unfold`, `with f using spec`, `with f using fwd bwd`. `Computable f` is its own goal, on
the function named, tried with `assumption` and `fun_prop` (no unfolding of a bundled link) and
left open if they fail; `with f` leaves `forward`, `backward`, then what is open.

The source `h` is a proved halting reduction, the fact `HaltHard p` (unpacked, so not for the data
goal `HaltReduction q`), a negative result `¬ ComputablePred p` (for the two negative goals), or a
problem with a `HaltSource` instance (data) or a `HaltHardFact` instance (a proposition); a
synthetic halting reduction is an error. `reduce_from h with …` picks `synth_reduce_from` or
`hard_reduce_from` by the goal. After a `using` clause, a lemma on the next line is not read as a
second lemma (`colGt`).

## A problem as the source

A source that is a problem `X → Prop` rather than a reduction is looked up by the naming
convention: in the namespace of the problem's head constant, `synthFromHalt` and
`synthFromHaltBool` (without explicit arguments) whose target unifies with the problem. No match, or
several, is an error that says so.
-/

namespace DiagonaLean.Foundations.Computability

/-- A registered proof that `P` is halting-hard, as data: `hard_reduce_from` finds it when the
source is the problem `P` itself. An instance holds a `HaltReduction`, so it is in the proved
layer, which `#check_reductions` does not check. -/
class HaltSource {β : Type*} [Primcodable β] (P : β → Prop) where
  /-- The proved reduction from halting. -/
  red : HaltReduction P

/-- A registered fact that `P` is halting-hard, for a problem with no `HaltReduction` as data. -/
class HaltHardFact {β : Type*} [Primcodable β] (P : β → Prop) : Prop where
  /-- The fact. -/
  hard : HaltHard P

instance (priority := low) {β : Type*} [Primcodable β] (P : β → Prop) [HaltSource P] :
    HaltHardFact P := ⟨⟨HaltSource.red⟩⟩

end DiagonaLean.Foundations.Computability

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

open DiagonaLean.Synthetic.ReductionCheck (isTrusted escapeHatch)

/-- A problem: a predicate `X → Prop`. -/
def isProblemType (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun xs body => return !xs.isEmpty && (← whnf body).isProp

/-- The names, in the namespace of a problem, of the synthetic halting reductions to it that
`reduce_from` looks for. -/
def sourceSuffixes : List Name := [`synthFromHalt, `synthFromHaltBool]

/-- A type with an explicit binder, so a definition that must be applied to arguments. -/
def hasExplicitBinder : Expr → Bool
  | .forallE _ _ b bi => bi.isExplicit || hasExplicitBinder b
  | _ => false

/-- What was found for the problem `p`. -/
structure Lookup where
  /-- The namespace searched: the prefix of the problem's head constant. -/
  ns : Name
  /-- The sources whose target is the problem. -/
  matched : Array Name := #[]
  /-- The sources that exist but reduce halting to another problem. -/
  elsewhere : Array Name := #[]
  /-- The sources that exist but take explicit arguments, so cannot be found by name. -/
  needsArgs : Array Name := #[]

/-- The synthetic halting reductions in the namespace of `p`'s head constant (by the naming
convention) whose target unifies with `p` and that take no explicit arguments. -/
def lookupSynthSource (p : Expr) : MetaM Lookup := do
  let p ← instantiateMVars p
  let some c := p.getAppFn.constName? | throwError "reduce_from: the problem{indentExpr p}\n\
    has no head constant, so no source can be looked up from its name"
  let mut lk : Lookup := { ns := c.getPrefix }
  let env ← getEnv
  for suf in sourceSuffixes do
    let n := lk.ns ++ suf
    unless env.contains n do continue
    let ci ← getConstInfo n
    if hasExplicitBinder ci.type then
      lk := { lk with needsArgs := lk.needsArgs.push n }
      continue
    let ok ← withoutModifyingState do
      let e ← mkConstWithFreshMVarLevels n
      let (_, _, concl) ← forallMetaTelescopeReducing (← inferType e)
      match ← endsOf? concl with
      | some (_, q) => isDefEq q p
      | none => pure false
    if ok then lk := { lk with matched := lk.matched.push n }
    else lk := { lk with elsewhere := lk.elsewhere.push n }
  return lk

/-- If `h` is a problem rather than a reduction, the registered source for it (by name); otherwise
`h` itself. -/
def resolveSource (h : Term) : TacticM Term := do
  let r ← withoutModifyingState do
    let e ← withoutRecover <| elabTerm h none (mayPostpone := true)
    unless ← isProblemType (← inferType e) do return none
    return some (← lookupSynthSource e)
  let some lk := r | return h
  match lk.matched with
  | #[n] => return ⟨(mkIdent n).raw⟩
  | #[] =>
    let names (a : Array Name) : MessageData := MessageData.joinSep (a.toList.map (m!"`{·}`")) ", "
    let mut msg := m!"reduce_from: `{h}` is a problem, not a reduction, so the tactic looks for a \
      synthetic halting reduction to it in the namespace `{lk.ns}`, by the names `synthFromHalt` \
      and `synthFromHaltBool`, and finds none that applies. Give the source explicitly."
    unless lk.elsewhere.isEmpty do
      msg := msg ++ m!"\nThese exist but reduce halting to another problem: {names lk.elsewhere}."
    unless lk.needsArgs.isEmpty do
      msg := msg ++ m!"\nThese take explicit arguments, so give them as the source: \
        {names lk.needsArgs}."
    throwError msg
  | ns => throwError "reduce_from: several halting reductions to `{h}` apply: {
      MessageData.joinSep (ns.toList.map (m!"`{·}`")) ", "}. Fix the alphabet or give the source \
      explicitly."

/-- The link function of a synthetic result must be a program: a constant that is not
`noncomputable`, and without an escape hatch (`implemented_by`, `extern`, `opaque`, `partial`,
`unsafe`), or classical choice. One level only: `#check_reductions` and the compiler check the
rest, so this check is for the message. -/
def checkLinkFunction (f : Term) : TacticM Unit := do
  let some e ← (do
      try withoutModifyingState do
        return some (← instantiateMVars (← withoutRecover <| elabTerm f none (mayPostpone := true)))
      catch _ => return none) | return
  let env ← getEnv
  for c in e.getUsedConstants do
    let classical := (`Classical).isPrefixOf c && !(env.find? c matches some (.thmInfo _))
    if isTrusted env c && !classical then continue
    let why? : Option String :=
      if classical then some "has no compiled code (classical choice)"
      else if isNoncomputable env c then some "is marked `noncomputable`"
      else escapeHatch env c
    if let some why := why? then
      let who : MessageData :=
        if f.raw.isIdent && f.raw.getId == c then m!"the link function `{c}` {why}"
        else m!"the link function uses `{c}`, which {why}"
      throwError "synth_reduce_from: {who}. The function of a synthetic reduction must be a \
        compiled program. For a proved result, use a proved link, or prove `Computable` of the \
        function."

/-- How the correctness of the link function is given: left as the goals `forward` and `backward`
(`open_`), the same with both problems unfolded (`unfold`), as a whole statement (`spec`), or as
the two directions (`lemmas`). -/
inductive LinkProof
  | open_ | unfold | spec (s : Term) | lemmas (a b : Term)

/-- One unfolding of the head definition of a problem applied to an instance, beta first; a problem
that is an alias (`abbrev`) is unfolded through to its definition. Kept folded (with a message)
when the unfolding is recursive (a matcher, `brecOn`, well-founded recursion) or very large. -/
partial def unfoldProblem? (e : Expr) (fuel : Nat := 4) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).headBeta
  let fn := e.getAppFn
  let some e' ← unfoldDefinition? e | return none
  let env ← getEnv
  let recursive := e'.getUsedConstants.any fun c =>
    isMatcherCore env c || c == ``WellFounded.fix ||
      (match c with | .str _ n => n == "brecOn" | _ => false)
  if recursive || e'.sizeWithoutSharing > 6000 then
    logInfo m!"synth_reduce_from … unfold: `{e}` unfolds into a recursive or very large term, so \
      it is kept folded"
    return none
  if fn.isConst && fuel > 0 && (← isReducible fn.constName!) then
    return (← unfoldProblem? e' (fuel - 1)).getD e' |> some
  return some e'

/-- Unfold the hypothesis `hyp` and the target of the goal `g`, each by one step. -/
def unfoldSplitGoal (g : MVarId) (hyp : Name) : MetaM MVarId := g.withContext do
  let mut g := g
  if let some d := (← getLCtx).findFromUserName? hyp then
    if let some t ← unfoldProblem? d.type then g ← g.changeLocalDecl d.fvarId t
  if let some t ← unfoldProblem? (← g.getType) then g ← g.change t
  return g

/-- `synth_reduce_from h with f …` on a goal `SynthHaltReduction q`: the link is `⟨f, proof⟩`. -/
def runWith (h f : Term) (how : LinkProof) : TacticM Unit := withMainContext do
  match ← goalOf? (← getMainTarget) with
  | some .synth => pure ()
  | _ => throwError "synth_reduce_from: the goal{indentExpr (← getMainTarget)}\nis not \
      `SynthHaltReduction q`. For a proved goal, use `reduce_from … via`."
  let h ← resolveSource h
  checkLinkFunction f
  let link : Term ← match how with
    | .open_ | .unfold => `(⟨$f, ?spec⟩)
    | .spec s => `(⟨$f, $s⟩)
    | .lemmas a b => `(⟨$f, fun _ => ⟨$a, $b⟩⟩)
  let term ← `(DiagonaLean.Synthetic.Definitions.SynthHaltReduction.comp $h $link)
  try withoutRecover <| evalTactic (← `(tactic| refine $term))
  catch e =>
    match how with
    | .lemmas a b => throwError "synth_reduce_from: the lemmas `{a}` and `{b}` do not prove that \
        `{f}` reduces the source `{h}` to the goal. They must state `p x → q ({f} x)` and the \
        converse, in this order; or give the whole statement with `using`.\n{e.toMessageData}"
    | .spec s => throwError "synth_reduce_from: `{s}` does not prove that `{f}` reduces the \
        source `{h}` to the goal.\n{e.toMessageData}"
    | _ => throw e
  match how with
  | .open_ | .unfold =>
    evalTactic (← `(tactic| intro $(mkIdent `x):ident))
    evalTactic (← `(tactic| refine ⟨fun $(mkIdent `hp):ident => ?forward,
      fun $(mkIdent `hq):ident => ?backward⟩))
    if let .unfold := how then
      match ← getGoals with
      | gf :: gb :: rest =>
        setGoals ((← unfoldSplitGoal gf `hp) :: (← unfoldSplitGoal gb `hq) :: rest)
      | _ => pure ()
  | _ => pure ()

/-- The kinds of source of a hard goal. -/
inductive HardSource | red | hard | neg

/-- The kind of the source `stx` of a hard goal: a proved halting reduction, the fact `HaltHard p`,
or a negative result `¬ ComputablePred p`. A synthetic halting reduction is an error. -/
def hardSourceOf (stx : Term) : TacticM HardSource := withoutModifyingState do
  let e ← withoutRecover <| elabTerm stx none (mayPostpone := true)
  let ty ← instantiateMVars (← inferType e)
  if ty.isAppOfArity ``Not 1 then
    if (← whnfR ty.appArg!).isAppOf ``ComputablePred then return .neg
  let ty' ← whnfR ty
  if ty'.isAppOfArity ``Nonempty 1 then
    if (← whnfR ty'.appArg!).isAppOf ``ComputableReduction then return .hard
  match ← layerOf? ty with
  | some .proved => return .red
  | some .synth => throwError "hard_reduce_from: the source `{stx}` is a synthetic halting \
      reduction, but a hard goal needs a proved one. A halting reduction is upgraded at its root, \
      from `HaltCanon`, not by a computability proof of the link."
  | none => throwError "hard_reduce_from: the source `{stx}` is not a proved halting reduction, \
      `HaltHard p`, `¬ ComputablePred p` or a registered problem; its type is{indentExpr ty}"

/-- If the source is a problem, the registered proof that it is halting-hard (`HaltSource`, then
`HaltHardFact`); otherwise the source itself. -/
def resolveHardSource (h : Term) : TacticM Term := do
  let isProblem ← withoutModifyingState do
    let e ← withoutRecover <| elabTerm h none (mayPostpone := true)
    isProblemType (← inferType e)
  unless isProblem do return h
  let cands : List Term := [
    ← `(DiagonaLean.Foundations.Computability.HaltSource.red (P := $h)),
    ← `(DiagonaLean.Foundations.Computability.HaltHardFact.hard (P := $h))]
  for stx in cands do
    let ok ← try
        withoutModifyingState do
          discard <| Term.withSynthesize <| withoutRecover <| elabTerm stx none
        pure true
      catch _ => pure false
    if ok then return stx
  throwError "hard_reduce_from: `{h}` is a problem, so the tactic looks for an instance of \
    `HaltSource` or `HaltHardFact` for it, and finds none. Register one, or give the source \
    explicitly."

/-- `hard_reduce_from h with f …` on a hard goal (`HaltReduction q`, `HaltHard q`,
`¬ ComputablePred q`, `¬ MachineDecidable enc q`): the link is `⟨f, computable, proof⟩`. The goal
`computable : Computable f` is tried with `assumption` and `fun_prop`; what they do not close
stays open. -/
def runHard (h f : Term) (how : LinkProof) : TacticM Unit := withMainContext do
  let some goal ← goalOf? (← getMainTarget) | throwError "hard_reduce_from: the goal{indentExpr
      (← getMainTarget)}\nis not one of `HaltReduction q`, `HaltHard q`, `¬ ComputablePred q`, \
      `¬ MachineDecidable enc q`"
  if let .synth := goal then
    throwError "hard_reduce_from: the goal{indentExpr (← getMainTarget)}\nis synthetic; use \
      `synth_reduce_from`."
  let h ← resolveHardSource h
  let kind ← hardSourceOf h
  let link : Term ← match how with
    | .open_ | .unfold => `(⟨$f, ?computable, ?spec⟩)
    | .spec s => `(⟨$f, ?computable, $s⟩)
    | .lemmas a b => `(⟨$f, ?computable, fun _ => ⟨$a, $b⟩⟩)
  let term : Term ← match kind with
  | .neg =>
    let neg ← `(DiagonaLean.Foundations.Computability.ComputableReduction.not_computablePred
      $link $h)
    match goal with
    | .notComputable => pure neg
    | .notMachine =>
      `(DiagonaLean.Foundations.Computability.not_machineDecidable_of_not_computablePred ?_ $neg)
    | _ => throwError "hard_reduce_from: the source `{h}` is a negative result \
        (`¬ ComputablePred`), so it proves only a goal `¬ ComputablePred q` or \
        `¬ MachineDecidable enc q`."
  | .red | .hard =>
    let mk (src : Term) : TacticM Term := do
      let core ← `(DiagonaLean.Foundations.Computability.HaltReduction.trans $src $link)
      match goal with
      | .proved => pure core
      | .hard => `(⟨$core⟩)
      | .notComputable =>
        `(DiagonaLean.Foundations.Computability.HaltHard.not_computablePred ⟨$core⟩)
      | _ => `(DiagonaLean.Foundations.Computability.HaltHard.not_machineDecidable ⟨$core⟩ ?_)
    match kind, goal with
    | .hard, .proved => throwError "hard_reduce_from: the source `{h}` is a proposition \
        (`HaltHard`), but the goal `HaltReduction q` is data. Use a source that is a \
        `HaltReduction`."
    | .hard, _ =>
      let hr := mkIdent `hr
      `(Nonempty.elim $h fun $hr => $(← mk hr))
    | _, _ => mk h
  let others := (← getGoals).drop 1
  let before := (← getGoals).length
  try withoutRecover <| evalTactic (← `(tactic| refine $term))
  catch e =>
    match how with
    | .lemmas a b => throwError "hard_reduce_from: the lemmas `{a}` and `{b}` do not prove that \
        `{f}` reduces the source `{h}` to the goal. They must state `p x → q ({f} x)` and the \
        converse, in this order; or give the whole statement with `using`.\n{e.toMessageData}"
    | .spec s => throwError "hard_reduce_from: `{s}` does not prove that `{f}` reduces the \
        source `{h}` to the goal.\n{e.toMessageData}"
    | _ => throw e
  let new := (← getGoals).take ((← getGoals).length - (before - 1))
  let mut specG : Option MVarId := none
  let mut side : List MVarId := []
  for g in new do
    if (← g.getTag).eraseMacroScopes == `spec then specG := some g
    else side := side ++ [g]
  let open_ ← tryOn side do
    try evalTactic (← `(tactic| first | assumption | fun_prop))
    catch _ =>
      unfoldFunction
      evalTactic (← `(tactic| fun_prop))
  let mut split : List MVarId := []
  if let some g := specG then
    setGoals [g]
    evalTactic (← `(tactic| intro $(mkIdent `x):ident))
    evalTactic (← `(tactic| refine ⟨fun $(mkIdent `hp):ident => ?forward,
      fun $(mkIdent `hq):ident => ?backward⟩))
    split ← getGoals
    if let .unfold := how then
      match split with
      | gf :: gb :: rest =>
        split := (← unfoldSplitGoal gf `hp) :: (← unfoldSplitGoal gb `hq) :: rest
      | _ => pure ()
  setGoals (split ++ open_ ++ others)

end DiagonaLean.Foundations.Computability.ReduceFrom

open DiagonaLean.Foundations.Computability.ReduceFrom Lean Elab Tactic in
/-- `reduce_from h via r`: close a goal about `q` from a halting reduction `h` to `p` and a link `r`
from `p` to `q`. The goal decides whether the result is synthetic or proved; see the module
docstring of `Foundations.Computability.ReduceFrom`. -/
elab "reduce_from " h:term:max " via " r:term : tactic => withMainContext do
  let h ← resolveSource h
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

open DiagonaLean.Foundations.Computability.ReduceFrom Lean Elab Tactic

/-- `synth_reduce_from h with f`: on a goal `SynthHaltReduction q`, build the link from the function
`f` and leave its correctness as the two goals `forward` (`hp : p x ⊢ q (f x)`) and `backward`
(`hq : q (f x) ⊢ p x`). `with f unfold` also unfolds both problems one step. `with f using spec`
(`spec : p ⪯_s[f] q`) or `with f using fwd bwd` closes the link with a known theorem, and
`synth_reduce_from h via r` composes with a bundled link. `h` is a halting reduction to `p`, or the
problem `p` itself, found by the naming convention. See `Foundations.Computability.ReduceFrom`. -/
syntax (name := srfWith) "synth_reduce_from " term:max " with " term:max : tactic
@[tactic_alt srfWith]
syntax (name := srfUnfold) "synth_reduce_from " term:max " with " term:max &" unfold" : tactic
@[tactic_alt srfWith]
syntax (name := srfUsing) "synth_reduce_from " term:max " with " term:max " using " term:max
  : tactic
@[tactic_alt srfWith]
syntax (name := srfLemmas) "synth_reduce_from " term:max " with " term:max " using " term:max
  colGt term:max : tactic
@[tactic_alt srfWith]
syntax (name := srfVia) "synth_reduce_from " term:max " via " term:max : tactic

elab_rules : tactic
  | `(tactic| synth_reduce_from $h with $f) => runWith h f .open_
  | `(tactic| synth_reduce_from $h with $f unfold) => runWith h f .unfold
  | `(tactic| synth_reduce_from $h with $f using $s) => runWith h f (.spec s)
  | `(tactic| synth_reduce_from $h with $f using $a $b) => runWith h f (.lemmas a b)
  | `(tactic| synth_reduce_from $h via $r) => withMainContext do
    match ← goalOf? (← getMainTarget) with
    | some .synth => evalTactic (← `(tactic| reduce_from $h via $r))
    | _ => throwError "synth_reduce_from: the goal{indentExpr (← getMainTarget)}\nis not \
        `SynthHaltReduction q`. For a proved goal, use `reduce_from … via`."

/-- `hard_reduce_from h with f`: on a hard goal (`HaltReduction q`, `HaltHard q`,
`¬ ComputablePred q`, `¬ MachineDecidable enc q`), build the link `⟨f, computable, proof⟩` from the
function `f`. `Computable f` is tried with `fun_prop` and stays open if it fails; the correctness is
left as `forward` (`hp : p x ⊢ q (f x)`) and `backward` (`hq : q (f x) ⊢ p x`). `with f unfold` also
unfolds both problems one step; `with f using spec` or `using fwd bwd` closes the link with a known
theorem. The source `h` is a proved halting reduction, `HaltHard p`, a negative result
`¬ ComputablePred p` (for the two negative goals), or a problem with a `HaltSource` or
`HaltHardFact` instance. -/
syntax (name := hrfWith) "hard_reduce_from " term:max " with " term:max : tactic
@[tactic_alt hrfWith]
syntax (name := hrfUnfold) "hard_reduce_from " term:max " with " term:max &" unfold" : tactic
@[tactic_alt hrfWith]
syntax (name := hrfUsing) "hard_reduce_from " term:max " with " term:max " using " term:max
  : tactic
@[tactic_alt hrfWith]
syntax (name := hrfLemmas) "hard_reduce_from " term:max " with " term:max " using " term:max
  colGt term:max : tactic

@[tactic_alt tacticReduce_from_Via_]
syntax (name := rfWith) "reduce_from " term:max " with " term:max : tactic
@[tactic_alt tacticReduce_from_Via_]
syntax (name := rfUnfold) "reduce_from " term:max " with " term:max &" unfold" : tactic
@[tactic_alt tacticReduce_from_Via_]
syntax (name := rfUsing) "reduce_from " term:max " with " term:max " using " term:max : tactic
@[tactic_alt tacticReduce_from_Via_]
syntax (name := rfLemmas) "reduce_from " term:max " with " term:max " using " term:max
  colGt term:max : tactic

/-- Whether the main goal is `SynthHaltReduction q`, so that `reduce_from … with` goes to
`synth_reduce_from`; every other goal goes to `hard_reduce_from`. -/
def isSynthGoal : TacticM Bool := withMainContext do
  match ← goalOf? (← getMainTarget) with
  | some .synth => return true
  | _ => return false

elab_rules : tactic
  | `(tactic| hard_reduce_from $h with $f) => runHard h f .open_
  | `(tactic| hard_reduce_from $h with $f unfold) => runHard h f .unfold
  | `(tactic| hard_reduce_from $h with $f using $s) => runHard h f (.spec s)
  | `(tactic| hard_reduce_from $h with $f using $a $b) => runHard h f (.lemmas a b)
  | `(tactic| reduce_from $h with $f) => do
    if ← isSynthGoal then evalTactic (← `(tactic| synth_reduce_from $h with $f))
    else evalTactic (← `(tactic| hard_reduce_from $h with $f))
  | `(tactic| reduce_from $h with $f unfold) => do
    if ← isSynthGoal then evalTactic (← `(tactic| synth_reduce_from $h with $f unfold))
    else evalTactic (← `(tactic| hard_reduce_from $h with $f unfold))
  | `(tactic| reduce_from $h with $f using $s) => do
    if ← isSynthGoal then evalTactic (← `(tactic| synth_reduce_from $h with $f using $s))
    else evalTactic (← `(tactic| hard_reduce_from $h with $f using $s))
  | `(tactic| reduce_from $h with $f using $a $b) => do
    if ← isSynthGoal then evalTactic (← `(tactic| synth_reduce_from $h with $f using $a $b))
    else evalTactic (← `(tactic| hard_reduce_from $h with $f using $a $b))
