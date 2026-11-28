/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Aalok Thakkar, Claude Opus
-/

import Lean.Meta.Tactic.TryThis
import DiagonaLean.Synthetic.HaltReduction
import DiagonaLean.Synthetic.Tactics.ReductionPath

@[expose] public section

/-! # Finding synthetic halting reductions

`undec from P` proves `SynthHaltReduction Q` by a route from halting to `P` and a route from `P`
to `Q`. Given a witness `H : SynthHaltReduction P` it leaves the reduction `P ⪯_s Q` as a goal,
and `undec from H via?` searches for it. `undec from H via r₁, …, rₙ` composes exactly the named
reductions, with no search. `undec?` and `undec? from P` suggest a script for the route found,
written with `reduce_from s via r₁, via r₂, …` (`Foundations/Computability/ReduceFrom.lean`), the
tactic library proofs use, so that replaying the proof does not depend on which reductions are
tagged. The goals `¬ ComputablePred Q`,
`¬ MachineDecidable enc Q`, `HaltReduction Q` and `HaltHard Q` are handled in
`Foundations/Computability/UndecTransfer.lean`.
-/

namespace DiagonaLean.Synthetic.Notation

open Lean Meta Elab Tactic DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.ReductionChain

/-- With a source predicate `P`, `undec from P` finds reductions from halting to `P` and from `P`
to the goal. With a witness `H : SynthHaltReduction P` it leaves the second leg as a goal,
preserving the manual form. `undec from H via?` searches for that leg as well. -/
syntax (name := undecFrom) "undec" " from " term (" via?")? : tactic

/-- `undec from H via r₁, …, rₙ` composes the source `H` with exactly the reductions `rᵢ`, in
order. The source is a halting reduction or a predicate; for a predicate, the route from halting
to it is found by search. -/
@[tactic_alt undecFrom]
syntax (name := undecFromVia) "undec" " from " term " via " term,+ : tactic

/-- Find a route and suggest a replayable `reduce_from … via …` script for it. -/
syntax (name := undecSuggest) "undec?" (" from " term)? : tactic

/-- The halting problem, as a node of the reduction graph. -/
def haltNode : Expr := mkConst ``Halt.HaltProblem

/-- The target `P` of a halting reduction `SynthHaltReduction P`, if `type` is one. -/
def haltReductionTarget? (type : Expr) : MetaM (Option Expr) := do
  let some (p, q) ← observing? (reductionEndpoints type) | return none
  if ← samePredicate p haltNode then return some q else return none

/-- `e` is a predicate: its type is a function type into `Prop`. -/
def isPredicate (e : Expr) : MetaM Bool := do
  forallTelescopeReducing (← inferType e) fun xs body => return !xs.isEmpty && body.isProp

/-- The proposition `P` of a negation, written `¬ P` or `P → False`. The library's
`Undecidable P` abbreviates `¬ ComputablePred P` and is read as that negation. -/
def notBody? (type : Expr) : Option Expr :=
  let type := type.consumeMData
  if type.isAppOfArity `DiagonaLean.Foundations.Computability.Undecidable 3 then
    some (mkAppN (.const `ComputablePred type.getAppFn.constLevels!) type.getAppArgs)
  else
  match type.not? with
  | some body => some body
  | none =>
    if type.isArrow && type.bindingBody!.consumeMData.isConstOf ``False then
      some type.bindingDomain!
    else none

/-- `type` is `¬ ComputablePred Q` or `¬ MachineDecidable enc Q`, the goals that
`Foundations/Computability/UndecTransfer.lean` handles. -/
def isHardnessGoal (type : Expr) : Bool :=
  let type := type.consumeMData
  -- the proved goals, handled in `UndecTransfer` by `reduce_from`
  type.isAppOf `DiagonaLean.Foundations.Computability.HaltReduction ||
  type.isAppOf `DiagonaLean.Foundations.Computability.HaltHard ||
  match notBody? type with
  | some body => body.isAppOf `ComputablePred || body.isAppOf ``MachineDecidable
  | none => false

/-- The goals `undec from` proves, for error messages. -/
def undecGoalShapes : MessageData :=
  m!"undec from proves goals of the form `SynthHaltReduction Q`, and, with \
    `DiagonaLean.Foundations.Computability.UndecTransfer` imported, `¬ ComputablePred Q`, \
    `¬ MachineDecidable enc Q`, `HaltReduction Q` and `HaltHard Q`"

/-- Compose reductions given first to last. With none, the identity reduction on `source`. -/
def composeWitnesses (source : Expr) : List Expr → MetaM Expr
  | [] => mkAppM ``SynthReduction.refl #[source]
  | w :: rest => rest.foldlM (fun acc e => mkAppM ``SynthReduction.trans #[acc, e]) w

/-- Close `goal` with `proof`, after checking its type. -/
def closeGoal (goal : MVarId) (proof : Expr) : MetaM Unit := do
  let type ← inferType proof
  unless ← isDefEq type (← goal.getType) do
    throwError m!"the route found proves{indentExpr type}\nnot the goal\
      {indentExpr (← goal.getType)}"
  goal.assign proof

/-- The reduction `r : P ⪯_s Q` named in a `via` list, as an edge. -/
def viaEdge (r : Term) : TacticM ReductionEdge := do
  let e ← instantiateMVars (← elabTerm r none)
  let some edge ← syntheticEdge? (← whnf (← inferType e)) e |
    throwErrorAt r m!"expected a reduction `P ⪯_s Q`, but{indentExpr e}\nhas type\
      {indentExpr (← inferType e)}"
  return edge

/-- `e` printed with all arguments, so that predicates differing only in implicit arguments are
told apart in an error. -/
def ppExplicit (e : Expr) : MetaM MessageData := do
  return indentD (← withOptions (fun o => o.setBool `pp.explicit true) (ppExpr e))

/-- Check that each reduction of `path` starts where the previous one ends, starting at `source`,
and that the last one ends at `target`. The syntax `refs` names the reductions, for errors. -/
def checkChain (source target : Expr) (path : List ReductionEdge) (refs : List Syntax) :
    MetaM Unit := do
  let mut current := source
  for edge in path, ref in refs do
    unless ← isDefEq edge.source current do
      throwErrorAt ref m!"this reduction starts at{← ppExplicit edge.source}\nbut the previous \
        step ends at{← ppExplicit current}"
    current := edge.target
  unless ← isDefEq current target do
    throwError m!"the route ends at{← ppExplicit current}\nnot at the goal's{← ppExplicit target}"

/-- The edge of a halting reduction `w : SynthHaltReduction P`. -/
def haltEdge (w target : Expr) : ReductionEdge := { source := haltNode, target, witness := w }

/-- The term `stx` elaborates to `e` again, against the expected type `expected?`. -/
def elaboratesTo (stx : Term) (e : Expr) (expected? : Option Expr) : TermElabM Bool :=
  withoutModifyingState do
    try
      let e' ← Term.elabTermAndSynthesize stx expected?
      isDefEq e' e
    catch _ => return false

/-- `e` as a term for a suggestion, with proofs printed, and implicit arguments and the types of
numerals where they are needed. `none` if even that term does not elaborate to `e` again, against
the expected type `expected?`. -/
def delabForScript (e : Expr) (expected? : Option Expr := none) : TermElabM (Option Term) := do
  let stx ← withOptions (fun o => o.setBool `pp.proofs true) <| PrettyPrinter.delab e
  if ← elaboratesTo stx e expected? then return stx
  let stx ← withOptions (fun o => ((o.setBool `pp.proofs true).setBool `pp.analyze true).setBool
    `pp.analyze.trustOfNat false) <| PrettyPrinter.delab e
  if ← elaboratesTo stx e expected? then return stx
  return none

/-- `e` as a term for a suggestion. A local hypothesis whose name is inaccessible or shadowed is
written `‹type›`, which finds it by its type. -/
def delabTermForScript (e : Expr) (expected? : Option Expr := none) : TermElabM (Option Term) := do
  if e.isFVar then
    let decl ← e.fvarId!.getDecl
    let named := ((← getLCtx).findFromUserName? decl.userName).map (·.fvarId)
    if decl.userName.hasMacroScopes || named != some e.fvarId! then
      let some type ← delabForScript (← instantiateMVars decl.type) | return none
      return some (← `(‹$type›))
  delabForScript e expected?

/-- The term naming `e` in a suggestion. -/
def delabEdge (e : ReductionEdge) : TermElabM (Option Term) := delabTermForScript e.name

/-- A script to suggest: a tactic, or a `reduce_from` chain as its pieces of text, which are
joined with spaces and wrapped at 100 columns. -/
inductive Script | tactic (t : TSyntax `tactic) | text (pieces : List String)

/-- `t` printed for a script, in parentheses unless it is a name or `‹type›`, which `reduce_from`
reads as one argument. -/
def scriptTerm (t : Term) : MetaM String := do
  let s := toString (← PrettyPrinter.ppTerm t)
  let atomic := t.raw.isIdent || t.raw.isOfKind ``Lean.Parser.Term.paren ||
    (s.startsWith "‹" && s.endsWith "›" && (s.splitOn "‹").length == 2)
  return if atomic then s else s!"({s})"

/-- The script `reduce_from s via r₁, via r₂, …` composing the source term `s` with the links
`rᵢ`. Library proofs are written with `reduce_from` (`Foundations/Computability/ReduceFrom.lean`),
which proves the same goals along the same links and also the proved goals (`HaltReduction`,
`HaltHard`); the search of `undec?` only finds the route. -/
def reduceFromScript (src : Term) (links : Array Term) : MetaM Script := do
  let links ← links.mapM scriptTerm
  let n := links.size
  let pieces := links.toList.zipIdx.map fun (l, i) => s!"via {l}" ++ if i + 1 < n then "," else ""
  return .text (s!"reduce_from {← scriptTerm src}" :: pieces)

/-- The pieces joined with spaces, wrapped at 100 columns for text starting at column `col`; a
continuation line is indented 4 more. -/
def wrapPieces (col : Nat) : List String → String
  | [] => ""
  | p :: ps => Id.run do
    let indent := "\n" ++ "".pushn ' ' (col + 4)
    let mut out := p
    let mut width := col + p.length
    for q in ps do
      if width + 1 + q.length > 100 then
        out := out ++ indent ++ q
        width := col + 4 + q.length
      else
        out := out ++ " " ++ q
        width := width + 1 + q.length
    return out

/-- The script `reduce_from s via r₁, …` for a route whose first step is the source `s`, or
`exact s` for a route of one step. `none` if some step has no term that elaborates again. -/
def routeScript : List ReductionEdge → TermElabM (Option Script)
  | [] => return some (.tactic (← `(tactic| exact $(mkIdent ``SynthReduction.refl) _)))
  | [s] => do
    let some t ← delabEdge s | return none
    return some (.tactic (← `(tactic| exact $t)))
  | s :: rest => do
    let some t ← delabEdge s | return none
    let some names := (← rest.toArray.mapM delabEdge).mapM id | return none
    return some (← reduceFromScript t names)

/-- Suggest `script` at `ref`, or say that the route has no replayable script. -/
def suggestScript (ref : Syntax) (script : Option Script) : MetaM Unit := do
  match script with
  | some (.tactic script) => TryThis.addSuggestion ref { suggestion := .tsyntax script }
  | some (.text pieces) =>
    let fileMap ← getFileMap
    let col := match ref.getPos? with
      | some pos => (fileMap.toPosition pos).column
      | none => 0
    TryThis.addSuggestion ref { suggestion := .string (wrapPieces col pieces) }
  | none => logInfoAt ref "a step of this route has no term that elaborates again, so there is \
      no script to suggest; name it in a `via` list"

/-- Fail unless `e` is a halting reduction or a predicate, naming what `undec from` accepts. -/
def requireSource (h : Syntax) (e : Expr) : MetaM Unit := do
  unless ← isPredicate e do
    throwErrorAt h m!"undec from expects a halting reduction `SynthHaltReduction P` or a \
      predicate `P`, but{indentExpr e}\nhas type{indentExpr (← inferType e)}"
  if e.hasExprMVar then throwErrorAt h "specify a fully determined source predicate"

/-- The first steps of a route through the source `e`: the halting reduction `e` itself, or a
route from halting to the predicate `e`. -/
def routeStart (h : Syntax) (e : Expr) (edges : Array ReductionEdge) :
    TacticM (List ReductionEdge) := do
  if let some p ← haltReductionTarget? (← inferType e) then return [haltEdge e p]
  requireSource h e
  reductionPathFrom edges haltNode e

/-- The route from halting to `q` through the source `h`, found by search after the source. -/
def routeThrough (h : Term) (q : Expr) : TacticM (List ReductionEdge) := do
  let e ← instantiateMVars (← elabTerm h none)
  let edges ← reductionEdges
  let start ← routeStart h e edges
  let mid := (start.getLast?.map (·.target)).getD haltNode
  return start ++ (← reductionPathFrom edges mid q)

/-- Close the main goal `SynthHaltReduction Q` along `route`, reporting it when requested. -/
def closeAlong (goal : MVarId) (route : List ReductionEdge) : TacticM Unit := do
  reportReductionPath haltNode route
  closeGoal goal (← composeWitnesses haltNode (route.map (·.witness)))
  replaceMainGoal []

/-- Another file adds an elaborator for the tactic syntax `kind`; for `undec from` this is
`Foundations/Computability/UndecTransfer.lean`. -/
def hasOtherElaborator (kind : SyntaxNodeKind) : CoreM Bool :=
  return (tacticElabAttribute.getEntries (← getEnv) kind).length > 1

/-- The predicate `Q` of the goal `SynthHaltReduction Q`. On a noncomputability goal, defer to the
elaborator of `kind` in `UndecTransfer`, when there is one; any other goal is an error naming the
goals `undec from` proves. -/
def requireHaltGoal (goal : MVarId) (kind : SyntaxNodeKind) : MetaM Expr := do
  let type ← instantiateMVars (← goal.getType)
  let some q ← haltReductionTarget? type | do
    if isHardnessGoal type && (← hasOtherElaborator kind) then throwUnsupportedSyntax
    throwError m!"{undecGoalShapes}\nThe goal is{indentExpr type}"
  return q

/-- `undec from h` with a halting reduction `h : SynthHaltReduction P` that does not prove the
goal `SynthHaltReduction Q`: leave the link `P ⪯_s Q` as the new goal. -/
def leaveLink (goal : MVarId) (e p q : Expr) : TacticM Unit := do
  let link ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``SynthReduction #[p, q])
  closeGoal goal (← mkAppM ``SynthHaltReduction.comp #[e, link])
  replaceMainGoal [link.mvarId!]

elab_rules : tactic
  | `(tactic| undec from $h via?) => withMainContext do
    let goal ← getMainGoal
    closeAlong goal (← routeThrough h (← requireHaltGoal goal ``undecFrom))
  | `(tactic| undec from $h) => withMainContext do
    let goal ← getMainGoal
    let q ← requireHaltGoal goal ``undecFrom
    let e ← instantiateMVars (← elabTerm h none)
    match ← haltReductionTarget? (← inferType e) with
    | none =>
      requireSource h e
      let edges ← reductionEdges
      closeAlong goal ((← reductionPathFrom edges haltNode e) ++ (← reductionPathFrom edges e q))
    | some p =>
      if ← isDefEq (← inferType e) (← goal.getType) then
        goal.assign e
        replaceMainGoal []
      else leaveLink goal e p q
  | `(tactic| undec from $h via $rs,*) => withMainContext do
    let goal ← getMainGoal
    let q ← requireHaltGoal goal ``undecFromVia
    let e ← instantiateMVars (← elabTerm h none)
    let start ← routeStart h e (← reductionEdges)
    let links ← rs.getElems.toList.mapM viaEdge
    let mid := (start.getLast?.map (·.target)).getD haltNode
    checkChain mid q links (rs.getElems.toList.map (·.raw))
    closeAlong goal (start ++ links)

elab_rules : tactic
  | `(tactic| undec?%$tk) => withMainContext do
    let goal ← getMainGoal
    let type ← instantiateMVars (← goal.getType)
    if isHardnessGoal type then
      throwError m!"on a goal{indentExpr type}\nname a source problem: `undec? from P`"
    let q ← requireHaltGoal goal ``undecSuggest
    let route ← reductionPathFrom (← reductionEdges) haltNode q
    closeAlong goal route
    suggestScript tk (← routeScript route)
  | `(tactic| undec?%$tk from $h) => withMainContext do
    let goal ← getMainGoal
    let route ← routeThrough h (← requireHaltGoal goal ``undecSuggest)
    withOptions (fun o => o.setBool `undec.showRoute true) <| closeAlong goal route
    suggestScript tk (← routeScript route)

end DiagonaLean.Synthetic.Notation
