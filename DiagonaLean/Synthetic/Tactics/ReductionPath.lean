/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Lean.LabelAttribute
import Lean.Elab.Tactic.Basic
import Std.Data.HashMap
import DiagonaLean.Synthetic.ReductionChain
import DiagonaLean.Synthetic.ReductionCheck

@[expose] public section

/-! # Finding a chain of compiled many-one reductions

The tactic searches local hypotheses and tagged definitions first, then also considers
untagged concrete reduction definitions available in the environment. Each search is breadth first.
A `SynthHaltReduction P` is an edge from halting to `P`. Run
`show_term reduction_path` to see the named definitions in the resulting term.
-/

namespace DiagonaLean.Synthetic.ReductionChain

open Lean Meta Elab Tactic DiagonaLean.Synthetic.Definitions

/-- Register a concrete many-one reduction for path search. -/
register_label_attr undecReduction

/-- Optional display name for a predicate in a reduction route. -/
class ProblemName {α : Type*} (p : α → Prop) where
  /-- Name as it would appear in a mathematical statement. -/
  text : String

/-- The halting problem is displayed as "Halting". -/
instance : ProblemName Halt.HaltProblem := ⟨"Halting"⟩

/-- Show the route chosen by the tactic, including unmet computability obligations. -/
register_option undec.showRoute : Bool := {
  defValue := false
  descr := "show the predicates along a reduction route"
}

/-- A reduction in the current environment or local context. -/
structure ReductionEdge where
  /-- Predicate on the input to the reduction. -/
  source : Expr
  /-- Predicate on its output. -/
  target : Expr
  /-- Lean term of type `source ⪯_s target`. -/
  witness : Expr
  /-- Computability evidence carried by a proved reduction, when available. -/
  computable? : Option Expr := none
  /-- The term to name in a replayable script, when it differs from `witness`. -/
  original? : Option Expr := none
  deriving Inhabited

/-- The term that names the edge `e` in a replayable script. -/
def ReductionEdge.name (e : ReductionEdge) : Expr := e.original?.getD e.witness

/-- Read the source and target predicates, unfolding aliases such as `SynthHaltReduction`. -/
def reductionEndpoints (type : Expr) : MetaM (Expr × Expr) := do
  let type ← whnf type
  let_expr DiagonaLean.Synthetic.Definitions.SynthReduction _ _ p q := type
    | throwError "expected a many-one reduction, got {type}"
  return (p, q)

/-- Recognize a concrete reduction by its normalized type. -/
def syntheticEdge? (type witness : Expr) : MetaM (Option ReductionEdge) := do
  let_expr DiagonaLean.Synthetic.Definitions.SynthReduction _ _ p q := type | return none
  return some { source := p, target := q, witness }

/-- Collect local reduction witnesses and imported registrations. Local witnesses come first. -/
def reductionEdges (recognize : Expr → Expr → MetaM (Option ReductionEdge) := syntheticEdge?) :
    MetaM (Array ReductionEdge) := do
  let mut edges := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if let some edge ← recognize (← whnf decl.type) decl.toExpr then
      edges := edges.push edge
  for name in ← labelled `undecReduction do
    let info ← getConstInfo name
    unless info.isDefinition && info.levelParams.isEmpty do continue
    let some (p, q) ← observing? (reductionEndpoints info.type) | continue
    edges := edges.push { source := p, target := q, witness := mkConst name }
  return edges

/-- The `@[undecReduction]` declarations that are not closed reduction definitions, with the
reason. The search skips them; `scripts/CheckUndecTags.lean` reports them in CI. -/
def badReductionTags : MetaM (Array MessageData) := do
  let mut bad := #[]
  for name in ← labelled `undecReduction do
    let info ← getConstInfo name
    if !info.isDefinition then
      bad := bad.push m!"{.ofConstName name} is not a definition"
    else if !info.levelParams.isEmpty then
      bad := bad.push m!"{.ofConstName name} has universe parameters"
    else if (← observing? (reductionEndpoints info.type)).isNone then
      bad := bad.push m!"{.ofConstName name} has type {info.type}, not a closed reduction \
        P ⪯_s Q; specialize it"
  return bad

/-- Add the visible, compiled, parameter-free reduction definition `ci` to `edges`, unless it is
tagged, private to another module, internal, unsafe or deprecated. -/
def addLibraryEdge (recognize : Expr → Expr → MetaM (Option ReductionEdge)) (env : Environment)
    (tagged : NameSet) (imported : Bool) (edges : Array ReductionEdge) (ci : ConstantInfo) :
    MetaM (Array ReductionEdge) := do
  let n := ci.name
  unless ci.isDefinition && ci.levelParams.isEmpty && ci.type.getAppFn.isConst do return edges
  if imported && isPrivateName n || (privateToUserName n).isInternalDetail ||
      tagged.contains n || ci.isUnsafe || Linter.isDeprecated env n then
    return edges
  let some edge ← recognize (← whnf ci.type) (mkConst n) | return edges
  if (ReductionCheck.compiledViolation env n).isSome then return edges
  return edges.push edge

/-- Extend the preferred edges with visible, compiled, parameter-free reduction definitions.
Only modules that transitively import the reduction type can contain a witness. -/
def libraryReductionEdges (preferred : Array ReductionEdge)
    (recognize : Expr → Expr → MetaM (Option ReductionEdge) := syntheticEdge?) :
    MetaM (Array ReductionEdge) := do
  let env ← getEnv
  let tagged := NameSet.ofList (preferred.toList.filterMap (·.witness.constName?))
  let mut edges := preferred
  let mut relevant : NameSet := {}
  for mod in env.header.modules, data in env.header.moduleData do
    if mod.module == `DiagonaLean.Synthetic.Definitions ||
        data.imports.any (fun imp => relevant.contains imp.module) then
      relevant := relevant.insert mod.module
      for ci in data.constants do
        edges ← addLibraryEdge recognize env tagged true edges ci
  env.constants.map₂.foldlM (fun es _ ci => addLibraryEdge recognize env tagged false es ci) edges

/-- The constant heading the predicate `p`, used to index edges. Reducible constants are unfolded
while the unfolding is again headed by a constant, so an `abbrev` such as `PCP.PCProblem` and
its unfolding `@PCP.DecisionProblem Bool` get the same key. A predicate with no constant head
gets `Name.anonymous`. -/
def predicateKey (p : Expr) : MetaM Name := do
  let mut e := (← instantiateMVars p).consumeMData.eta
  for _ in [0:32] do
    let some c := e.getAppFn.constName? | return .anonymous
    unless (← getReducibilityStatus c) matches .reducible do return c
    let some e' ← unfoldDefinition? e | return c
    let e' := e'.headBeta.eta
    unless e'.getAppFn.isConst do return c
    e := e'
  return e.getAppFn.constName?.getD .anonymous

/-- Two predicates are the same node of the graph if they are definitionally equal with only
reducible and instance definitions unfolded. The test assigns no metavariable of the goal. -/
def samePredicate (p q : Expr) : MetaM Bool :=
  withNewMCtxDepth <| withTransparency .instances <| isDefEq p q

/-- The edges grouped by the key of their source predicate. -/
def edgeIndex (edges : Array ReductionEdge) : MetaM (Std.HashMap Name (Array ReductionEdge)) :=
  edges.foldlM (init := {}) fun index e => do
    let k ← predicateKey e.source
    return index.insert k ((index.getD k #[]).push e)

/-- The edges that may leave `node`: those indexed under its key and those whose source has no
constant head. A node with no constant head may meet any edge. -/
def candidateEdges (edges : Array ReductionEdge) (index : Std.HashMap Name (Array ReductionEdge))
    (node : Expr) : MetaM (Array ReductionEdge) := do
  let k ← predicateKey node
  if k.isAnonymous then return edges
  return index.getD k #[] ++ index.getD .anonymous #[]

/-- Search breadth first among edges accepted by `select`. Keep the evidence it returns for
each edge. A rejected edge does not mark its target as visited. -/
def findReductionPath? {α : Type} (edges : Array ReductionEdge) (source target : Expr)
    (select : ReductionEdge → TacticM (Option α)) :
    TacticM (Option (List (ReductionEdge × α))) := do
  if ← samePredicate source target then return some []
  let index ← edgeIndex edges
  let mut queue : Array (Expr × List (ReductionEdge × α)) := #[(source, [])]
  let mut head := 0
  while head < queue.size do
    let (current, path) := queue[head]!
    head := head + 1
    for edge in ← candidateEdges edges index current do
      unless ← samePredicate edge.source current do continue
      if ← queue.anyM (fun node => samePredicate node.1 edge.target) then continue
      let some evidence ← select edge | continue
      let next := (edge, evidence) :: path
      if ← samePredicate edge.target target then return some next.reverse
      queue := queue.push (edge.target, next)
  return none

/-- Report both endpoints when there is no path in the available graph, and any
`@[undecReduction]` declarations the search had to skip. -/
def noReductionPath {α : Type} (source target : Expr) : TacticM α := do
  let bad ← badReductionTags
  let skipped := if bad.isEmpty then m!"" else
    m!"\nSkipped @[undecReduction] declarations:\n{MessageData.joinSep bad.toList "\n"}"
  throwError m!"no reduction path found from {source} to {target}\n\
    Import a concrete reduction definition or supply a specialized witness locally.{skipped}"

/-- Every edge is accepted, with no evidence. -/
def acceptEdge (_ : ReductionEdge) : TacticM (Option Unit) := pure (some ())

/-- Prefer the registered graph, falling back to untagged concrete definitions. -/
def reductionPathFrom (edges : Array ReductionEdge) (source target : Expr) :
    TacticM (List ReductionEdge) := do
  if let some path ← findReductionPath? edges source target acceptEdge then return path.map Prod.fst
  let library ← libraryReductionEdges edges
  if let some path ← findReductionPath? library source target acceptEdge then
    return path.map Prod.fst
  noReductionPath source target

/-- Display a problem's registered mathematical name, falling back to its Lean expression. -/
def problemDisplayName (p : Expr) : MetaM MessageData := do
  if let some label ← observing? (mkAppOptM ``ProblemName.text #[none, some p, none]) then
    if let some text := getStringValue? (← whnf label) then return m!"{text}"
  return m!"{p}"

/-- Report the predicates in the selected route when requested. -/
def reportReductionPath (source : Expr) (path : List ReductionEdge) : TacticM Unit := do
  if undec.showRoute.get (← getOptions) then
    let names ← (source :: path.map (·.target)).mapM (fun p => problemDisplayName p)
    logInfo (MessageData.joinSep names " → ")

/-- Compose reductions, optionally passing through a given predicate. Reflexive legs add no term. -/
syntax (name := reductionPath) "reduction_path" (" via " term)? : tactic

elab_rules : tactic
  | `(tactic| reduction_path $[via $mid]?) => withMainContext do
    let goal ← getMainGoal
    let (p, q) ← reductionEndpoints (← instantiateMVars (← goal.getType))
    if p.hasExprMVar || q.hasExprMVar then
      throwError "reduction_path needs a known source and target predicate"
    let edges ← reductionEdges (recognize := syntheticEdge?)
    let path ← match mid with
      | none => reductionPathFrom edges p q
      | some term => do
        let mid ← instantiateMVars (← elabTerm term none)
        if mid.hasExprMVar then throwErrorAt term "specify a fully determined source predicate"
        let firstLeg ← reductionPathFrom edges p mid
        pure (firstLeg ++ (← reductionPathFrom edges mid q))
    reportReductionPath p path
    let witness ← match path.reverse.map (·.witness) with
      | [] => mkAppM ``SynthReduction.refl #[p]
      | last :: rest =>
        rest.foldlM (fun tail edge => mkAppM ``SynthReduction.trans #[edge, tail]) last
    unless ← isDefEq (← inferType witness) (← goal.getType) do
      throwError m!"the route found proves {← inferType witness}, not {← goal.getType}"
    goal.assign witness
    replaceMainGoal []

end DiagonaLean.Synthetic.ReductionChain
