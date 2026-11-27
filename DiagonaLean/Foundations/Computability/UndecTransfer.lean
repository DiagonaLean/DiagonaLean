/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.Computability.ComputableReduction
import DiagonaLean.Synthetic.Tactics.UndecFrom

@[expose] public section

/-! # Transferring noncomputability with `undec from`

For `¬ ComputablePred Q` or `¬ MachineDecidable enc Q`, give `undec from` either a source
predicate with a registered hardness theorem or a proof of `¬ ComputablePred P` (also written
`ComputablePred P → False`). Search prefers a route whose reduction functions have computability
proofs, and proves each function's computability at most once per call. If evidence is missing,
the corresponding computability obligations remain as goals. `undec from h via r₁, …, rₙ` follows
exactly the named reductions, and `undec? from P` suggests such a script.
`undecTagProblems` lists ill-formed `@[undecReduction]` and `@[undecHardness]` declarations;
`scripts/CheckUndecTags.lean` runs it in CI.
-/

namespace DiagonaLean.Foundations.Computability

open Lean Meta Elab Tactic DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.ReductionChain

/-- Register a theorem of the form `¬ ComputablePred P`. Implicit parameters and instances
are inferred from the source predicate when applying the theorem. -/
register_label_attr undecHardness

/-- The predicate `P` of a noncomputability statement `¬ ComputablePred P`, without unfolding
`P`. -/
def hardPredicate? (type : Expr) : Option Expr := do
  let body ← Synthetic.Notation.notBody? type
  guard (body.isAppOf ``ComputablePred)
  return body.getAppArgs.back!

/-- The type of an `@[undecHardness]` theorem is a noncomputability statement after its
parameters. -/
def isHardnessStatement (type : Expr) : MetaM Bool :=
  forallTelescope type fun xs body => do
    if (hardPredicate? body).isSome then return true
    let some x := xs.back? | return false
    return body.isConstOf ``False && (← inferType x).isAppOf ``ComputablePred

/-- The ill-formed `@[undecReduction]` and `@[undecHardness]` declarations, with the reason. The
tactics skip them, so `scripts/CheckUndecTags.lean` reports them in CI. -/
def undecTagProblems : MetaM (Array MessageData) := do
  let mut bad ← badReductionTags
  for name in ← labelled `undecHardness do
    let info ← getConstInfo name
    unless ← isHardnessStatement info.type do
      bad := bad.push m!"{.ofConstName name} is tagged @[undecHardness] but has type \
        {info.type}, not ¬ ComputablePred P"
  return bad

/-- Resolve either an explicit theorem or a source predicate, preferring local hypotheses. With
`mayPostpone`, implicit arguments of the theorem may stay undetermined for the caller to fix. -/
def resolveHardness (stx : Syntax) (mayPostpone := false) : TacticM (Expr × Expr) := do
  let mut arg ← instantiateMVars (← elabTerm stx none mayPostpone)
  if mayPostpone && (← instantiateMVars (← inferType arg)).isMVar then
    -- a postponed source, such as a tactic block, is elaborated now
    Term.synthesizeSyntheticMVarsNoPostponing
    arg ← instantiateMVars arg
  let type ← instantiateMVars (← inferType arg)
  if let some p := hardPredicate? type then return (p, arg)
  unless ← Synthetic.Notation.isPredicate arg do
    throwErrorAt stx m!"undec from expects a proof of `¬ ComputablePred P` or a predicate \
      `P`, but{indentExpr arg}\nhas type{indentExpr type}"
  let wanted ← try mkAppM ``Not #[← mkAppM ``ComputablePred #[arg]] catch _ =>
    throwErrorAt stx m!"ComputablePred {arg} needs a `Primcodable` instance on its domain"
  let goal ← mkFreshExprSyntheticOpaqueMVar wanted
  if ← goal.mvarId!.assumptionCore then return (arg, ← instantiateMVars goal)
  for name in ← labelled `undecHardness do
    if let some proof ← observing? (do
      let [] ← goal.mvarId!.apply (← mkConstWithFreshMVarLevels name) | failure
      pure (← instantiateMVars goal)) then return (arg, proof)
  throwErrorAt stx m!"missing hardness theorem for {arg}. Supply a proof of {wanted} \
    or register one with @[undecHardness]."

/-- Try the library's computability lemmas in isolation. An open goal rejects this edge. -/
def certificate? (type : Expr) : TacticM (Option Expr) := observing? do
  let g ← mkFreshExprSyntheticOpaqueMVar type
  let tac ← `(tactic| first | assumption | fun_prop | (apply Primrec.to_comp; fun_prop))
  let [] ← withoutRecover <| evalTacticAt tac g.mvarId! | failure
  return ← instantiateMVars g

/-- The type `Computable r.f` of a computability certificate for the edge `r`. -/
def certificateType (e : ReductionEdge) : MetaM Expr := do
  mkAppM ``Computable #[← mkAppM ``SynthReduction.f #[e.witness]]

/-- An edge is eligible for a structural route when its certificate type can be stated. -/
def certificateTypeOf? (e : ReductionEdge) : TacticM (Option Expr) :=
  observing? (certificateType e)

/-- A proved reduction supplies its own computability certificate, and a script names it rather
than its synthetic part. -/
def libraryEdge? (type witness : Expr) : MetaM (Option ReductionEdge) := do
  let_expr ComputableReduction _ _ _ _ p q := type | return ← syntheticEdge? type witness
  let synth ← mkAppM ``ComputableReduction.toSynth #[witness]
  let cert ← mkAppM ``ComputableReduction.computable #[witness]
  return some
    { source := p, target := q, witness := synth, computable? := cert, original? := witness }

/-- The computability certificates found during one call, by edge witness; `none` records a
failed search. -/
abbrev CertificateCache := IO.Ref (Std.HashMap Expr (Option Expr))

/-- A certificate for an edge: its own proof, a cached result, or one found by `certificate?`. -/
def edgeCertificate? (cache : CertificateCache) (e : ReductionEdge) :
    TacticM (Option Expr) := do
  if let some proof := e.computable? then return some proof
  if let some known := (← cache.get)[e.witness]? then return known
  let found ← match ← observing? (certificateType e) with
    | none => pure none
    | some type => certificate? type
  cache.modify (·.insert e.witness found)
  return found

/-- A certificate for each edge of `path`, or a new goal for its computability. -/
def certifyPath (cache : CertificateCache) (path : List ReductionEdge) :
    TacticM (List (ReductionEdge × Expr)) :=
  path.mapM fun edge => do
    let cert ← (← edgeCertificate? cache edge).getDM do
      mkFreshExprSyntheticOpaqueMVar (← certificateType edge)
    return (edge, cert)

/-- Prefer a fully certified route. Keep individual obligations on a structural route if
the caller needs to supply a certificate interactively. -/
def hardnessRoute (cache : CertificateCache) (source target : Expr) :
    TacticM (List (ReductionEdge × Expr)) := do
  let mut edges ← reductionEdges libraryEdge?
  let mut certified ← findReductionPath? edges source target (edgeCertificate? cache)
  if certified.isNone then
    edges ← libraryReductionEdges edges libraryEdge?
    certified ← findReductionPath? edges source target (edgeCertificate? cache)
  if let some path := certified then return path
  let some path ← findReductionPath? edges source target certificateTypeOf? |
    noReductionPath source target
  certifyPath cache (path.map Prod.fst)

/-- Prove the main goal `¬ ComputablePred target` from `proof : ¬ ComputablePred source` along
`path`. Missing certificates become the new goals. -/
def applyRoute (source proof : Expr) (path : List (ReductionEdge × Expr)) : TacticM Unit := do
  reportReductionPath source (path.map Prod.fst)
  let mut pending := []
  let mut result := proof
  for (edge, cert) in path do
    if cert.isMVar then
      pending := cert.mvarId! :: pending
      if undec.showRoute.get (← getOptions) then
        logInfo m!"{← problemDisplayName edge.source} → {← problemDisplayName edge.target} \
          needs {← inferType cert}"
    result ← mkAppM ``not_computablePred_of_reduces #[edge.witness, cert, result]
  let goal ← getMainGoal
  unless ← isDefEq (← inferType result) (← goal.getType) do
    throwError m!"the route proves{indentExpr (← inferType result)}\nnot the goal\
      {indentExpr (← goal.getType)}"
  goal.assign result
  replaceMainGoal pending.reverse

/-- For a main goal `¬ MachineDecidable enc Q` or `¬ ComputablePred Q`: reduce the first to the
second, and return the encoding obligation, if any, and `Q`. Any other goal gives `none`. -/
def prepareHardnessGoal : TacticM (Option (Option MVarId × Expr)) := do
  let some body := Synthetic.Notation.notBody? (← instantiateMVars (← getMainTarget)) | return none
  let mut encoding := none
  if body.isAppOf ``MachineDecidable then
    evalTactic (← `(tactic| refine not_machineDecidable_of_not_computablePred ?_ ?_))
    let [enc, hard] ← getGoals | throwError "expected encoding and hardness obligations"
    encoding := some enc
    setGoals [hard]
  else unless body.isAppOf ``ComputablePred do return none
  let some target := hardPredicate? (← instantiateMVars (← getMainTarget)) | return none
  return some (encoding, target)

/-- Discharge the encoding obligation by the computability lemmas, or leave it as the last goal. -/
def finishEncoding (encoding : Option MVarId) : TacticM Unit := do
  let some enc := encoding | return
  let type ← enc.getType
  if let some cert ← certificate? type then enc.assign cert
  else
    if undec.showRoute.get (← getOptions) then logInfo m!"The encoding needs {type}"
    setGoals ((← getGoals) ++ [enc])

/-- The reduction `r` named in a `via` list, synthetic or proved, as an edge. -/
def hardnessViaEdge (r : Term) : TacticM ReductionEdge := do
  let e ← instantiateMVars (← elabTerm r none)
  let some edge ← libraryEdge? (← whnf (← inferType e)) e |
    throwErrorAt r m!"expected a reduction `P ⪯_s Q` or `P ⪯ Q`, but{indentExpr e}\nhas type\
      {indentExpr (← inferType e)}"
  return edge

/-- The script `undec from proof via r₁, …, rₙ` for a route from a hardness proof. `none` if
some term does not elaborate again. -/
def hardnessScript (proof : Expr) (path : List ReductionEdge) :
    TermElabM (Option (TSyntax `tactic)) := do
  -- the source is replayed against the route, which fixes its implicit arguments
  let some src ← Synthetic.Notation.delabTermForScript proof (← inferType proof) | return none
  match path with
  | [] => return some (← `(tactic| undec from $src))
  | _ =>
    let some names := (← path.toArray.mapM Synthetic.Notation.delabEdge).mapM id | return none
    return some (← `(tactic| undec from $src via $names,*))

/-- `undec from h` on a noncomputability goal, suggesting a script at `ref` when given. -/
def undecHardness (h : Term) (ref : Option Syntax) : TacticM Unit := do
  let some (encoding, target) ← prepareHardnessGoal | throwUnsupportedSyntax
  let (source, proof) ← resolveHardness h
  let cache ← IO.mkRef {}
  let path ← hardnessRoute cache source target
  match ref with
  | none => applyRoute source proof path
  | some tk =>
    withOptions (fun o => o.setBool `undec.showRoute true) <| applyRoute source proof path
    Synthetic.Notation.suggestScript tk (← hardnessScript proof (path.map Prod.fst))
  finishEncoding encoding

elab_rules : tactic
  | `(tactic| undec from $h $[via?]?) => focus <| withMainContext do undecHardness h none
  | `(tactic| undec from $h via $rs,*) => focus <| withMainContext do
    let some (encoding, target) ← prepareHardnessGoal | throwUnsupportedSyntax
    -- elaborating a link synthesizes pending instances, so the links come before the source
    let links ← rs.getElems.toList.mapM hardnessViaEdge
    let (source, proof) ← resolveHardness h (mayPostpone := true)
    Synthetic.Notation.checkChain source target links (rs.getElems.toList.map (·.raw))
    Term.synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let proof ← instantiateMVars proof
    applyRoute source proof (← certifyPath (← IO.mkRef {}) links)
    finishEncoding encoding
  | `(tactic| undec?%$tk from $h) => focus <| withMainContext do undecHardness h (some tk)

end DiagonaLean.Foundations.Computability
