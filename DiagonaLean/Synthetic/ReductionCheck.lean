/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus
-/

import Lean

/-! # Checking that reductions are computed by compiled definitions

`Undecidable p` is `Nonempty (HaltProblem ⪯ₘ p)`, and Lean's logic is classical, so as a statement
it holds for every `p` with a positive and a negative instance: the reduction can be the case split
`fun x => if HaltProblem x then a else b`. A reduction carries algorithmic content only when its
function is a program. `#check_reductions` checks this over every declaration of a `DiagonaLean`
module (with `local`, over the declarations of the current file instead). A reduction is a term of
`ManyOneReduces` or `SepReduces`.

1. Every definition whose type ends in a reduction, or whose body builds one with `.mk`, is
   compiled: safe, not `noncomputable`, without `implemented_by` or `extern`, and with compiled
   code. Lean refuses to compile a case split on an undecided `Prop`.
2. No theorem builds a reduction with `.mk`, since proofs are never compiled.
3. In a theorem, every data argument of a constant whose type mentions a reduction uses no
   noncomputable constant or axiom, and no variable bound inside the proof whose type carries a
   function, such as a function or a decidability instance obtained from an existential, or a
   subtype of functions. Variables bound by the statement are allowed, since the statement
   quantifies over them. Finite data obtained inside the proof, such as a letter or a program code,
   is allowed: one constant cannot encode infinitely many answers.
4. A definition returns a reduction only as its result, never inside another type such as an
   `Equiv` or a pair, and no axiom mentions a reduction. Otherwise a reduction could be produced
   from a function without passing through rules 1 to 3.

Passing these checks shows that every reduction runs as a Lean program. It does not show that a
Turing machine computes it on encoded inputs; that is the `ComputesReduction` hypothesis of
`not_machineDecidable_of_halt_reduces`.
-/

namespace DiagonaLean.Synthetic.ReductionCheck

open Lean Meta Elab Command

/-- The structures whose terms are reductions. -/
def reductionStructs : List Name :=
  [`DiagonaLean.Synthetic.Definitions.ManyOneReduces,
    `DiagonaLean.Foundations.Computability.SepReduces]

/-- The reduction structures, as a set. -/
def reductionStructSet : NameSet :=
  reductionStructs.foldl (fun s n => s.insert n) {}

/-- The constructors of the reduction structures. -/
def reductionCtors : NameSet :=
  reductionStructs.foldl (fun s n => s.insert (n ++ `mk)) {}

/-- `e` mentions a constant in `s`. -/
def mentionsAny (s : NameSet) (e : Expr) : Bool :=
  (e.find? fun t => match t with
    | .const n _ => s.contains n
    | _ => false).isSome

/-- The body of a type after its leading `∀` binders. -/
def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | .mdata _ e => conclusion e
  | e => e

/-- `ty` is the type of a reduction, possibly after parameters. -/
def isReductionType (ty : Expr) : Bool :=
  match (conclusion ty).getAppFn with
  | .const n _ => reductionStructs.contains n
  | _ => false

/-- `c` is part of the generated API of a reduction structure, such as `ManyOneReduces.mk.injEq`. -/
def isStructureAPI (c : Name) : Bool :=
  reductionStructs.any (·.isPrefixOf c)

/-- `c` is checked: it belongs to a `DiagonaLean` module, or, when `onlyLocal` is set, to the
current file. -/
def inScope (env : Environment) (onlyLocal : Bool) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx =>
    !onlyLocal && (`DiagonaLean).isPrefixOf (env.allImportedModuleNames[idx.toNat]?.getD .anonymous)
  | none => onlyLocal

/-- Why the definition `c` is not a compiled program, if it is not. -/
def compiledViolation (env : Environment) (c : Name) : Option String :=
  if isNoncomputable env c then some "is marked `noncomputable`"
  else if (Compiler.getImplementedBy? env c).isSome then some "uses `implemented_by`"
  else if isExtern env c then some "uses `extern`"
  else if (IR.findEnvDecl env c).isNone then some "has no compiled code"
  else none

/-- `ty` is the type of data that carries a function returning data: a function type, or an
inductive type with a field that carries one, such as a subtype of functions. Predicates, type
families and reductions do not count. `seen` holds the inductive types already entered. -/
partial def carriesFunction (seen : NameSet) (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  if ty.isForall then
    return ← forallTelescopeReducing ty fun _ body => do
      let body ← whnf body
      return !body.isSort && !(← isProp body)
  let .const n lvls := ty.getAppFn | return false
  if reductionStructSet.contains n || seen.contains n then return false
  let some (.inductInfo info) := (← getEnv).find? n | return false
  let args := ty.getAppArgs
  if args.size < info.numParams then return false
  let params := args.extract 0 info.numParams
  for ctor in info.ctors do
    let ctorTy ← inferType (mkAppN (.const ctor lvls) params)
    let found ← forallTelescopeReducing ctorTy fun fields _ => do
      for x in fields do
        let fty ← inferType x
        if !(← isProp fty) && (← carriesFunction (seen.insert n) fty) then return true
      return false
    if found then return true
  return false

/-- `e` is a proof; terms whose type cannot be inferred count as data. -/
def isProofTerm (e : Expr) : MetaM Bool := do
  try isProof e catch _ => pure false

/-- Rule 3 on a data argument `e`. `inner` holds the variables bound inside the argument itself. -/
partial def argViolations (params inner : FVarIdSet) (e : Expr) : MetaM (Array MessageData) := do
  if ← isProofTerm e then return #[]
  match e with
  | .const n _ =>
    let env ← getEnv
    if isNoncomputable env n then return #[m!"passes the noncomputable `{n}` to a reduction"]
    if let some (.axiomInfo _) := env.find? n then
      return #[m!"passes the axiom `{n}` to a reduction"]
    return #[]
  | .fvar id =>
    if params.contains id || inner.contains id then return #[]
    if ← carriesFunction {} (← inferType e) then
      let name := (← id.getDecl).userName
      return #[m!"passes `{name}`, which carries a function and is bound inside the proof, to a \
        reduction"]
    return #[]
  | .forallE .. => return #[]
  | .lam .. =>
    lambdaTelescope e fun xs body =>
      argViolations params (xs.foldl (fun s x => s.insert x.fvarId!) inner) body
  | .letE n t v b _ => do
    let vs ← argViolations params inner v
    withLetDecl n t v fun x => do
      return vs ++ (← argViolations params (inner.insert x.fvarId!) (b.instantiate1 x))
  | .app f a => return (← argViolations params inner f) ++ (← argViolations params inner a)
  | .mdata _ b | .proj _ _ b => argViolations params inner b
  | _ => return #[]

mutual

/-- Rules 2 and 3 on a subterm `e` of a theorem's proof. `params` holds the variables bound by the
statement, and `related` the constants whose type mentions a reduction. -/
partial def proofViolations (params : FVarIdSet) (related : NameSet) (e : Expr) :
    MetaM (Array MessageData) := do
  match e with
  | .lam .. => lambdaTelescope e fun _ body => proofViolations params related body
  | .letE n t v b _ => do
    let vs ← proofViolations params related v
    withLetDecl n t v fun x => return vs ++ (← proofViolations params related (b.instantiate1 x))
  | .app .. => appViolations params related e
  | .const n _ =>
    return if reductionCtors.contains n then #[m!"builds a reduction with `{n}`"] else #[]
  | .mdata _ b | .proj _ _ b => proofViolations params related b
  | _ => return #[]

/-- Rules 2 and 3 on an application `e` inside a theorem's proof. -/
partial def appViolations (params : FVarIdSet) (related : NameSet) (e : Expr) :
    MetaM (Array MessageData) := do
  let args := e.getAppArgs
  let mut out := #[]
  match e.getAppFn with
  | .const n _ =>
    if reductionCtors.contains n then out := out.push m!"builds a reduction with `{n}`"
    if related.contains n then
      for a in args do out := out ++ (← argViolations params {} a)
  | f => out := out ++ (← proofViolations params related f)
  for a in args do out := out ++ (← proofViolations params related a)
  return out

end

/-- The violations of the theorem with proof `value`. -/
def theoremViolations (related : NameSet) (value : Expr) : MetaM (Array MessageData) :=
  lambdaTelescope value fun xs body =>
    proofViolations (xs.foldl (fun s x => s.insert x.fvarId!) {}) related body

/-- The violations of the declaration `c`. -/
def declViolations (env : Environment) (related : NameSet) (c : Name) (ci : ConstantInfo) :
    MetaM (Array MessageData) := do
  if !ci.isTheorem && mentionsAny reductionStructSet (conclusion ci.type) && !isReductionType ci.type
  then
    return #[m!"returns a reduction inside another type"]
  match ci with
  | .defnInfo d =>
    if !(isReductionType d.type || mentionsAny reductionCtors d.value) then return #[]
    if d.safety != .safe then return #[m!"builds a reduction but is not safe"]
    return match compiledViolation env c with
      | some why => #[m!"builds a reduction but {why}"]
      | none => #[]
  | .opaqueInfo o =>
    return if isReductionType o.type then #[m!"is an opaque or partial reduction"] else #[]
  | .axiomInfo a =>
    return if mentionsAny reductionStructSet a.type then #[m!"is an axiom about reductions"] else #[]
  | .thmInfo t =>
    if !mentionsAny (related.union reductionCtors) t.value then return #[]
    try theoremViolations related t.value
    catch ex => return #[m!"could not be checked: {ex.toMessageData}"]
  | _ => return #[]

/-- The constants whose type mentions a reduction. -/
def relatedConstants (env : Environment) : NameSet :=
  env.constants.fold
    (fun s n ci => if mentionsAny reductionStructSet ci.type then s.insert n else s) {}

/-- `#check_reductions` checks the rules of the module docstring over every declaration of a
`DiagonaLean` module, and `#check_reductions local` over the declarations of the current file. -/
syntax (name := checkReductions) "#check_reductions" ("local")? : command

/-- The elaborator of `#check_reductions`. -/
@[command_elab checkReductions]
def elabCheckReductions : CommandElab := fun stx => do
  let onlyLocal := !stx[1].isNone
  let env ← getEnv
  for n in reductionStructs do
    if !onlyLocal && !env.contains n then
      throwError "#check_reductions: `{n}` is not in the environment; update `reductionStructs`"
  let related := relatedConstants env
  let decls := env.constants.fold (fun acc n ci =>
    if inScope env onlyLocal n && !isStructureAPI n && !n.isInternalDetail then acc.push (n, ci)
    else acc) #[]
  let mut failures := 0
  for (c, ci) in decls.qsort (fun a b => a.1.lt b.1) do
    let issues ← liftTermElabM (declViolations env related c ci)
    for msg in issues do
      logError m!"`{c}` {msg}"
      failures := failures + 1
  if failures == 0 then
    logInfo m!"#check_reductions: {decls.size} declarations checked, no violations"

end DiagonaLean.Synthetic.ReductionCheck
