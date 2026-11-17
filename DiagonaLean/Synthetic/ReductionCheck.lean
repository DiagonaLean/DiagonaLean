/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus
-/

import Lean

/-! # Checking that reductions are computed by compiled definitions

`Undecidable p` is the type `HaltProblem ⪯ₘ p`, and Lean's logic is classical, so a term of it exists
for every `p` with a positive and a negative instance: the reduction can be the case split
`fun x => if HaltProblem x then a else b`. A reduction carries algorithmic content only when its
function is a program. Lean refuses to compile that case split, so an undecidability result is a
definition whose value is the reduction, and what has to be checked is that the definition
compiles and that its compiled code is its logical meaning. `#check_reductions` checks this over
every declaration of a `DiagonaLean` module (with `local`, over the declarations of the current
file instead), private ones included.

A reduction is a term of `ManyOneReduces`. A *carrier* is a reduction structure or a
definition of a type or a proposition that unfolds to one, such as `Undecidable`.

1. **Every reduction is a compiled definition with honest proofs.** A definition whose type ends in a
   carrier is safe, not `noncomputable`, without `implemented_by` or `extern`, and has compiled
   code. Its dependencies are free of escape hatches (see below). Its proofs, and the theorems they
   use, depend on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`: not `sorry`, not
   an `axiom` of the library, and not `native_decide`, whose proofs trust compiled code that an
   escape hatch can make lie. Likewise every `@[csimp]` lemma, since it replaces the compiled code of
   a definition and a false one makes a classical definition compile.
2. **Reductions are not wrapped.** A definition returns a reduction only as its result, never
   inside another type such as an `Equiv` or a pair, and no constructor of a structure, inductive
   type or inductive proposition takes one. Otherwise a reduction could be passed around inside a
   value that rule 1 does not see.
3. **No proposition claims that a reduction exists.** The statement of a theorem may take
   reductions as hypotheses, but after them it does not mention a carrier: `Nonempty (p ⪯ₘ q)` or
   `∃ r : p ⪯ₘ q, …` holds classically and says nothing. No axiom or `opaque` declaration mentions a
   carrier at all.

Proofs are not checked: a proof cannot produce a reduction that a definition then uses, since
extracting data from a proposition (`Classical.choice`) is not compiled, so rule 1 rejects any
definition that does it.

## Escape hatches

Compiling a definition does not show that its logical meaning is a program. `@[implemented_by g]`
and `@[extern]` replace a definition's code without any check that the code agrees with the logical
body, and `opaque`, `partial` and `unsafe` definitions have no logical body to compare against. So a
definition with `@[implemented_by stub]` and a classical body, such as `decide (HaltProblem x)`,
gives every definition that calls it compiled code, while logically they decide the halting problem.
Rule 1 therefore walks the dependencies of each reduction: every constant used by a definition's
body, transitively. The walk does not enter theorems, since proofs are erased before compilation,
and stops at constants from the trusted packages (`trustedPrefixes`), whose escape hatches are
taken on trust. The one exception is `sorryAx`: a definition that uses `sorry` compiles, so the walk
reports it although it comes from `Init`.

Declarations that Lean generates are not checked; they are recognised by their kind, not their name
alone, since a user can write `def foo._bar` or `def Nat.succ.bar`.

The check reads the environment and trusts that the kernel checked it. A metaprogram can add a
declaration without the kernel (`debug.skipKernelTC`, or `addDecl` from `unsafe` code), such as a
"proof" of `False` that uses no axiom; neither this check nor `#print axioms` can see that. Rechecking
the compiled library with the kernel, as `lean4checker` does, closes this.

Passing these checks shows that every reduction runs as a Lean program. It does not show that a
Turing machine computes it on encoded inputs; that is the `ComputesReduction` hypothesis of
`not_machineDecidable_of_halt_reduces`.
-/

namespace DiagonaLean.Synthetic.ReductionCheck

open Lean Meta Elab Command

/-- The structures whose terms are reductions. -/
def reductionStructs : List Name :=
  [`DiagonaLean.Synthetic.Definitions.ManyOneReduces]

/-- The reduction structures, as a set. -/
def reductionStructSet : NameSet :=
  reductionStructs.foldl (fun s n => s.insert n) {}

/-- `e` mentions a constant in `s`. -/
def mentionsAny (s : NameSet) (e : Expr) : Bool :=
  (e.find? fun t => match t with
    | .const n _ => s.contains n
    | _ => false).isSome

/-- The body of a term after its leading `λ` binders, its parameters. -/
def lamBody : Expr → Expr
  | .lam _ _ b _ => lamBody b
  | .mdata _ e => lamBody e
  | e => e

/-- The body of a type after its leading `∀` binders. -/
def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | .mdata _ e => conclusion e
  | e => e

/-- `ty` is the type of a reduction, possibly after parameters: its conclusion is headed by a
constant of `carriers`, the reduction structures and the definitions that unfold to one. -/
def isReductionType (carriers : NameSet) (ty : Expr) : Bool :=
  match (conclusion ty).getAppFn with
  | .const n _ => carriers.contains n
  | _ => false

/-- `c` is the `SizeOf` instance of an inductive type `X` (`X._sizeOf_inst`), or the curried form
of a constructor `K` (`K._flat_ctor`), whose body only applies `K`. Lean generates these for every
structure; the checks on the shape keep a user from hiding a reduction under such a name. -/
def isGeneratedForInductive (env : Environment) (c : Name) (ci : ConstantInfo) : Bool :=
  match c, ci with
  | .str X "_sizeOf_inst", .defnInfo _ => (env.find? X matches some (.inductInfo _))
  | .str K "_flat_ctor", .defnInfo d =>
    (env.find? K matches some (.ctorInfo _)) && (lamBody d.value).getAppFn.isConstOf K
  | _, _ => false

/-- `c` is generated by Lean rather than written by the user, and is not checked: the recursors,
`noConfusion` and projections of a structure, matchers such as `foo.match_1`, smart-unfolding
definitions, and theorems with an internal name such as `foo._proof_1` or about a constructor such
as `Foo.mk.injEq`, whose constructor is checked instead. A name alone does not make a definition
auxiliary, since a user can write `def foo._bar` or `def Nat.succ.bar`. Private declarations count as
written by the user, although their names start with `_private`. -/
def isAuxiliary (env : Environment) (c : Name) (ci : ConstantInfo) : Bool :=
  isAuxRecursor env c || isNoConfusion env c || env.isProjectionFn c || Meta.isMatcherCore env c
    || isGeneratedForInductive env c ci
    || (match c with | .str _ s => s.endsWith Meta.smartUnfoldingSuffix | _ => false)
    || (ci matches .thmInfo _ &&
      (((privateToUserName? c).getD c).isInternalDetail
        || (env.find? c.getPrefix matches some (.ctorInfo _))))

/-- `c` is part of the generated API of a reduction structure, such as its constructor or
`ManyOneReduces.mk.injEq`. Definitions in the structure's namespace are checked like any other. -/
def isStructureAPI (c : Name) (ci : ConstantInfo) : Bool :=
  !(ci matches .defnInfo _) && reductionStructs.any (·.isPrefixOf c)

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

/-- Module prefixes whose escape hatches are trusted. -/
def trustedPrefixes : List Name :=
  [`Init, `Std, `Lean, `Batteries, `Mathlib, `Cslib, `Aesop, `Qq, `Plausible, `ProofWidgets,
    `LeanSearchClient, `ImportGraph]

/-- `c` comes from a trusted package. -/
def isTrusted (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx =>
    let m := env.allImportedModuleNames[idx.toNat]?.getD .anonymous
    trustedPrefixes.any (·.isPrefixOf m)
  | none => false

/-- The escape hatch on `c`, if any: a way for its compiled code to differ from its logical
meaning, or for it to have no logical body. `sorryAx` counts, although it is in `Init`. -/
def escapeHatch (env : Environment) (c : Name) : Option String :=
  if c == ``sorryAx then some "is `sorry`"
  else if (Compiler.getImplementedBy? env c).isSome then some "uses `implemented_by`"
  else if isExtern env c then some "uses `extern`"
  else match env.find? c with
    | some (.opaqueInfo _) => some "is `opaque` or `partial`"
    | some (.defnInfo d) => if d.safety != .safe then some "is `unsafe` or `partial`" else none
    | _ => none

/-- The untrusted definitions that reach an untrusted escape hatch through the bodies of untrusted
definitions: every `root` for which `hatchInDeps` can succeed. Computed once, by searching backwards
from the escape hatches, so that `hatchInDeps` walks only from these. -/
def taintedConstants (env : Environment) : NameSet := Id.run do
  let mut users : NameMap (Array Name) := {}
  let mut todo : Array Name := #[``sorryAx]
  for (n, ci) in env.constants.toList do
    if isTrusted env n then continue
    if (escapeHatch env n).isSome then todo := todo.push n
    let .defnInfo d := ci | continue
    for u in d.value.getUsedConstants do
      users := users.insert u ((users.getD u #[]).push n)
  let mut tainted : NameSet := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    for n in users.getD c #[] do
      if !tainted.contains n then
        tainted := tainted.insert n
        todo := todo.push n
  return tainted

/-- The first escape hatch among the dependencies of `root`, other than `root` itself, with the
chain of definitions from `root` that reaches it. Follows the constants used by each definition's
body; does not enter theorems, and stops at trusted constants other than `sorryAx`. `tainted` is
`taintedConstants env`. -/
def hatchInDeps (env : Environment) (tainted : NameSet) (root : Name) :
    Option (List Name × String) := Id.run do
  if !tainted.contains root then return none
  let mut parent : NameMap Name := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut todo : Array Name := #[root]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if isTrusted env c && c != ``sorryAx then continue
    if c != root then
      if let some why := escapeHatch env c then
        let mut path := [c]
        let mut cur := c
        while let some p := parent.find? cur do
          path := p :: path
          cur := p
        return some (path, why)
    let some (.defnInfo d) := env.find? c | continue
    for n in d.value.getUsedConstants do
      if !seen.contains n then
        seen := seen.insert n
        parent := parent.insert n c
        todo := todo.push n
  return none

/-- The axioms a reduction or a `@[csimp]` lemma may depend on: those of classical logic. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms that `c` depends on, through definitions and theorems, other than `allowedAxioms`:
`sorryAx`, the axiom of a `native_decide` proof, or one declared with `axiom`. -/
def badAxioms (c : Name) : CoreM (Array Name) :=
  return (← collectAxioms c).filter (!allowedAxioms.contains ·)

/-- How to name the axiom `a` in a message. -/
def axiomMessage (a : Name) : MessageData :=
  if a == ``sorryAx then m!"`sorry`" else m!"the axiom `{a}`"

/-- The message for an escape hatch found by `hatchInDeps`. -/
def hatchMessage (path : List Name) (why : String) : MessageData :=
  let chain := " → ".intercalate (path.map toString)
  m!"`{path.getLast!}`, which {why}, via {chain}"

/-- `ty` is a proposition, possibly after parameters. -/
def isPropType (ty : Expr) : MetaM Bool := do
  try forallTelescopeReducing ty fun _ body => isProp body catch _ => pure false

/-- Rule 3 on the statement `ty` of a proposition: after its hypotheses, it mentions no carrier. -/
def statementViolations (carriers : NameSet) (ty : Expr) : Array MessageData :=
  if mentionsAny carriers (conclusion ty) then
    #[m!"states a proposition about a reduction; state the result as a definition whose value is \
      the reduction"]
  else #[]

/-- The violations of the declaration `c`. `tainted` is `taintedConstants env` and `carriers` is
`reductionCarriers env`. -/
def declViolations (env : Environment) (tainted carriers : NameSet) (c : Name) (ci : ConstantInfo) :
    MetaM (Array MessageData) := do
  match ci with
  | .thmInfo t => return statementViolations carriers t.type
  | .defnInfo d =>
    if ← isPropType d.type then return statementViolations carriers d.type
    if mentionsAny carriers (conclusion d.type) && !isReductionType carriers d.type then
      return #[m!"returns a reduction inside another type"]
    if !isReductionType carriers d.type then return #[]
    if d.safety != .safe then return #[m!"builds a reduction but is not safe"]
    if let some why := compiledViolation env c then return #[m!"builds a reduction but {why}"]
    if let some (path, why) := hatchInDeps env tainted c then
      return #[m!"builds a reduction that depends on {hatchMessage path why}"]
    return (← badAxioms c).map fun a => m!"builds a reduction that depends on {axiomMessage a}"
  | .opaqueInfo o =>
    return if mentionsAny carriers o.type then #[m!"is an opaque or partial declaration about \
      reductions"] else #[]
  | .axiomInfo a =>
    return if mentionsAny carriers a.type then #[m!"is an axiom about reductions"] else #[]
  | .ctorInfo k =>
    return if mentionsAny carriers k.type then #[m!"stores a reduction inside another type"] else #[]
  | _ => return #[]

/-- The reduction structures, and every untrusted definition of a type or a proposition whose body
mentions one of them, directly or through another such definition, such as `Undecidable`. Only the body after the parameters counts, so a predicate on reductions, such
as `fun r : p ⪯ₘ q => Computable r.f`, is not a carrier. Definitions of terms, such as a reduction
itself, are not carriers. -/
def reductionCarriers (env : Environment) : NameSet := Id.run do
  let candidates := env.constants.fold (fun acc n ci =>
    match ci with
    | .defnInfo d =>
      if isTrusted env n || !(conclusion d.type).isSort then acc else acc.push (n, lamBody d.value)
    | _ => acc) #[]
  let mut carriers := reductionStructSet
  let mut changed := true
  while changed do
    changed := false
    for (n, v) in candidates do
      if !carriers.contains n && mentionsAny carriers v then
        carriers := carriers.insert n
        changed := true
  return carriers

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
  let carriers := reductionCarriers env
  let tainted := taintedConstants env
  let decls := env.constants.fold (fun acc n ci =>
    if inScope env onlyLocal n && !isStructureAPI n ci && !isAuxiliary env n ci then
      acc.push (n, ci)
    else acc) #[]
  let mut failures := 0
  let userName (c : Name) := (privateToUserName? c).getD c
  for (c, ci) in decls.qsort (fun a b => (userName a.1).lt (userName b.1)) do
    for msg in ← liftTermElabM (declViolations env tainted carriers c ci) do
      logError m!"`{userName c}` {msg}"
      failures := failures + 1
  -- a `@[csimp]` lemma replaces the compiled code of a definition; it must be a real proof
  for (_, e) in (Compiler.CSimp.ext.getState env).map.toList do
    if !inScope env onlyLocal e.thmName then continue
    for a in ← liftCoreM (badAxioms e.thmName) do
      logError m!"`{userName e.thmName}` is a `@[csimp]` lemma that depends on {axiomMessage a}, \
        so the compiled code of `{userName e.fromDeclName}` may differ from its meaning"
      failures := failures + 1
  if failures == 0 then
    logInfo m!"#check_reductions: {decls.size} declarations checked, no violations"

end DiagonaLean.Synthetic.ReductionCheck
