/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus
-/

import Lean

@[expose] public section

/-! # Checking that reductions are computed by compiled definitions

`SynthHaltReduction p` (former name `Undecidable p`) is the type `HaltProblem ⪯_s p`, and Lean's
logic is classical, so a term of it exists for every `p` with a positive and a negative instance:
the reduction can be the case split `fun x => if HaltProblem x then a else b`. A reduction carries
algorithmic content only when its function is a program. Lean refuses to compile that case split, so
an undecidability result is a definition whose value is the reduction, and what has to be checked is
that the definition compiles and that its compiled code is its logical meaning. `#check_reductions`
checks this over every declaration of a `DiagonaLean` module (with `local`, over the declarations of
the current file instead), private ones included.

A reduction is a term of `SynthReduction` (`⪯_s`; former name `ManyOneReduces`): a term whose type,
after its parameters and after unfolding every definition, is a reduction structure, listed in
`reductionStructs`. Unfolding matters, since a type can reach a reduction structure through an alias
whose own type is not syntactically a sort, such as
`def T : (fun _ => Type 1) () := SynthHaltReduction p`, or through a field of a structure, such as
`box.T` for `def box : Box := ⟨SynthHaltReduction p⟩`. A *carrier* is a reduction structure or an
untrusted definition, other than a reduction itself, whose body mentions a carrier, such as
`SynthHaltReduction`, `T` or `box`.

1. **Every reduction is a compiled definition with honest proofs.** A definition whose type ends in
   a reduction is safe, not `noncomputable`, without `implemented_by` or `extern`, and has compiled
   code. Its dependencies are free of escape hatches (see below). Its proofs, and the theorems they
   use, depend on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`: not `sorry`, not
   an `axiom` of the library, and not `native_decide`, whose proofs trust compiled code that an
   escape hatch can make lie. Likewise every `@[csimp]` lemma, since it replaces the compiled code
   of a definition and a false one makes a classical definition compile.
2. **Reductions are not wrapped.** A definition returns a reduction only as its result, never
   inside another type such as an `Equiv` or a pair, and no constructor of a structure, inductive
   type or inductive proposition takes one. Otherwise a reduction could be passed around inside a
   value that rule 1 does not see.
3. **No proposition claims that a reduction exists.** A carrier may occur in the statement of a
   theorem only negatively: in a hypothesis, but not in a hypothesis of a hypothesis, since
   `(Nonempty (p ⪯_s q) → False) → False` and `∀ c, (p ⪯_s q → c) → c` claim a reduction as much as
   `Nonempty (p ⪯_s q)`, which holds classically and says nothing. Likewise `∃ f, p ⪯_s[f] q`, the
   relation `⪯_s[f]` with a quantified `f`. So `¬ Nonempty (p ⪯_s q)` may be stated, and
   `¬¬ Nonempty (p ⪯_s q)` may not. No axiom or `opaque` declaration mentions a carrier at all.

Rule 3 is a lint against stating a result the wrong way, not a guarantee: the statement
`∃ f, ∀ x, HaltProblem x ↔ q (f x)`, which writes the relation out, mentions no carrier.

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

Declarations that Lean generates are not checked; they are recognised by their kind and shape, not
their name alone, since a user can write `def foo_sunfold`, `theorem foo._bar` or
`theorem Nat.succ.bar`. Theorems are always checked.

## Metaprograms

The check reads the environment, and a metaprogram can write it. A `run_cmd` can add a classical
reduction with `addDecl`, which the kernel accepts, and then copy the compiled code of an honest
stub into the compiler's tables: the result is safe, not `noncomputable`, and has code, so it passes
the check, and rechecking the library with the kernel, as `lean4checker` does, accepts it too. A
metaprogram can also add a declaration without the kernel (`debug.skipKernelTC`), such as a "proof"
of `False` that uses no axiom, which neither this check nor `#print axioms` can see. So
`scripts/CheckMetaprograms.lean`, run by CI, rejects the commands and functions that change the
environment (`run_cmd`, `#eval`, `addDecl`, `modifyEnv`, …) in the library's sources outside an
allowlist; the tactics that the library defines with `elab` are reviewed by hand.

Passing these checks shows that every reduction runs as a Lean program. It does not show that a
Turing machine computes it on encoded inputs; that is the `ComputesReduction` hypothesis of
`not_machineDecidable_of_halt_reduces`.
-/

namespace DiagonaLean.Synthetic.ReductionCheck

open Lean Meta Elab Command

/-- The structures whose terms are reductions. A new kind of reduction, a structure that bundles a
function with a property it must have, is added here. -/
def reductionStructs : List Name :=
  [`DiagonaLean.Synthetic.Definitions.SynthReduction]

/-- The reduction structures, as a set. -/
def reductionStructSet : NameSet :=
  reductionStructs.foldl (fun s n => s.insert n) {}

/-- The relations `p ⪯_s[f] q` that say a given function is a reduction, with the index of the
function among their arguments. With `f` quantified, they say that a reduction exists. -/
def reductionRelations : List (Name × Nat) :=
  [(`DiagonaLean.Synthetic.Definitions.ReducesVia, 2),
   -- the former name, an alias of `ReducesVia`, until existing uses are renamed
   (`DiagonaLean.Synthetic.Definitions.Reduction, 2)]

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

/-- `ty` is the type of a reduction, possibly after parameters: after unfolding every definition,
its conclusion is a reduction structure. If the type cannot be unfolded, it is treated as one, so
that rule 1 checks it. -/
def isReductionType (ty : Expr) : MetaM Bool :=
  withCurrHeartbeats do
    try
      withTransparency .all <| forallTelescopeReducing ty fun _ body => do
        match (← whnf body).getAppFn with
        | .const n _ => return reductionStructSet.contains n
        | _ => return false
    catch _ => return true

/-- `c` is the `SizeOf` instance of an inductive type `X` (`X._sizeOf_inst`), or the curried form
of a constructor `K` (`K._flat_ctor`), whose body only applies `K`. Lean generates these for every
structure; the checks on the shape keep a user from hiding a reduction under such a name. -/
def isGeneratedForInductive (env : Environment) (c : Name) (ci : ConstantInfo) : Bool :=
  match c, ci with
  | .str X "_sizeOf_inst", .defnInfo d =>
    (env.find? X matches some (.inductInfo _)) && (conclusion d.type).getAppFn.isConstOf ``SizeOf
  | .str K "_flat_ctor", .defnInfo d =>
    (env.find? K matches some (.ctorInfo _)) && (lamBody d.value).getAppFn.isConstOf K
  | _, _ => false

/-- `c` is `f._sunfold`, the smart-unfolding definition Lean generates for a recursive definition
`f`, with the type of `f`. A user's definition of that name and type is harmless: `f` is checked,
and a classical term of a type that `f` already inhabits claims nothing more. -/
def isSmartUnfolding (env : Environment) (c : Name) (ci : ConstantInfo) : Bool :=
  match c, ci with
  | .str f s, .defnInfo d =>
    s == Meta.smartUnfoldingSuffix && match env.find? f with
      | some (.defnInfo fd) => fd.type == d.type && fd.levelParams == d.levelParams
      | _ => false
  | _, _ => false

/-- `c` is generated by Lean rather than written by the user, and is not checked: the recursors,
`noConfusion` and projections of a structure, matchers such as `foo.match_1`, the definitions
recognised by `isGeneratedForInductive` and `isSmartUnfolding`, and theorems with a reserved name,
such as the equation lemma `foo.eq_1` or the congruence lemma `foo.congr_simp`, which Lean derives
from `foo` and forbids users to declare. The recognised names are recorded by Lean in environment
extensions or checked against the declaration's shape, since a user can write `def foo._bar` or
`theorem Nat.succ.bar`. Private declarations count as written by the user, although their names
start with `_private`. -/
def isAuxiliary (env : Environment) (c : Name) (ci : ConstantInfo) : Bool :=
  isAuxRecursor env c || isNoConfusion env c || env.isProjectionFn c || Meta.isMatcherCore env c
    || isGeneratedForInductive env c ci || isSmartUnfolding env c ci
    || (ci matches .thmInfo _ && isReservedName env c)

/-- `K` is the constructor of a reduction structure. -/
def isReductionCtor (env : Environment) (K : Name) : Bool :=
  match env.find? K with
  | some (.ctorInfo k) => reductionStructSet.contains k.induct
  | _ => false

/-- `c` is part of the generated API of a reduction structure that mentions it: the constructor,
and the theorems `mk.injEq`, `mk.inj` and `mk.sizeOf_spec`. Anything else in the structure's
namespace, such as a user's `theorem SynthReduction.foo` or `structure SynthReduction.Bag`, is
checked like any other declaration. -/
def isStructureAPI (env : Environment) (c : Name) (ci : ConstantInfo) : Bool :=
  match c, ci with
  | _, .ctorInfo k => reductionStructSet.contains k.induct
  | .str K s, .thmInfo _ => ["injEq", "inj", "sizeOf_spec"].contains s && isReductionCtor env K
  | _, _ => false

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

/-- `e` applies a relation of `reductionRelations` to a function that depends on a variable bound
inside `e`, as in `∃ f, p ⪯_s[f] q` or `Nonempty {f // p ⪯_s[f] q}`. -/
def quantifiesReductionFn (e : Expr) : Bool :=
  (e.find? fun t => reductionRelations.any fun (rel, i) =>
    t.getAppFn.isConstOf rel && t.getAppNumArgs > i && (t.getArg! i).hasLooseBVars).isSome

/-- `ty` claims that a reduction exists when it occurs with polarity `pos` (true for a statement,
false for a hypothesis): after unfolding its head, a carrier, or a relation of `reductionRelations`
on a quantified function, occurs positively. A hypothesis flips the polarity, so `p ⪯_s q → c` is
fine and `(p ⪯_s q → c) → c` is not. Inside a statement that is not a `∀` or `→`, such as `A ∧ B`,
every occurrence counts as positive. -/
partial def claimsReduction (carriers : NameSet) (ty : Expr) (pos : Bool) : MetaM Bool :=
  forallTelescopeReducing ty fun xs body => do
    for x in xs do
      if ← claimsReduction carriers (← inferType x) !pos then return true
    if !pos then return false
    let body ← whnf body
    return mentionsAny carriers body || quantifiesReductionFn body

/-- Rule 3 on the statement `ty` of a proposition, by `claimsReduction`. If the statement cannot be
unfolded, it may not mention a carrier at all. -/
def statementViolations (carriers : NameSet) (ty : Expr) : MetaM (Array MessageData) := do
  let claims ← withCurrHeartbeats do
    try claimsReduction carriers ty true
    catch _ => pure (mentionsAny carriers ty || quantifiesReductionFn ty)
  return if claims then
    #[m!"states a proposition that a reduction exists; state the result as a definition whose \
      value is the reduction"]
  else #[]

/-- The violations of the declaration `c`. `tainted` is `taintedConstants env` and `carriers` is
`reductionCarriers`. -/
def declViolations (env : Environment) (tainted carriers : NameSet) (c : Name) (ci : ConstantInfo) :
    MetaM (Array MessageData) := do
  match ci with
  | .thmInfo t => statementViolations carriers t.type
  | .defnInfo d =>
    if ← isPropType d.type then return ← statementViolations carriers d.type
    let isReduction ← isReductionType d.type
    if mentionsAny carriers (conclusion d.type) && !isReduction then
      return #[m!"returns a reduction inside another type"]
    if !isReduction then return #[]
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
    return if mentionsAny carriers k.type then #[m!"stores a reduction inside another type"]
      else #[]
  | _ => return #[]

/-- The reduction structures, and every untrusted definition, other than a reduction, whose body
mentions one of them, directly or through another such definition: aliases such as
`SynthHaltReduction`, whatever their declared type, and values that store such a type, such as `box`
in `def box : Box := ⟨SynthHaltReduction p⟩`. Only the body after the parameters counts, so a
predicate on reductions, such as `fun r : p ⪯_s q => Computable r.f`, is not a carrier, and neither
are the definitions Lean generates (`isAuxiliary`), such as the projection `SynthReduction.f`. A
reduction is not a carrier, so that a theorem may state facts about a named one. Computed by
searching backwards from the reduction structures, as `taintedConstants` does. -/
def reductionCarriers : MetaM NameSet := do
  let env ← getEnv
  let mut users : NameMap (Array (Name × Expr)) := {}
  for (n, ci) in env.constants.toList do
    if isTrusted env n || isAuxiliary env n ci then continue
    let .defnInfo d := ci | continue
    for u in (lamBody d.value).getUsedConstants do
      users := users.insert u ((users.getD u #[]).push (n, d.type))
  let mut carriers := reductionStructSet
  let mut todo : Array Name := reductionStructs.toArray
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    for (n, ty) in users.getD c #[] do
      if !carriers.contains n && !(← isReductionType ty) then
        carriers := carriers.insert n
        todo := todo.push n
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
  let carriers ← liftTermElabM reductionCarriers
  let tainted := taintedConstants env
  let decls := env.constants.fold (fun acc n ci =>
    if inScope env onlyLocal n && !isStructureAPI env n ci && !isAuxiliary env n ci then
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
