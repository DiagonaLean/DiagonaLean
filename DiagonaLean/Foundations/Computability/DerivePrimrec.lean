/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.Prim

@[expose] public section

/-! # `derive_primrec`: the `fun_prop` lemma of a definition

`fun_prop` uses a lemma about a function `f` of several arguments when it is stated in uncurried
form, `Primrec fun x : A₁ × A₂ × A₃ => f x.1 x.2.1 x.2.2`, and then proves goals in which `f` is
applied to arbitrary primitive recursive arguments; no compositional lemma
(`Primrec g₁ → Primrec g₂ → Primrec fun x => f (g₁ x) (g₂ x)`) is needed.

`derive_primrec f` states that lemma for a definition `f`, proves it by `unfold f; fun_prop`, and
registers it with `@[fun_prop]`, as `f_prim` in the namespace of `f`. The implicit and instance
arguments of `f` stay arguments of the lemma; extra ones, such as `[Primcodable α]` when `f` only
asks for `[DecidableEq α]`, follow `f`: `derive_primrec f [Primcodable α]`. The explicit arguments
of `f` must not depend on each other. A recursive `f` needs `primrec_rec`, not this command.

The command builds Lean source text and elaborates it with `elabCommand`, so the lemma is
elaborated and checked by the kernel as if written by hand. It changes the environment in no other
way, and the metaprogram check (`Synthetic/MetaprogramCheck.lean`) permits only the definition of
this command here. `#check` shows what it generated.

**Function arguments.** A function is not `Primcodable`, so an explicit argument of function type
`c : A → B`, such as a letterwise code, cannot be a component of the tuple. When `f` has one, the
lemma is stated in compositional form over a parameter type `X`: the function argument becomes a
function of the parameter, `c : X → A → B`, with the hypothesis
`Primrec fun p : X × A => c p.1 p.2` (uncurried, the form `fun_prop` uses for local hypotheses),
and every other explicit argument a function `g : X → T` with `Primrec g`:

```
Primrec fun x : X => f (c x) (g x)
```

`fun_prop` then proves goals in which the function argument depends on the input, such as
`fun P => P.encode (code P)`, layer by layer. A function argument of several arguments, or one
whose argument is itself a function, is not supported.
-/

namespace DiagonaLean.Foundations.Computability.DerivePrimrec

open Lean Elab Command Meta

/-- The type of `e` as source text that parses back, with full names. -/
def typeText (e : Expr) : MetaM String := do
  let s ← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr e)
  return toString s

/-- The projection of argument `i` out of `n` from a right-nested tuple `x`. -/
def projText (x : String) (n i : ℕ) : String :=
  let pre := x ++ String.join (List.replicate i ".2")
  if i + 1 = n then pre else pre ++ ".1"

/-- The binders (as source text, with their braces), the explicit argument types of `f`, the
names of its implicit and instance arguments, the names of its implicit arguments, which the
generated application passes by name so that they need not be inferred, and, for each explicit
argument of function type `A → B`, the texts of `A` and `B`. -/
def readArgs (f : Name) :
    CommandElabM (Array String × Array String × Array String × Array String ×
      Array (Option (String × String))) := do
  let info ← getConstInfo f
  liftTermElabM do
    forallTelescope info.type fun xs _ => do
      let mut binders := #[]
      let mut explicit : Array Expr := #[]
      let mut tys := #[]
      let mut names := #[]
      let mut named := #[]
      let mut fns : Array (Option (String × String)) := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        unless d.binderInfo == .default do names := names.push d.userName.toString
        let ty ← inferType x
        if explicit.any (ty.containsFVar ·.fvarId!) then
          throwError "derive_primrec: the type of the argument `{d.userName}` of `{f}` depends on \
            an earlier explicit argument, which is not supported"
        match d.binderInfo with
        | .default =>
          explicit := explicit.push x
          tys := tys.push (← typeText ty)
          match ty with
          | .forallE _ dom body _ =>
            if dom.isForall then
              throwError "derive_primrec: the function argument `{d.userName}` of `{f}` must have \
                a type `A → B` with `A` not a function type"
            if body.hasLooseBVars || body.isForall then
              throwError "derive_primrec: the function argument `{d.userName}` of `{f}` must have \
                a type `A → B` with `B` not a function type"
            fns := fns.push (some (← typeText dom, ← typeText body))
          | _ => fns := fns.push none
        | .instImplicit => binders := binders.push s!"[{← typeText ty}]"
        | .implicit | .strictImplicit =>
          binders := binders.push s!"\{{d.userName} : {← typeText ty}}"
          named := named.push d.userName.toString
      if tys.isEmpty then
        throwError "derive_primrec: `{f}` has no explicit argument"
      return (binders, tys, names, named, fns)

/-- `stx` with every position replaced by `info`, so that messages about generated code point at
the command that generated it. -/
partial def withInfo (info : SourceInfo) : Syntax → Syntax
  | .node _ k args => .node info k (args.map (withInfo info))
  | .atom _ v => .atom info v
  | .ident _ raw v pre => .ident info raw v pre
  | .missing => .missing

/-- `derive_primrec f` states, proves and registers the uncurried `fun_prop` lemma of `f`; see the
module docstring. Extra binders after `f` are added to the lemma. -/
elab (name := derivePrimrec) "derive_primrec " id:ident extra:(ppSpace bracketedBinder)* :
    command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let (binders, tys, names, named, fns) ← readArgs f
  let n := tys.size
  let x := if names.contains "x" then "x_derive_primrec" else "x"
  let extraText := extra.map fun b => b.raw.reprint.getD ""
  let univs := (← getConstInfo f).levelParams.filter (!(← getScope).levelNames.contains ·)
  let univText := if univs.isEmpty then "" else
    "universe " ++ " ".intercalate (univs.map toString) ++ " in\n"
  let namedText := String.join (named.toList.map fun m => s!"({m} := {m}) ")
  let args := namedText ++ " ".intercalate ((List.range n).map (projText x n))
  let thm := f.appendAfter "_prim"
  let generated := ["X_dp", "x_dp"] ++ (List.range n).flatMap fun i => [s!"g_dp_{i}", s!"hg_dp_{i}"]
  if fns.any Option.isSome then
    if let some m := names.find? (generated.contains ·) then
      throwError "derive_primrec: rename the argument `{m}` of `{f}`; the generated code uses \
        that name"
  let src := if fns.all Option.isNone then univText ++
    s!"/-- `{f}` is primitive recursive (generated by `derive_primrec`). -/\n" ++
    s!"@[fun_prop] theorem _root_.{thm} {" ".intercalate (binders ++ extraText).toList} :\n" ++
    s!"    Primrec fun {x} : {" × ".intercalate (tys.toList.map fun t => s!"({t})")} =>\n" ++
    s!"      {f} {args} := by\n" ++
    s!"  unfold {f}\n  fun_prop"
  else
    -- compositional form over a parameter type, for a function argument
    let gs := (List.range n).map fun i => s!"g_dp_{i}"
    let argBinders := (List.range n).foldl (init := #[]) fun acc i =>
      match fns[i]! with
      | some (dom, cod) => acc.push s!"\{g_dp_{i} : X_dp → ({dom}) → ({cod})}"
          |>.push s!"(hg_dp_{i} : Primrec fun p : X_dp × ({dom}) => g_dp_{i} p.1 p.2)"
      | none => acc.push s!"\{g_dp_{i} : X_dp → ({tys[i]!})}"
          |>.push s!"(hg_dp_{i} : Primrec g_dp_{i})"
    let allBinders :=
      binders ++ extraText ++ #["{X_dp : Type*}", "[Primcodable X_dp]"] ++ argBinders
    let args := namedText ++ " ".intercalate (gs.map fun g => s!"({g} x_dp)")
    univText ++
    s!"/-- `{f}` is primitive recursive (generated by `derive_primrec`). -/\n" ++
    s!"@[fun_prop] theorem _root_.{thm} {" ".intercalate allBinders.toList} :\n" ++
    s!"    Primrec fun x_dp : X_dp => {f} {args} := by\n" ++
    s!"  unfold {f}\n  fun_prop"
  let stx ← match Parser.runParserCategory (← getEnv) `command src with
    | .ok stx => pure stx
    | .error e => throwError "derive_primrec: generated code does not parse: {e}\n{src}"
  elabCommand (withInfo (SourceInfo.fromRef id) stx)

end DiagonaLean.Foundations.Computability.DerivePrimrec
