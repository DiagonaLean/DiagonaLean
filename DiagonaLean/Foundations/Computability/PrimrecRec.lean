/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.Prim

@[expose] public section

/-! # Primitive recursion from equations

A function given by the two equations of a structural recursion on `ℕ` or on lists is primitive
recursive when its base case and its step are. The lemmas take the equations as hypotheses, so they
apply to any definition, whatever Lean compiled it to:

* `primrec_of_nat_eqns`, `primrec₂_of_nat_eqns`: `f 0 = z`, `f (n + 1) = s n (f n)`, without and
  with a parameter;
* `primrec_of_list_eqns`, `primrec₂_of_list_eqns`: `f [] = z`, `f (b :: l) = s b l (f l)`,
  without and with a parameter.

The tactic `primrec_rec` proves `Primrec f` or `Primrec₂ f` for a constant `f` defined by
structural recursion on its last argument, with at most one parameter before it. It reads `f`'s
equation lemmas, takes `z` from the base case and `s` from the step (abstracting the recursive call
`f … n` or `f … l`), applies these lemmas, and closes the remaining `Primrec` goals with `fun_prop`.
It fails, with a message, on other shapes: more than two equations (nested patterns), a recursive
call on anything other than the immediate predecessor or tail (course-of-values recursion), or
more than one parameter. The result is a plain proof term; the tactic adds no declarations.

```lean
def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo n + n

@[fun_prop] theorem primrec_sumTo : Primrec sumTo := by primrec_rec
```
-/

namespace DiagonaLean.Foundations.Computability

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

/-- **Recursion on `ℕ`, with a parameter.** -/
theorem primrec₂_of_nat_eqns {f : α → ℕ → σ} (z : α → σ) (s : α → ℕ → σ → σ)
    (h0 : ∀ a, f a 0 = z a) (hs : ∀ a n, f a (n + 1) = s a n (f a n)) (hz : Primrec z)
    (hsp : Primrec fun p : α × (ℕ × σ) => s p.1 p.2.1 p.2.2) : Primrec₂ f := by
  have h : ∀ a n, f a n = n.rec (motive := fun _ => σ) (z a) fun n IH => s a n IH := by
    intro a n
    induction n with
    | zero => exact h0 a
    | succ n ih => rw [hs, ih]
  exact (Primrec.nat_rec (g := fun a p => s a p.1 p.2) hz hsp).of_eq fun a n => (h a n).symm

/-- **Recursion on `ℕ`.** -/
theorem primrec_of_nat_eqns {f : ℕ → σ} (z : σ) (s : ℕ → σ → σ) (h0 : f 0 = z)
    (hs : ∀ n, f (n + 1) = s n (f n)) (hsp : Primrec fun p : ℕ × σ => s p.1 p.2) : Primrec f :=
  (primrec₂_of_nat_eqns (f := fun (_ : Unit) => f) (fun _ => z) (fun _ => s) (fun _ => h0)
    (fun _ => hs) (Primrec.const z) (hsp.comp Primrec.snd)).comp (Primrec.const ()) Primrec.id

/-- **Recursion on lists, with a parameter.** -/
theorem primrec₂_of_list_eqns {f : α → List β → σ} (z : α → σ) (s : α → β → List β → σ → σ)
    (h0 : ∀ a, f a [] = z a) (hs : ∀ a b l, f a (b :: l) = s a b l (f a l)) (hz : Primrec z)
    (hsp : Primrec fun p : α × (β × (List β × σ)) => s p.1 p.2.1 p.2.2.1 p.2.2.2) :
    Primrec₂ f := by
  have h : ∀ a l, f a l = List.recOn l (z a) fun b l IH => s a b l IH := by
    intro a l
    induction l with
    | nil => exact h0 a
    | cons b l ih => rw [hs, ih]
  have hh : Primrec₂ fun (p : α × List β) (y : β × (List β × σ)) => s p.1 y.1 y.2.1 y.2.2 :=
    hsp.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  exact (Primrec.list_rec Primrec.snd (hz.comp Primrec.fst) hh).of_eq fun p => (h p.1 p.2).symm

/-- **Recursion on lists.** -/
theorem primrec_of_list_eqns {f : List β → σ} (z : σ) (s : β → List β → σ → σ) (h0 : f [] = z)
    (hs : ∀ b l, f (b :: l) = s b l (f l))
    (hsp : Primrec fun p : β × (List β × σ) => s p.1 p.2.1 p.2.2) : Primrec f :=
  (primrec₂_of_list_eqns (f := fun (_ : Unit) => f) (fun _ => z) (fun _ => s) (fun _ => h0)
    (fun _ => hs) (Primrec.const z) (hsp.comp Primrec.snd)).comp (Primrec.const ()) Primrec.id


/-! ### The tactic -/

open Lean Meta Elab Tactic

/-- The kind of structural recursion found in a step equation. -/
private inductive RecKind where
  | nat
  | list

/-- `primrec_rec` proves `Primrec f` or `Primrec₂ f` for a structural recursion `f` on `ℕ` or on
lists; see the module docstring. -/
elab (name := primrecRec) "primrec_rec" : tactic => withMainContext do
  let goal ← getMainGoal
  let tgt ← whnfR (← instantiateMVars (← goal.getType))
  let (two, F) ←
    if tgt.isAppOfArity ``Primrec 5 then pure (false, tgt.appArg!)
    else if tgt.isAppOfArity ``Primrec₂ 7 then pure (true, tgt.appArg!)
    else throwError "primrec_rec: the goal is not `Primrec f` or `Primrec₂ f`"
  let .const fn _ := F
    | throwError "primrec_rec: `{F}` is not a constant; give the definition by name"
  let some eqns ← getEqnsFor? fn
    | throwError "primrec_rec: `{fn}` has no equation lemmas"
  unless eqns.size == 2 do
    throwError "primrec_rec: `{fn}` has {eqns.size} equation lemmas; only a base case and one \
      step are supported"
  let k := if two then 1 else 0
  -- the base case: `z`
  let z ← forallTelescopeReducing (← inferType (mkConst eqns[0]!)) fun xs body => do
    let some (_, lhs, rhs) := body.eq? | throwError "primrec_rec: `{eqns[0]!}` is not an equation"
    unless lhs.getAppNumArgs == k + 1 && xs.size == k do
      throwError "primrec_rec: unexpected base case `{body}`"
    mkLambdaFVars xs rhs
  -- the step: the kind of recursion and `s`
  let (kind, s) ← forallTelescopeReducing (← inferType (mkConst eqns[1]!)) fun xs body => do
    let some (_, lhs, rhs) := body.eq? | throwError "primrec_rec: `{eqns[1]!}` is not an equation"
    let args := lhs.getAppArgs
    unless args.size == k + 1 do throwError "primrec_rec: unexpected step `{body}`"
    let params := args[:k].toArray
    let pat := args[k]!
    let (kind, binders, recArg) ←
      if pat.isAppOfArity ``Nat.succ 1 then pure (RecKind.nat, #[pat.appArg!], pat.appArg!)
      else if pat.isAppOfArity ``List.cons 3 then
        pure (RecKind.list, #[pat.appFn!.appArg!, pat.appArg!], pat.appArg!)
      else throwError "primrec_rec: the step `{body}` does not recurse on `n + 1` or `b :: l`"
    unless (params ++ binders).all (·.isFVar) && params.size + binders.size == xs.size do
      throwError "primrec_rec: unexpected step `{body}`"
    let call := mkAppN F (params.push recArg)
    let abst ← kabstract rhs call
    if (abst.find? (·.isConstOf fn)).isSome then
      throwError "primrec_rec: `{fn}` calls itself on something other than the predecessor or \
        tail (course-of-values recursion is not supported yet)"
    let σ ← inferType rhs
    let body := Expr.lam `r σ abst .default
    pure (kind, ← mkLambdaFVars (params ++ binders) body)
  let lemName := match kind, two with
    | .nat, false => ``primrec_of_nat_eqns
    | .nat, true => ``primrec₂_of_nat_eqns
    | .list, false => ``primrec_of_list_eqns
    | .list, true => ``primrec₂_of_list_eqns
  let lem ← mkConstWithFreshMVarLevels lemName
  let (mvs, bis, concl) ← forallMetaTelescopeReducing (← inferType lem)
  unless ← isDefEq concl (← goal.getType) do
    throwError "primrec_rec: could not match `{lemName}` with the goal"
  let names ← forallTelescopeReducing (← inferType lem) fun xs _ =>
    xs.mapM fun x => x.fvarId!.getUserName
  let get (n : Name) : MetaM Expr := do
    let some i := names.findIdx? (· == n) | throwError "primrec_rec: internal error ({n})"
    pure mvs[i]!
  unless ← isDefEq (← get `z) z do throwError "primrec_rec: base case does not fit"
  unless ← isDefEq (← get `s) s do throwError "primrec_rec: step does not fit"
  unless ← isDefEq (← get `h0) (mkConst eqns[0]!) do
    throwError "primrec_rec: `{eqns[0]!}` does not have the expected form"
  unless ← isDefEq (← get `hs) (mkConst eqns[1]!) do
    throwError "primrec_rec: `{eqns[1]!}` does not have the expected form"
  for mv in mvs, bi in bis do
    if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
      let inst ← synthInstance (← inferType mv)
      unless ← isDefEq mv inst do
        throwError "primrec_rec: could not synthesize `{← inferType mv}`"
  goal.assign (mkAppN lem mvs)
  let open_ ← mvs.filterM fun mv => return !(← mv.mvarId!.isAssigned)
  let rest := open_.map Expr.mvarId!
  setGoals rest.toList
  for g in rest do
    setGoals [g]
    evalTactic (← `(tactic| fun_prop))
  setGoals []

end DiagonaLean.Foundations.Computability
