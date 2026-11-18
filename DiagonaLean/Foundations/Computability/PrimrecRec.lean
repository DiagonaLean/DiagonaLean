/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.Prim

@[expose] public section

/-! # Primitive recursion from equations

A function given by the equations of a recursion on `ℕ` or on lists is primitive recursive when
its base case and its step are. The lemmas take the equations as hypotheses, so they apply to any
definition, whatever Lean compiled it to:

* `primrec_of_nat_eqns`, `primrec₂_of_nat_eqns`: `f 0 = z`, `f (n + 1) = s n (f n)`, without and
  with a parameter;
* `primrec_of_list_eqns`, `primrec₂_of_list_eqns`: `f [] = z`, `f (b :: l) = s b l (f l)`,
  without and with a parameter;
* `primrec₂_of_nat_cov_eqns`: course-of-values recursion, `f (n + 1) = s n [f 0, …, f n]`.

## The tactic `primrec_rec`

It proves `Primrec f`, `Primrec₂ f`, or `Primrec₂ fun (p : _ × _ × …) x => f p.1 p.2.1 … x` for a
definition `f` that recurses on its last argument, with any number of parameters before it
(packed into a product when there are two or more). It reads `f`'s equation lemmas and:

* for the structural recursion `f 0`, `f (n + 1)` calling `f n` (or `f []`, `f (b :: l)` calling
  `f l`), takes `z` from the base case and `s` from the step by abstracting the recursive call;
* otherwise, on `ℕ`, uses course-of-values recursion. This covers recursive calls on any smaller
  argument (`f (n / 2)`, `f (n - 3)`) and nested patterns (`f 0`, `f 1`, `f (n + 2)`): the step
  decides which equation applies, and looks up every recursive call in the table of earlier
  values. The equations for this table form are proved by case analysis on `n`, with `omega` for
  the bounds;

and closes the remaining `Primrec` goals with `fun_prop`. It fails, with a message, on
overlapping patterns (equation lemmas with hypotheses), nested recursive calls (`f (f n)`), and
recursion on lists other than structural. The result is a plain proof term; the tactic adds no
declarations.

```lean
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

@[fun_prop] theorem primrec_fib : Primrec fib := by primrec_rec
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


/-- A unary function is primitive recursive if it is so with a dummy `Unit` parameter. -/
theorem primrec_of_unit₂ {f : β → σ} (h : Primrec₂ fun (_ : Unit) b => f b) : Primrec f :=
  h.comp (Primrec.const ()) Primrec.id

omit [Primcodable σ] in
/-- Looking up entry `t` of the table of `g` below `n`, for `t < n`. -/
theorem getD_map_range_of_lt {g : ℕ → σ} {t n : ℕ} (d : σ) (h : t < n) :
    ((List.range n).map g).getD t d = g t := by
  simp [List.getD_eq_getElem?_getD, h]

/-- **Course-of-values recursion on `ℕ`, with a parameter.** The step sees the table
`[f a 0, …, f a n]` of all earlier values. -/
theorem primrec₂_of_nat_cov_eqns {f : α → ℕ → σ} (z : α → σ) (s : α → ℕ → List σ → σ)
    (h0 : ∀ a, f a 0 = z a) (hs : ∀ a n, f a (n + 1) = s a n ((List.range (n + 1)).map (f a)))
    (hz : Primrec z) (hsp : Primrec fun p : α × (ℕ × List σ) => s p.1 p.2.1 p.2.2) :
    Primrec₂ f := by
  refine Primrec.nat_strong_rec f
    (g := fun a L => some (if L.length = 0 then z a else s a (L.length - 1) L)) ?_ ?_
  · have hs' : Primrec fun q : α × List σ => s q.1 (q.2.length - 1) q.2 :=
      hsp.comp (Primrec.fst.pair
        ((prim_sub (prim_length Primrec.snd) (Primrec.const 1)).pair Primrec.snd))
    exact Primrec.option_some.comp
      (prim_ite (pred_eq (prim_length Primrec.snd) (Primrec.const 0)) (hz.comp Primrec.fst) hs')
  · intro a n
    cases n with
    | zero => simp [h0]
    | succ n => simp [hs]

/-- A function is primitive recursive if it is so paired with its argument; `primrec_rec` uses
this for paramorphisms, where a right-hand side also uses the subterms themselves. -/
theorem primrec₂_of_pair {T : Type*} [Primcodable T] {f : α → T → σ}
    (h : Primrec₂ fun p t => (t, f p t)) : Primrec₂ f :=
  Primrec.snd.comp h

/-! ### The tactic -/

open Lean Meta Elab Tactic

/-- A pattern on `ℕ` in an equation lemma: the literal `c`, or a variable plus `k`. -/
private inductive NatPat where
  | lit (c : ℕ)
  | var (k : ℕ)
  deriving Inhabited

/-- Reads a pattern on `ℕ`: `Nat.succ` applied `k` times to a variable or to a literal. Also
returns the variable, which is only meaningful in the caller's local context. -/
private partial def natPat (e : Expr) : MetaM (NatPat × Option Expr) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``Nat.succ 1 then
    return match ← natPat e.appArg! with
      | (.lit c, x) => (.lit (c + 1), x)
      | (.var k, x) => (.var (k + 1), x)
  if e.isFVar then return (.var 0, some e)
  match ← evalNat e with
  | some c => return (.lit c, none)
  | none => throwError "primrec_rec: unsupported pattern `{e}`"

/-- The parameters `p.1`, `p.2.1`, …, `p.2…2` of a packed parameter `p`, for `k` parameters. -/
private def projs (p : Expr) : ℕ → MetaM (Array Expr)
  | 0 => pure #[]
  | 1 => pure #[p]
  | k + 1 => do
    let rest ← projs (← mkAppM ``Prod.snd #[p]) k
    return #[← mkAppM ``Prod.fst #[p]] ++ rest

/-- The product `T₁ × (T₂ × …)` of the parameter types, or `Unit` without parameters. -/
private def packType : List Expr → MetaM Expr
  | [] => pure (mkConst ``Unit)
  | [t] => pure t
  | t :: ts => do mkAppM ``Prod #[t, ← packType ts]

/-- The fixed leading arguments of the definition: its implicit and instance arguments (such as the
`α` of `hashL {α}`), with its universe levels. They are the same in every equation and every
recursive call, so equation lemmas are instantiated with them before anything else. -/
private structure Fixed where
  /-- The universe levels. -/
  lvls : List Level
  /-- The fixed arguments. -/
  args : Array Expr

/-- Equation lemma `e`, applied to the fixed arguments. -/
private def Fixed.eqn (fx : Fixed) (e : Name) : Expr := mkAppN (mkConst e fx.lvls) fx.args

/-- The type of `fx.eqn e`. -/
private def Fixed.eqnType (fx : Fixed) (e : Name) : MetaM Expr := do
  instantiateForall (← inferType (mkConst e fx.lvls)) fx.args

/-- `t` is a recursive call of `fn` with the fixed arguments, the parameters `ps` and some last
argument. -/
private def isRecCall (fn : Name) (fx : Fixed) (ps : Array Expr) (t : Expr) : Bool :=
  t.isAppOfArity fn (fx.args.size + ps.size + 1) &&
    t.getAppArgs[:fx.args.size].toArray == fx.args &&
    t.getAppArgs[fx.args.size:fx.args.size + ps.size].toArray == ps

/-- Runs `k` on the parts of equation lemma `e` for a function with `n` parameters: its binders,
parameters, pattern and right-hand side. These are only valid inside `k`. -/
private def withEqn {β : Type} (fx : Fixed) (e : Name) (n : ℕ)
    (k : Array Expr → Array Expr → Expr → Expr → MetaM β) : MetaM β := do
  forallTelescopeReducing (← fx.eqnType e) fun xs body => do
    unless (← xs.allM fun x => return !(← isProp (← inferType x))) do
      throwError "primrec_rec: `{e}` has hypotheses (overlapping patterns are not supported)"
    let some (_, lhs, rhs) := body.eq? | throwError "primrec_rec: `{e}` is not an equation"
    let args := lhs.getAppArgs[fx.args.size:].toArray
    unless args.size == n + 1 do throwError "primrec_rec: unexpected equation `{body}`"
    let params := args[:n].toArray
    unless params.all (·.isFVar) do throwError "primrec_rec: unsupported parameters in `{e}`"
    k xs params args[n]! rhs

/-- `fun a ys => e (projs a) ys`: equation lemma `e`, restated over the packed parameter `a`. -/
private def eqnOverPack (fx : Fixed) (e : Name) (P : Expr) (n : ℕ) : MetaM Expr :=
  withLocalDeclD `a P fun a => do
    let pa ← projs a n
    let ty ← instantiateForall (← fx.eqnType e) pa
    forallTelescopeReducing ty fun ys _ =>
      mkLambdaFVars (#[a] ++ ys) (mkAppN (fx.eqn e) (pa ++ ys))

/-- Applies the lemma `lemName` to `goal`, with `assign` giving the values of named arguments;
returns the arguments that remain open. -/
private def applyLemma (goal : MVarId) (lemName : Name) (assign : List (Name × Expr)) :
    MetaM (Array MVarId) := do
  let lem ← mkConstWithFreshMVarLevels lemName
  let (mvs, bis, concl) ← forallMetaTelescopeReducing (← inferType lem)
  unless ← isDefEq concl (← goal.getType) do
    throwError "primrec_rec: could not match `{lemName}` with the goal"
  let names ← forallTelescopeReducing (← inferType lem) fun xs _ =>
    xs.mapM fun x => x.fvarId!.getUserName
  for (n, v) in assign do
    let some i := names.findIdx? (· == n) | throwError "primrec_rec: internal error ({n})"
    unless ← isDefEq mvs[i]! v do
      throwError "primrec_rec: `{n}` does not fit: {v} : {← inferType v}"
  for mv in mvs, bi in bis do
    if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
      let inst ← synthInstance (← inferType mv)
      unless ← isDefEq mv inst do
        throwError "primrec_rec: could not synthesize `{← inferType mv}`"
  goal.assign (mkAppN lem mvs)
  let open_ ← mvs.filterM fun mv => return !(← mv.mvarId!.isAssigned)
  return open_.map Expr.mvarId!

/-- `primrec_rec` proves `Primrec f` or `Primrec₂ f` for a recursion `f` on `ℕ` or on lists;
see the module docstring. -/
elab (name := primrecRec) "primrec_rec" : tactic => withMainContext do
  let goal ← getMainGoal
  let tgt ← whnfR (← instantiateMVars (← goal.getType))
  let (two, F) ←
    if tgt.isAppOfArity ``Primrec 5 then pure (false, tgt.appArg!)
    else if tgt.isAppOfArity ``Primrec₂ 7 then pure (true, tgt.appArg!)
    else throwError "primrec_rec: the goal is not `Primrec f` or `Primrec₂ f`"
  -- the definition: the head of `F` (`f`, `@f α`, or `fun p x => @f α p.1 … x`)
  let head ← lambdaTelescope F fun _ body => pure body
  let .const fn lvls := head.getAppFn
    | throwError "primrec_rec: `{F}` is not a definition applied to its arguments"
  let some eqns ← getEqnsFor? fn
    | throwError "primrec_rec: `{fn}` has no equation lemmas"
  -- its leading implicit and instance arguments are fixed
  let nf ← forallTelescopeReducing (← inferType (mkConst fn lvls)) fun xs _ => do
    let mut i := 0
    for x in xs do
      if (← x.fvarId!.getBinderInfo).isExplicit then break
      i := i + 1
    pure i
  unless head.getAppNumArgs ≥ nf do
    throwError "primrec_rec: `{F}` does not fix the implicit arguments of `{fn}`"
  let fx : Fixed := { lvls, args := head.getAppArgs[:nf].toArray }
  if (fx.args.any fun a => a.hasLooseBVars) then
    throwError "primrec_rec: the implicit arguments of `{fn}` depend on the parameters"
  let fnE := mkAppN (mkConst fn lvls) fx.args
  -- the number of parameters, their types, and the type recursed on
  let (k, paramTys, recTy) ←
    forallTelescopeReducing (← fx.eqnType eqns[0]!) fun _ body => do
      let some (_, lhs, _) := body.eq? | throwError "primrec_rec: `{eqns[0]!}` is not an equation"
      let args := lhs.getAppArgs[nf:].toArray
      let tys ← args[:args.size - 1].toArray.mapM fun x => inferType x
      pure (args.size - 1, tys.toList, ← whnfR (← inferType args.back!))
  if !two && k != 0 then
    throwError "primrec_rec: `{fn}` has parameters; state the goal as `Primrec₂ …`"
  if two && k == 0 then throwError "primrec_rec: `{fn}` has no parameter; state `Primrec {fn}`"
  if two && k ≥ 2 && !F.isLambda then
    throwError "primrec_rec: `{fn}` has {k} parameters; state the goal with them packed, as \
      `Primrec₂ fun (p : _ × _) x => {fn} p.1 p.2 x`"
  let P ← packType paramTys
  -- the goal in the form `Primrec₂ F₂`, over the packed parameter
  let (goal₂, F₂) ← if two then pure (goal, F) else do
    let F₂ ← withLocalDeclD `u P fun u => do mkLambdaFVars #[u] F
    let g₂ ← mkFreshExprMVar (← mkAppM ``Primrec₂ #[F₂])
    goal.assign (← mkAppM ``primrec_of_unit₂ #[g₂])
    pure (g₂.mvarId!, F₂)
  let finish (rest : Array MVarId) : TacticM Unit := do
    for g in rest do
      setGoals [g]
      evalTactic (← `(tactic| fun_prop))
    setGoals []
  -- `z`: the right-hand side of equation `i`, over the packed parameter
  let mkZ (i : ℕ) : MetaM Expr := withLocalDeclD `a P fun a => do
    let pa ← projs a k
    withEqn fx eqns[i]! k fun _ ps _ rhs => do
      if (rhs.find? (·.isConstOf fn)).isSome then
        throwError "primrec_rec: the base case of `{fn}` is recursive"
      mkLambdaFVars #[a] (rhs.replaceFVars ps pa)
  if recTy.isAppOfArity ``List 1 then
    -- structural recursion on lists
    unless eqns.size == 2 do throwError "primrec_rec: `{fn}` needs exactly two equations"
    let z ← mkZ 0
    let s ← withLocalDeclD `a P fun a => do
      let pa ← projs a k
      withEqn fx eqns[1]! k fun _ ps pat rhs => do
        unless pat.isAppOfArity ``List.cons 3 do
          throwError "primrec_rec: `{fn}` does not recurse on `[]` and `b :: l`"
        let (b, l) := (pat.appFn!.appArg!, pat.appArg!)
        let abst ← kabstract rhs (mkAppN fnE (ps.push l))
        if (abst.find? (·.isConstOf fn)).isSome then
          throwError "primrec_rec: `{fn}` calls itself on something other than the tail"
        withLocalDeclD `r (← inferType rhs) fun r =>
          mkLambdaFVars #[a, b, l, r] ((abst.instantiate1 r).replaceFVars ps pa)
    let rest ← applyLemma goal₂ ``primrec₂_of_list_eqns [(`f, F₂), (`z, z), (`s, s),
      (`h0, ← eqnOverPack fx eqns[0]! P k), (`hs, ← eqnOverPack fx eqns[1]! P k)]
    finish rest
    return
  unless recTy.isConstOf ``Nat do
    -- structural recursion on an inductive type `T` with a lemma `T.primrec_of_eqns`
    let .const tName _ := recTy.getAppFn
      | throwError "primrec_rec: `{fn}` does not recurse on `ℕ`, a list or an inductive type"
    let lemName := tName ++ `primrec_of_eqns
    unless (← getEnv).contains lemName do
      throwError "primrec_rec: `{fn}` recurses on `{tName}`, which has no lemma `{lemName}`"
    -- the equation lemma of each constructor
    let mut byCtor : Std.HashMap Name Name := {}
    for e in eqns do
      let c ← withEqn fx e k fun _ _ pat _ => do
        let .const c _ := pat.getAppFn
          | throwError "primrec_rec: the equation `{e}` does not match a constructor"
        pure c
      byCtor := byCtor.insert c e
    -- a paramorphism: some right-hand side uses a subterm outside a recursive call
    let para ← eqns.anyM fun e => withEqn fx e k fun _ ps pat rhs => do
      let fields := pat.getAppArgs.filter (·.isFVar)
      let recFields ← fields.filterM fun x => do isDefEq (← inferType x) recTy
      let rhs' ← Meta.transform rhs (pre := fun t => do
        if isRecCall fn fx ps t then
          return .done (mkConst ``Unit.unit)
        return .continue)
      return recFields.any fun r => (rhs'.find? (· == r)).isSome
    -- for a paramorphism, prove the pair `(t, f p t)` primitive recursive instead
    let σ₀ ← withEqn fx eqns[0]! k fun _ _ _ rhs => inferType rhs
    let goal₃ ← if !para then pure goal₂ else do
      let F₃ ← withLocalDeclD `a P fun a => withLocalDeclD `t recTy fun t => do
        mkLambdaFVars #[a, t] (← mkAppM ``Prod.mk #[t, (mkApp2 F₂ a t).headBeta])
      let g₃ ← mkFreshExprMVar (← mkAppM ``Primrec₂ #[F₃])
      let br ← mkConstWithFreshMVarLevels ``primrec₂_of_pair
      let (bmvs, bbis, bconcl) ← forallMetaTelescopeReducing (← inferType br)
      unless ← isDefEq bconcl (← goal₂.getType) do
        throwError "primrec_rec: internal error (paramorphism)"
      for mv in bmvs, bi in bbis do
        if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
          unless ← isDefEq mv (← synthInstance (← inferType mv)) do
            throwError "primrec_rec: could not synthesize `{← inferType mv}`"
      unless ← isDefEq bmvs.back! g₃ do throwError "primrec_rec: internal error (paramorphism)"
      goal₂.assign (mkAppN br bmvs)
      pure g₃.mvarId!
    let lem ← mkConstWithFreshMVarLevels lemName
    let (mvs, bis, concl) ← forallMetaTelescopeReducing (← inferType lem)
    unless ← isDefEq concl (← goal₃.getType) do
      throwError "primrec_rec: could not match `{lemName}` with the goal"
    for mv in mvs, bi in bis do
      if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
        let inst ← synthInstance (← inferType mv)
        unless ← isDefEq mv inst do
          throwError "primrec_rec: could not synthesize `{← inferType mv}`"
    for mv in mvs do
      if ← mv.mvarId!.isAssigned then continue
      let ty ← instantiateMVars (← inferType mv)
      -- an equation hypothesis `∀ p fields, f p (c fields) = ?g p data [f p r, …]`
      let info? ← forallTelescopeReducing ty fun _ body => do
        let some (_, lhs, rhs) := body.eq? | return none
        -- the constructor: the first subterm headed by a constructor of `T` (for a paramorphism
        -- the left-hand side is the pair `(c fields, f p (c fields))`)
        let env ← getEnv
        let isCtor (t : Expr) : Bool := match t.getAppFn with
          | .const n _ => match env.find? n with
            | some (.ctorInfo ci) => ci.induct == tName
            | _ => false
          | _ => false
        let some ct := lhs.find? isCtor | return none
        let .const c _ := ct.getAppFn | return none
        unless rhs.getAppFn.isMVar do return none
        return some (c, rhs.getAppFn)
      let some (c, gmv) := info? | continue
      let some e := byCtor.get? c
        | throwError "primrec_rec: `{fn}` has no equation for the constructor `{c}`"
      -- `g`: the right-hand side over the packed parameter, with recursive calls looked up; for a
      -- paramorphism, the entries are pairs `(subterm, result)`, and `g` also rebuilds the node
      let σ ← if para then mkAppM ``Prod #[recTy, σ₀] else pure σ₀
      let listσ ← mkAppM ``List #[σ]
      let dflt ← mkAppOptM ``Inhabited.default #[σ, none]
      let g ← withLocalDeclD `a P fun a => withLocalDeclD `rs listσ fun rs => do
        let pa ← projs a k
        withEqn fx e k fun _ ps pat rhs => do
          let fields := pat.getAppArgs.filter (·.isFVar)
          let recFields ← fields.filterM fun x => do isDefEq (← inferType x) recTy
          let dataFields ← fields.filterM fun x => return !(recFields.contains x)
          let entry (j : ℕ) : MetaM Expr := mkAppM ``List.getD #[rs, mkNatLit j, dflt]
          let rhs' ← Meta.transform rhs (pre := fun t => do
            if isRecCall fn fx ps t then
              match recFields.idxOf? t.appArg! with
              | some j =>
                return .done (← if para then mkAppM ``Prod.snd #[← entry j] else entry j)
              | none => return .continue
            return .continue)
          if (rhs'.find? (·.isConstOf fn)).isSome then
            throwError "primrec_rec: `{fn}` calls itself on something other than a direct \
              subterm (only structural recursion on `{tName}` is supported)"
          let body ← if !para then pure rhs' else do
            let subs ← (List.range recFields.size).toArray.mapM fun j => do
              mkAppM ``Prod.fst #[← entry j]
            let rhs'' := rhs'.replaceFVars recFields subs
            let node := pat.replaceFVars recFields subs
            mkAppM ``Prod.mk #[node, rhs'']
          mkLambdaFVars (#[a] ++ dataFields ++ #[rs]) (body.replaceFVars ps pa)
      unless ← isDefEq gmv g do
        throwError "primrec_rec: the equation `{e}` does not fit `{lemName}`"
      if para then
        -- prove `(c fields, f p (c fields)) = g p data [(r, f p r), …]` from the equation
        let eqId := mkIdent e
        setGoals [mv.mvarId!]
        evalTactic (← `(tactic| (intros; first
          | (simp only [$eqId:ident, List.getD_cons_zero, List.getD_cons_succ]; done)
          | (simp only [$eqId:ident, List.getD_cons_zero, List.getD_cons_succ]; rfl)
          | simp [$eqId:ident])))
        unless (← getGoals).isEmpty do
          throwError "primrec_rec: could not prove the paired equation for `{e}`"
      else
        unless ← isDefEq mv (← eqnOverPack fx e P k) do
          throwError "primrec_rec: the equation `{e}` does not have the expected form"
    goal₃.assign (mkAppN lem mvs)
    let open_ ← mvs.filterM fun mv => return !(← mv.mvarId!.isAssigned)
    finish (open_.map Expr.mvarId!)
    return
  let pats ← eqns.mapM fun e => withEqn fx e k fun _ _ pat _ => do pure (← natPat pat).1
  -- the structural fast path: `f … 0` and `f … (x + 1)`, calling itself only on `x`
  let structS ← if eqns.size != 2 then pure none else
    match pats[0]!, pats[1]! with
    | .lit 0, .var 1 => withLocalDeclD `a P fun a => do
      let pa ← projs a k
      withEqn fx eqns[1]! k fun _ ps pat rhs => do
        let (_, some x) ← natPat pat | pure none
        let abst ← kabstract rhs (mkAppN fnE (ps.push x))
        if (abst.find? (·.isConstOf fn)).isSome then return none
        withLocalDeclD `r (← inferType rhs) fun r => do
          return some (← mkLambdaFVars #[a, x, r] ((abst.instantiate1 r).replaceFVars ps pa))
    | _, _ => pure none
  if let some s := structS then
    let rest ← applyLemma goal₂ ``primrec₂_of_nat_eqns [(`f, F₂), (`z, ← mkZ 0), (`s, s),
      (`h0, ← eqnOverPack fx eqns[0]! P k), (`hs, ← eqnOverPack fx eqns[1]! P k)]
    finish rest
    return
  -- course-of-values recursion: recursive calls become lookups in the table of earlier values
  let some i0 := pats.findIdx? fun | .lit 0 => true | _ => false
    | throwError "primrec_rec: `{fn}` has no equation for `0`"
  let z ← mkZ i0
  let σ ← withEqn fx eqns[i0]! k fun _ _ _ rhs => inferType rhs
  let listσ ← mkAppM ``List #[σ]
  let s ← withLocalDeclD `a P fun a => withLocalDeclD `n (mkConst ``Nat) fun n =>
      withLocalDeclD `L listσ fun L => do
    let pa ← projs a k
    let za := (mkApp z a).headBeta
    let m ← mkAppM ``HAdd.hAdd #[n, mkNatLit 1]
    -- the value given by equation `i` at `m`, recursive calls looked up in `L`
    let value (i : ℕ) (xval : Expr) : MetaM Expr := withEqn fx eqns[i]! k fun _ ps pat rhs => do
      let rhs' ← Meta.transform rhs (pre := fun e => do
        if isRecCall fn fx ps e then
          return .done (← mkAppM ``List.getD #[L, e.appArg!, za])
        return .continue)
      let rhs' := rhs'.replaceFVars ps pa
      match ← natPat pat with
      | (_, some x) => pure (rhs'.replaceFVar x xval)
      | (_, none) => pure rhs'
    -- the equation that applies at `m`: a literal `c ≥ 1`, or the general pattern
    let mut acc ← match (List.range pats.size).find? fun i =>
        match pats[i]! with | .var _ => true | _ => false with
      | some i => do
        let .var j := pats[i]! | unreachable!
        value i (← mkAppM ``HSub.hSub #[m, mkNatLit j])
      | none => pure za
    for i in (List.range pats.size).reverse do
      if let .lit c := pats[i]! then
        if c ≥ 1 then
          acc ← mkAppM ``ite #[← mkEq m (mkNatLit c), ← value i (mkNatLit 0), acc]
    mkLambdaFVars #[a, n, L] acc
  if (s.find? (·.isConstOf fn)).isSome then
    throwError "primrec_rec: a recursive call of `{fn}` could not be turned into a table lookup \
      (nested recursive calls are not supported)"
  let rest ← applyLemma goal₂ ``primrec₂_of_nat_cov_eqns [(`f, F₂), (`z, z), (`s, s)]
  -- the equations hold for the table form: case analysis on `n`, deep enough for every pattern
  let depth := pats.foldl (fun d p => match p with | .lit c => max d c | .var j => max d j) 0
  let lems ← (eqns.map mkIdent).mapM fun i => `(Parser.Tactic.simpLemma| $i:ident)
  let mut others := #[]
  for g in rest do
    let ty ← instantiateMVars (← g.getType)
    let binders ← forallTelescopeReducing ty fun xs _ => pure xs.size
    if binders == 0 then others := others.push g; continue
    setGoals [g]
    if binders == 1 then
      -- `∀ a, F₂ a 0 = z a`
      evalTactic (← `(tactic| intro a))
    else
      -- `∀ a n, F₂ a (n + 1) = s a n (table)`
      evalTactic (← `(tactic| intro a n))
      for _ in [0:depth] do
        evalTactic (← `(tactic| all_goals (try rcases n with _ | n)))
    -- first turn the table lookups into calls, then unfold the equations
    evalTactic (← `(tactic| all_goals (try simp (disch := omega) only
      [getD_map_range_of_lt, List.length_map, List.length_range])))
    evalTactic (← `(tactic| all_goals (first
      | (simp only [$lems,*]; done)
      | (simp [$lems,*]; done)
      | (simp [$lems,*] <;> omega))))
    unless (← getGoals).isEmpty do
      throwError "primrec_rec: could not prove the equations of `{fn}` for its table form"
  finish others

end DiagonaLean.Foundations.Computability
