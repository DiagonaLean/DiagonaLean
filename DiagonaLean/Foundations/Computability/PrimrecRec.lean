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
* on an inductive type `T` with a lemma `T.primrec_of_eqns` (from `derive_primcodable`, or written
  by hand), applies it, with the step of each constructor read off its equation. For a nested `T`
  (a field `xs : List T` or `o : Option T`), the right-hand side may use `xs` through
  `List.map (fun c => … f p c …) xs` and `xs.length`, and `o` through `Option.map`, which become the
  same over the results. Equations that Lean splits by `none` and `some` on an option field are
  put back together with `Option.elim`. A right-hand side that uses the subterms themselves is a
  paramorphism, proved through the pair `(t, f t)`;

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

/-! ### Recursion on `ℕ` with a changing parameter

`f a (n + 1) = s a n (f (h n a) n)`: the recursive call is on `n`, with the parameter changed by
`h`. First compute the parameter each level sees (`paramAt`), by iterating `h` downwards from `a`;
then fold the results back up (`eq_fold_of_param_eqns`). -/

section ParamRec

variable {α σ : Type}

/-- The parameter at depth `i` of a recursion of depth `n` started with `a`. -/
def paramAt (h : ℕ → α → α) (n : ℕ) (a : α) (i : ℕ) : α :=
  ((fun q : ℕ × α => (q.1 + 1, h (n - 1 - q.1) q.2))^[i] (0, a)).2

theorem iter_shift (h : ℕ → α → α) (n : ℕ) (a : α) (i : ℕ) :
    (fun q : ℕ × α => (q.1 + 1, h (n + 1 - 1 - q.1) q.2))^[i + 1] (0, a) =
      ((fun q : ℕ × α => (q.1 + 1, h (n - 1 - q.1) q.2))^[i] (0, h n a)).map (· + 1) id := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp only [Prod.map]
    congr 2
    omega

theorem paramAt_succ (h : ℕ → α → α) (n : ℕ) (a : α) (i : ℕ) :
    paramAt h (n + 1) a (i + 1) = paramAt h n (h n a) i := by
  unfold paramAt; rw [iter_shift]; rfl

theorem eq_fold_of_param_eqns {f : α → ℕ → σ} (z : α → σ) (h : ℕ → α → α) (s : α → ℕ → σ → σ)
    (h0 : ∀ a, f a 0 = z a) (hs : ∀ a n, f a (n + 1) = s a n (f (h n a) n)) (n : ℕ) :
    ∀ a, f a n = (List.range n).foldr (fun i r => s (paramAt h n a i) (n - 1 - i) r)
      (z (paramAt h n a n)) := by
  induction n with
  | zero => intro a; simp [h0, paramAt]
  | succ n ih =>
    intro a
    rw [hs, ih, List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    simp only [paramAt_succ]
    congr 1
    simp only [paramAt, Nat.sub_sub, Nat.add_comm 1, Nat.succ_eq_add_one, Nat.add_sub_add_right]

variable [Primcodable α] [Primcodable σ] in
theorem paramAt_primrec {h : ℕ → α → α} (hh : Primrec fun q : ℕ × α => h q.1 q.2) :
    Primrec fun y : (ℕ × α) × ℕ => paramAt h y.1.1 y.1.2 y.2 := by
  unfold paramAt
  have hstep : Primrec₂ fun (y : (ℕ × α) × ℕ) (q : ℕ × α) => (q.1 + 1, h (y.1.1 - 1 - q.1) q.2) :=
    Primrec₂.mk (prim_pair (prim_add (prim_fst Primrec.snd) (Primrec.const 1))
      (hh.comp (prim_pair (prim_sub (prim_sub (prim_fst (prim_fst Primrec.fst)) (Primrec.const 1))
        (prim_fst Primrec.snd)) (prim_snd Primrec.snd))))
  exact prim_snd (Primrec.nat_iterate Primrec.snd
    (prim_pair (Primrec.const 0) (prim_snd (prim_fst Primrec.id))) hstep)

variable [Primcodable α] [Primcodable σ] in
/-- **Recursion on `ℕ` with a changing parameter**: `f a (n + 1) = s a n (f (h n a) n)`. -/
theorem primrec₂_of_nat_param_eqns {f : α → ℕ → σ} (z : α → σ) (h : ℕ → α → α)
    (s : α → ℕ → σ → σ) (h0 : ∀ a, f a 0 = z a) (hs : ∀ a n, f a (n + 1) = s a n (f (h n a) n))
    (hz : Primrec z) (hh : Primrec fun q : ℕ × α => h q.1 q.2)
    (hsp : Primrec fun q : α × (ℕ × σ) => s q.1 q.2.1 q.2.2) : Primrec₂ f := by
  have hp := paramAt_primrec hh
  have hstep : Primrec fun w : (α × ℕ) × (ℕ × σ) =>
      s (paramAt h w.1.2 w.1.1 w.2.1) (w.1.2 - 1 - w.2.1) w.2.2 :=
    hsp.comp (prim_pair (hp.comp (prim_pair (prim_pair (prim_snd Primrec.fst) (prim_fst Primrec.fst))
      (prim_fst Primrec.snd))) (prim_pair (prim_sub (prim_sub (prim_snd Primrec.fst)
        (Primrec.const 1)) (prim_fst Primrec.snd)) (prim_snd Primrec.snd)))
  have hbase : Primrec fun q : α × ℕ => z (paramAt h q.2 q.1 q.2) :=
    hz.comp (hp.comp (prim_pair (prim_pair Primrec.snd Primrec.fst) Primrec.snd))
  have hfold : Primrec fun q : α × ℕ => (List.range q.2).foldr
      (fun i r => s (paramAt h q.2 q.1 i) (q.2 - 1 - i) r) (z (paramAt h q.2 q.1 q.2)) :=
    prim_foldr (prim_range Primrec.snd) hbase hstep
  exact hfold.of_eq fun q => (eq_fold_of_param_eqns z h s h0 hs q.2 q.1).symm

variable [Primcodable α] [Primcodable σ] in
/-- `primrec₂_of_nat_param_eqns` with the argument recursed on first:
`f (n + 1) a = s a n (f n (h n a))`. -/
theorem primrec₂_of_nat_param_eqns' {f : ℕ → α → σ} (z : α → σ) (h : ℕ → α → α)
    (s : α → ℕ → σ → σ) (h0 : ∀ a, f 0 a = z a) (hs : ∀ n a, f (n + 1) a = s a n (f n (h n a)))
    (hz : Primrec z) (hh : Primrec fun q : ℕ × α => h q.1 q.2)
    (hsp : Primrec fun q : α × (ℕ × σ) => s q.1 q.2.1 q.2.2) : Primrec₂ f :=
  (primrec₂_of_nat_param_eqns (f := fun a n => f n a) z h s h0 (fun a n => hs n a) hz hh
    hsp).swap

end ParamRec

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

/-- The fields of a constructor application `pat`: its arguments after the type's parameters. -/
private def ctorFields (pat : Expr) : MetaM (Array Expr) := do
  let np ← match pat.getAppFn with
    | .const c _ => do
      match (← getEnv).find? c with
      | some (.ctorInfo ci) => pure ci.numParams
      | _ => pure 0
    | _ => pure 0
  return pat.getAppArgs[np:].toArray.filter (·.isFVar)

/-- For a nested inductive type: the step `fun a data res… => rhs` of constructor `ctor`, from its
equations `es`. A recursive call `f p x` on a field `x : T` becomes its result; a list field
`xs : List T` may be used through `List.map (fun c => … f p c …) xs` and `xs.length`, and an
option field `o : Option T` through `Option.map`, which become the same over its results. Lean
splits the equations of a constructor with option fields by `none` and `some y`; the step then
does `Option.elim` on the results of those fields, with the equation that matches in each branch.
For a paramorphism (`para`), the results are pairs `(subterm, result)`: a recursive call becomes
the second component, a subterm the first, a list or option field used otherwise becomes its
results mapped by `Prod.fst`, and the step also rebuilds the node. -/
private def nestedStep (fn : Name) (fx : Fixed) (tName : Name) (recTy listTy σ P : Expr) (k : ℕ)
    (ctor : Name) (es : Array Name) (para : Bool := false) : MetaM Expr := do
  let listσ ← mkAppM ``List #[σ]
  let optσ ← mkAppM ``Option #[σ]
  let optTy ← mkAppM ``Option #[recTy]
  let ci ← getConstInfoCtor ctor
  let ctorTy ← instantiateForall (← instantiateTypeLevelParams ci.toConstantVal recTy.getAppFn.constLevels!)
    recTy.getAppArgs
  forallTelescopeReducing ctorTy fun fieldsC _ => do
  -- 1: a field `T`, 2: a field `List T`, 3: a field `Option T`, 0: data
  let kinds ← fieldsC.mapM fun x => do
    let ty ← inferType x
    if ← isDefEq ty recTy then return 1 else if ← isDefEq ty listTy then return 2
    else if ← isDefEq ty optTy then return 3 else return (0 : ℕ)
  let recPos := (List.range fieldsC.size).filter (kinds[·]! != 0)
  let dataC := ((List.range fieldsC.size).filter (kinds[·]! == 0)).map (fieldsC[·]!)
  withLocalDeclD `a P fun a => do
  let pa ← projs a k
  -- the results on the recursive fields, and a variable for the content of each option
  let rec mkVars (i : ℕ) (vs : Array Expr) (k' : Array Expr → MetaM Expr) : MetaM Expr := do
    if h : i < recPos.length then
      let kd := kinds[recPos[i]]!
      withLocalDeclD ((← fieldsC[recPos[i]]!.fvarId!.getUserName).appendAfter "_r")
        (if kd == 1 then σ else if kd == 2 then listσ else optσ) fun v => mkVars (i + 1) (vs.push v) k'
    else k' vs
  mkVars 0 #[] fun vs => do
  let resAt (pos : ℕ) : Expr := vs[recPos.idxOf pos]!
  let optPos := recPos.filter (kinds[·]! == 3)
  let rec mkRos (i : ℕ) (ros : Array Expr) (k' : Array Expr → MetaM Expr) : MetaM Expr := do
    if h : i < optPos.length then
      withLocalDeclD `ro σ fun r => mkRos (i + 1) (ros.push r) k'
    else k' ros
  mkRos 0 #[] fun ros => do
  let roAt (pos : ℕ) : Expr := ros[optPos.idxOf pos]!
  -- each equation: what it says about each option field (`none`: unsplit), and its right-hand
  -- side over the shared variables
  let mut cases : Array (Array (Option Bool) × Expr) := #[]
  for e in es do
    let c ← withEqn fx e k fun xs ps pat rhs => do
      let args := pat.getAppArgs[ci.numParams:].toArray
      unless args.size == fieldsC.size do throwError "primrec_rec: unexpected pattern in `{e}`"
      let mut spec : Array (Option Bool) := #[]
      -- an equation-local subterm and what replaces it: its result, or an option's content
      let mut subRes : Array (Expr × Expr × Bool) := #[]  -- (variable, result, is it a content)
      let mut renames : Array (Expr × Expr) := #[]
      for pos in List.range args.size do
        let x := args[pos]!
        let kd := kinds[pos]!
        if kd == 0 then
          unless x.isFVar do throwError "primrec_rec: a data field is matched in `{e}`"
          renames := renames.push (x, fieldsC[pos]!)
        else if kd == 3 && !x.isFVar then
          if x.isAppOfArity ``Option.none 1 then spec := spec.push (some false)
          else if x.isAppOfArity ``Option.some 2 && x.appArg!.isFVar then
            spec := spec.push (some true)
            subRes := subRes.push (x.appArg!, roAt pos, true)
          else throwError "primrec_rec: unsupported pattern `{x}` in `{e}`"
        else
          unless x.isFVar do throwError "primrec_rec: unsupported pattern `{x}` in `{e}`"
          if kd == 3 then spec := spec.push none
          subRes := subRes.push (x, resAt pos, false)
      let resOf (x : Expr) : Option (Expr × Bool) := subRes.findSome? fun (y, v, b) =>
        if y == x then some (v, b) else none
      let rhs' ← Meta.transform rhs (pre := fun t => do
        if isRecCall fn fx ps t then
          if let some (v, _) := resOf t.appArg! then
            return .done (← if para then mkAppM ``Prod.snd #[v] else pure v)
        let isMap := t.isAppOfArity ``List.map 4 || t.isAppOfArity ``Option.map 4
        if isMap then
          if let some (R, false) := resOf t.appArg! then
            let F₀ := t.appFn!.appArg!
            let F ← if F₀.isLambda then pure F₀ else etaExpand F₀
            let F' ← lambdaTelescope F fun cs body => do
              let body := body.headBeta
              unless cs.size == 1 do
                throwError "primrec_rec: unexpected `map` over `{t.appArg!}`"
              let c := cs[0]!
              withLocalDeclD `r σ fun r => do
                let body' ← Meta.transform body (pre := fun u => do
                  if isRecCall fn fx ps u && u.appArg! == c then
                    return .done (← if para then mkAppM ``Prod.snd #[r] else pure r)
                  return .continue)
                let body' ← if para then pure (body'.replaceFVar c (← mkAppM ``Prod.fst #[r]))
                  else pure body'
                if body'.containsFVar c.fvarId! then
                  throwError "primrec_rec: the function mapped over `{t.appArg!}` uses its \
                    argument other than through a recursive call of `{fn}`"
                mkLambdaFVars #[r] body'
            if F'.isLambda && F'.bindingBody! == .bvar 0 then return .done R
            return .done (← mkAppM t.getAppFn.constName! #[F', R])
        if t.isAppOfArity ``List.length 2 && !para then
          if let some (R, false) := resOf t.appArg! then return .done (← mkAppM ``List.length #[R])
        return .continue)
      -- for a paramorphism, the subterms themselves, from the pairs
      let rhs' ← if !para then pure rhs' else do
        let subs ← subRes.mapM fun (_, v, isContent) => do
          if isContent then return ← mkAppM ``Prod.fst #[v]
          let kd := kinds[recPos[vs.idxOf v]!]!
          if kd == 1 then mkAppM ``Prod.fst #[v] else
            let fstFn ← withLocalDeclD `r σ fun r => do mkLambdaFVars #[r] (← mkAppM ``Prod.fst #[r])
            mkAppM (if kd == 2 then ``List.map else ``Option.map) #[fstFn, v]
        pure (rhs'.replaceFVars (subRes.map (·.1)) subs)
      for (x, _, _) in subRes do
        if rhs'.containsFVar x.fvarId! then
          throwError "primrec_rec: the equation `{e}` uses the subterm `{x}` other than \
            through recursive calls, `map` and `List.length` (a paramorphism)"
      if (rhs'.find? (·.isConstOf fn)).isSome then
        throwError "primrec_rec: `{fn}` calls itself on something other than a direct \
          subterm (only structural recursion on `{tName}` is supported)"
      let rhs' := (rhs'.replaceFVars (renames.map (·.1)) (renames.map (·.2))).replaceFVars ps pa
      if rhs'.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then
        throwError "primrec_rec: could not express the right-hand side of `{e}` in the step"
      return (spec, rhs')
    cases := cases.push c
  -- the decision on the option fields that some equation splits
  let splitOpts := (List.range optPos.length).filter fun j =>
    cases.any fun (sp, _) => sp[j]!.isSome
  let rec tree (fuel : ℕ) (j : ℕ) (cons : Array (Option Bool)) : MetaM Expr := do
    match fuel with
    | 0 => throwError "primrec_rec: internal error (option split)"
    | fuel + 1 =>
    if h : j < splitOpts.length then
      let jj := splitOpts[j]
      let pos := optPos[jj]!
      let noneB ← tree fuel (j + 1) (cons.set! jj (some false))
      let someB ← tree fuel (j + 1) (cons.set! jj (some true))
      mkAppM ``Option.elim #[resAt pos, noneB, ← mkLambdaFVars #[roAt pos] someB]
    else
      let ok (sp : Array (Option Bool)) : Bool := (List.range sp.size).all fun i =>
        match sp[i]!, cons[i]! with
        | some b, some b' => b == b'
        | _, _ => true
      match cases.find? (fun (sp, _) => ok sp) with
      | some (_, r) => pure r
      | none => throwError "primrec_rec: `{fn}` has no equation for a combination of `none` and \
          `some` in the option fields of `{ctor}`"
  let body ← tree (splitOpts.length + 1) 0 (Array.replicate optPos.length none)
  let body ← if !para then pure body else do
    let node := mkAppN (mkAppN (mkConst ctor recTy.getAppFn.constLevels!) recTy.getAppArgs)
      (← (List.range fieldsC.size).toArray.mapM fun pos => do
        let kd := kinds[pos]!
        if kd == 0 then return fieldsC[pos]!
        let v := resAt pos
        if kd == 1 then mkAppM ``Prod.fst #[v] else
          let fstFn ← withLocalDeclD `r σ fun r => do mkLambdaFVars #[r] (← mkAppM ``Prod.fst #[r])
          mkAppM (if kd == 2 then ``List.map else ``Option.map) #[fstFn, v])
    mkAppM ``Prod.mk #[node, body]
  mkLambdaFVars (#[a] ++ dataC.toArray ++ vs) body

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
  -- recursion on the first of two arguments, the second changing: `f (n + 1) a = … f n (h n a) …`
  let firstRec ← forallTelescopeReducing (← fx.eqnType eqns[0]!) fun _ body => do
    let some (_, lhs, _) := body.eq? | return false
    let args := lhs.getAppArgs[nf:].toArray
    return args.size == 2 && !args[0]!.isFVar && args[1]!.isFVar &&
      (← whnfR (← inferType args[0]!)).isConstOf ``Nat
  if two && firstRec && eqns.size == 2 then
    let parts ← forallTelescopeReducing (← fx.eqnType eqns[0]!) fun _ body => do
      let some (_, lhs, rhs) := body.eq? | throwError "primrec_rec: internal error"
      let a := lhs.appArg!
      unless (← natPat lhs.appFn!.appArg!).1 matches .lit 0 do
        throwError "primrec_rec: `{eqns[0]!}` is not the equation for `0`"
      pure (← mkLambdaFVars #[a] rhs, ← inferType a, ← inferType rhs)
    let (z, _, σ) := parts
    let (h, s) ← forallTelescopeReducing (← fx.eqnType eqns[1]!) fun _ body => do
      let some (_, lhs, rhs) := body.eq? | throwError "primrec_rec: internal error"
      let a := lhs.appArg!
      let (pat, some n) ← natPat lhs.appFn!.appArg!
        | throwError "primrec_rec: `{eqns[1]!}` is not the equation for `n + 1`"
      unless pat matches .var 1 do throwError "primrec_rec: `{eqns[1]!}` is not for `n + 1`"
      -- the recursive call `f n e`, the same in every occurrence
      let some call := rhs.find? fun t => t.isAppOfArity fn (nf + 2)
        | throwError "primrec_rec: `{fn}` does not call itself"
      unless call.appFn!.appArg! == n do
        throwError "primrec_rec: `{fn}` calls itself on something other than `{n}`"
      let e := call.appArg!
      let abst ← kabstract rhs call
      if (abst.find? (·.isConstOf fn)).isSome then
        throwError "primrec_rec: `{fn}` makes recursive calls with different arguments"
      let h ← mkLambdaFVars #[n, a] e
      let s ← withLocalDeclD `r σ fun r => mkLambdaFVars #[a, n, r] (abst.instantiate1 r)
      pure (h, s)
    let rest ← applyLemma goal ``primrec₂_of_nat_param_eqns' [(`f, F), (`z, z), (`h, h), (`s, s)]
    let lems ← (eqns.map mkIdent).mapM fun i => `(Parser.Tactic.simpLemma| $i:ident)
    for g in rest do
      setGoals [g]
      let ty ← instantiateMVars (← g.getType)
      if ty.isAppOf ``Primrec then
        evalTactic (← `(tactic| (beta_reduce; fun_prop)))
      else
        evalTactic (← `(tactic| (intros; first | (simp only [$lems,*]; done) | simp [$lems,*])))
      unless (← getGoals).isEmpty do
        throwError "primrec_rec: could not prove `{ty}`"
    setGoals []
    return
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
    let mut byCtorAll : Std.HashMap Name (Array Name) := {}
    for e in eqns do
      let c ← withEqn fx e k fun _ _ pat _ => do
        let .const c _ := pat.getAppFn
          | throwError "primrec_rec: the equation `{e}` does not match a constructor"
        pure c
      byCtor := byCtor.insert c e
      byCtorAll := byCtorAll.insert c ((byCtorAll.getD c #[]).push e)
    -- a paramorphism: some right-hand side uses a subterm outside a recursive call
    -- a nested type (fields of type `List T`): the step gets the results on each field
    let nested := (← getConstInfoInduct tName).isNested
    let listTy ← mkAppM ``List #[recTy]
    let σ₀ ← withEqn fx eqns[0]! k fun _ _ _ rhs => inferType rhs
    let para ← if nested then byCtorAll.toList.anyM fun (c, es) => do
        try discard <| nestedStep fn fx tName recTy listTy σ₀ P k c es; pure false
        catch _ => pure true
      else eqns.anyM fun e => withEqn fx e k fun _ ps pat rhs => do
      let fields ← ctorFields pat
      let recFields ← fields.filterM fun x => do isDefEq (← inferType x) recTy
      let rhs' ← Meta.transform rhs (pre := fun t => do
        if isRecCall fn fx ps t then
          return .done (mkConst ``Unit.unit)
        return .continue)
      return recFields.any fun r => (rhs'.find? (· == r)).isSome
    -- for a paramorphism, prove the pair `(t, f p t)` primitive recursive instead
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
      let g ← if nested then nestedStep fn fx tName recTy listTy σ P k c (byCtorAll.getD c #[e]) para else
        withLocalDeclD `a P fun a => withLocalDeclD `rs listσ fun rs => do
        let pa ← projs a k
        withEqn fx e k fun _ ps pat rhs => do
          let fields ← ctorFields pat
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
        throwError "primrec_rec: the equation `{e}` does not fit `{lemName}`: \
          `{g} : {← inferType g}` against `{← inferType gmv}`"
      if nested then
        -- prove `f p (c fields) = g p data (f p x) (xs.map (f p)) …` from the equations, by cases
        -- on the option fields
        let es := byCtorAll.getD c #[e]
        let lems ← (es.map mkIdent).mapM fun i => `(Parser.Tactic.simpLemma| $i:ident)
        let ci ← getConstInfoCtor c
        let ctorTy ← instantiateForall
          (← instantiateTypeLevelParams ci.toConstantVal recTy.getAppFn.constLevels!) recTy.getAppArgs
        let optTy ← mkAppM ``Option #[recTy]
        let optIdx ← forallTelescopeReducing ctorTy fun xs _ =>
          (List.range xs.size).filterM fun i => do isDefEq (← inferType xs[i]!) optTy
        let names := (List.range ci.numFields).toArray.map fun i => mkIdent (Name.mkSimple s!"x{i}")
        setGoals [mv.mvarId!]
        evalTactic (← `(tactic| intro p $names*))
        for i in optIdx do
          let nm := names[i]!
          evalTactic (← `(tactic| all_goals cases $nm:ident))
        evalTactic (← `(tactic| all_goals first
          | (simp only [$lems,*, List.map_map, Option.map_map, Function.comp_def,
              List.length_map, Option.map_some, Option.map_none, Option.elim_some,
              Option.elim_none]; done)
          | (simp only [$lems,*, List.map_map, Option.map_map, Function.comp_def,
              List.length_map, Option.map_some, Option.map_none, Option.elim_some,
              Option.elim_none]; rfl)
          | (simp only [$lems,*, List.map_map, Option.map_map, Function.comp_def,
              List.length_map, List.map_id', Option.map_id', Prod.mk.injEq, Option.map_some,
              Option.map_none, Option.elim_some, Option.elim_none]; done)
          | simp [$lems,*, List.map_map, Option.map_map, Function.comp_def]))
        unless (← getGoals).isEmpty do
          throwError "primrec_rec: could not prove the equation for `{e}` in the form of `{lemName}`"
      else if para then
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
