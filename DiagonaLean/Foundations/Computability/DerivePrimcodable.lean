/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.PolyTree

@[expose] public section

/-! # `derive_primcodable`: inductive types as trees

`derive_primcodable T`, for an inductive type `T` whose parameters are types, in any universe (and
which has no indices and is not mutual), whose constructor fields are `T` itself
(applied to its parameters), `List T`, `Option T`, or data of `Primcodable` types, generates (with
`[Primcodable α]` for each parameter `α` where needed) what
`CombinatoryLogic/Primcodable.lean` writes by hand for SKI terms:

* `T.Shape`, the nested sum over the constructors of the tuples of their data fields, and `T.ar`,
  the number of recursive fields of each;
* `T.toTree`, `T.ofTree`, the round trips `T.ofTree_toTree`, `T.toTree_ofTree` and `T.treeEquiv`;
* `instance : Primcodable T`, through the tree (Theorem A);
* `T.toTree_primrec`, `T.ofTree_primrec`, and for each constructor `c` with fields `T.c_primrec`
  and the `fun_prop` lemma `T.prim_c`; for a structure, the `fun_prop` lemma `T.prim_f` of each
  projection `f`;
* `T.primrec_of_eqns`: structural recursion on `T` is primitive recursive, which `primrec_rec`
  uses (Theorem B).

**Nested types.** When some field has type `List T` or `Option T`, `T` is a nested inductive
type, and the shape of a node also records the length of each such list and whether each such
option is `some`, so that every tree is still the tree of a term and Theorems A and B apply
unchanged (`generateNested`). `ofTree` has one case per assignment of `true` and `false` to the
option fields of a constructor. The tree of a term is built by
structural recursion together with `T.toTreeL` on lists of terms, and the round trips are proved
by induction with a second motive for lists. In `T.primrec_of_eqns` the step of a constructor
sees its data and the result on each recursive field: a value for a field of type `T`, a list of
values (`xs.map (f p)`) for a field of type `List T`, an optional value (`o.map (f p)`) for a field
of type `Option T`. The proof cuts the children's results into
these pieces with `chunks`.

The command builds Lean source text and elaborates it with `elabCommand`, so every declaration is
elaborated, checked by the kernel and compiled as if written by hand. It changes the environment
in no other way, and `scripts/check_metaprograms.py` permits only the definition of this command
here. `#print` shows what it generated.
-/

namespace DiagonaLean.Foundations.Computability.DerivePrimcodable

open Lean Elab Command Meta

/-- A constructor field: recursive (of type `T`) or data, with its type as source text. -/
structure Field where
  /-- Whether the field has type `T` or `List T`. -/
  isRec : Bool
  /-- Whether the field has type `List T` (then `isRec` is also set). -/
  isList : Bool := false
  /-- Whether the field has type `Option T` (then `isRec` is also set). -/
  isOpt : Bool := false
  /-- The type, as source text. -/
  ty : String
  deriving Inhabited

/-- A constructor: its full name and fields. -/
structure Ctor where
  /-- The full name. -/
  name : Name
  /-- The fields, in order. -/
  fields : Array Field
  deriving Inhabited

/-- `s₁ op s₂ op …`, right-nested, with `unit` for no entries. -/
def joinR (op unit : String) : List String → String
  | [] => unit
  | [s] => s
  | s :: rest => s!"({s}) {op} ({joinR op unit rest})"

/-- The tuple of `vs`: `()`, `v`, or `(v₁, v₂, …)`. -/
def tuple : List String → String
  | [] => "()"
  | [v] => v
  | vs => "(" ++ ", ".intercalate vs ++ ")"

/-- The projections of a tuple `t` with `k` components. -/
def projs (t : String) (k : ℕ) : List String :=
  if k == 0 then [] else if k == 1 then [t] else
    (List.range k).map fun l =>
      if l + 1 == k then t ++ String.join (List.replicate l ".2")
      else t ++ String.join (List.replicate l ".2") ++ ".1"

/-- `x` injected into summand `i` of a nested sum with `n` summands. -/
def inj (n i : ℕ) (x : String) : String :=
  if n == 1 then x
  else if i + 1 == n then String.join (List.replicate i "Sum.inr (") ++ x ++
    String.join (List.replicate i ")")
  else String.join (List.replicate i "Sum.inr (") ++ "Sum.inl (" ++ x ++ ")" ++
    String.join (List.replicate i ")")

/-- A `Primrec` proof term for the projection `z.i.j…` (each index `1` or `2`) of the variable
`z`, built from `Primrec.fst` and `Primrec.snd` rather than found by `fun_prop`. -/
def projPrim (path : String) : String := Id.run do
  let mut acc := "Primrec.id"
  for seg in (path.splitOn ".").drop 1 do
    acc := s!"({if seg == "1" then "Primrec.fst" else "Primrec.snd"}.comp {acc})"
  return acc

/-- A `Primrec` proof term for a tuple of projections, as `tuple` writes it. -/
def tuplePrim : List String → String
  | [] => "(Primrec.const ())"
  | [v] => projPrim v
  | v :: vs => s!"({projPrim v}.pair {tuplePrim vs})"

/-- The `rcases` pattern of the data tuple of a constructor with `k` data fields. -/
def dataPat (vs : List String) : String :=
  match vs with
  | [] => "⟨⟩"
  | [v] => v
  | vs => "⟨" ++ ", ".intercalate vs ++ "⟩"

/-- Names the generated code uses for its own variables, which a parameter must not take. -/
def reserved : List String :=
  ["P", "σ", "β", "p", "q", "t", "f", "s", "d", "x", "y", "z", "a", "j", "rs", "cs", "hj", "ih",
    "i", "h", "hi", "l", "c", "step"]

/-- Reads the parameters (their names) and the constructors of `T`. -/
def readCtors (T : Name) : CommandElabM (Array (String × String) × Array Ctor) := do
  let env ← getEnv
  let some (.inductInfo ind) := env.find? T | throwError "derive_primcodable: `{T}` is not an inductive type"
  unless ind.numIndices == 0 do
    throwError "derive_primcodable: `{T}` has indices, which are not supported"
  unless ind.all.length == 1 do
    throwError "derive_primcodable: `{T}` is mutual, which is not supported"
  liftTermElabM do
    forallBoundedTelescope ind.type ind.numParams fun ps _ => do
      let names ← ps.mapM fun x => do
        unless (← whnf (← inferType x)).isType do
          throwError "derive_primcodable: the parameter `{x}` of `{T}` is not a type"
        let n := toString (← x.fvarId!.getUserName)
        if reserved.contains n then
          throwError "derive_primcodable: rename the parameter `{n}` of `{T}`; the generated \
            code uses that name"
        pure (n, toString (← ppExpr (← inferType x)))
      let self := mkAppN (mkConst T (ind.levelParams.map mkLevelParam)) ps
      let cs ← ind.ctors.toArray.mapM fun c => do
        let info ← getConstInfoCtor c
        forallTelescopeReducing (← instantiateForall info.type ps) fun xs _ => do
          let fields ← xs.mapM fun x => do
            let ty ← inferType x
            if ty == self then return { isRec := true, ty := "" }
            if ty.isAppOfArity ``List 1 && ty.appArg! == self then
              return { isRec := true, isList := true, ty := "" }
            if ty.isAppOfArity ``Option 1 && ty.appArg! == self then
              return { isRec := true, isOpt := true, ty := "" }
            if (ty.find? (·.isConstOf T)).isSome then
              throwError "derive_primcodable: the field type `{ty}` of `{c}` mentions `{T}`; only \
                fields of type `{self}`, `List {self}` or `Option {self}` are supported"
            let s ← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr ty)
            return { isRec := false, ty := toString s }
          return { name := c, fields }
      return (names, cs)

/-- The case analysis `sv.elim (fun d => G j y d) (fun s => …)` on a value `sv` of the summands
from `j` on, out of `n`, with branch `G i y d` for summand `i` (`fuel` bounds the recursion). -/
def sumElimText (G : ℕ → String → String → String) (n : ℕ) : ℕ → ℕ → String → String → String
  | 0, j, y, sv => G j y sv
  | fuel + 1, j, y, sv => if j + 1 ≥ n then G j y sv else
      s!"{sv}.elim (fun d => {G j y "d"}) (fun s => {sumElimText G n fuel (j + 1) y "s"})"

/-- The lines proving `hstep : Primrec fun q : Q => step q.1 q.2.1 q.2.2`, where the step does
case analysis on a shape in the nested sum `D₀ ⊕ (D₁ ⊕ …)`. `G i y d` is the branch of summand `i`,
for the step's input `y : Q` and data `d : Dᵢ`, and `hb i` proves `Primrec fun z : Q × Dᵢ =>
G i z.1 z.2`. The case analysis is proved from the last summand up, one lemma `eᵢ` per level over
`Q × (Dᵢ ⊕ …)`, so that no context grows with the number of constructors. -/
def sumStepLines (Q stepHead : String) (Ds : List String) (G : ℕ → String → String → String)
    (hb : ℕ → String) : List String := Id.run do
  let n := Ds.length
  let rests : List String := (List.range n).map fun i => joinR "⊕" "Empty" (Ds.drop i)
  let E (fuel j : ℕ) (y sv : String) : String := sumElimText G n fuel j y sv
  let C := "DiagonaLean.Foundations.Computability"
  let mut out : List String := []
  -- the branches, then the levels from the last summand up
  for i in List.range n do
    out := out ++ [s!"  have hb{i} : Primrec fun z : ({Q}) × ({Ds[i]!}) => {G i "z.1" "z.2"} := {hb i}"]
  let lift (src tgt : String) : String :=
    s!"((Primrec.fst.comp Primrec.fst).pair Primrec.snd : Primrec fun z : ({src}) × ({tgt}) => (z.1.1, z.2))"
  for i in (List.range n).reverse do
    let zTy := s!"({Q}) × ({rests[i]!})"
    if i + 1 == n then
      out := out ++ [s!"  have e{i} : Primrec fun z : {zTy} => {G i "z.1" "z.2"} := hb{i}"]
    else
      out := out ++ [s!"  have e{i} : Primrec fun z : {zTy} => {E n i "z.1" "z.2"} :=
    {C}.prim_sumElim (o := fun z : {zTy} => z.2)
      (f := fun (z : {zTy}) (d : {Ds[i]!}) => {G i "z.1" "d"})
      (g := fun (z : {zTy}) (s : {rests[i + 1]!}) => {E n (i + 1) "z.1" "s"})
      Primrec.snd (hb{i}.comp {lift zTy Ds[i]!})
      (e{i + 1}.comp {lift zTy rests[i + 1]!})"]
  return out ++ [s!"  have hstep : Primrec fun q : {Q} => {stepHead} q.1 q.2.1 q.2.2 :=
    e0.comp (Primrec.id.pair (Primrec.fst.comp Primrec.snd) :
      Primrec fun q : {Q} => (q, q.2.1))"]

/-- The source text of the declarations for `T`. -/
def generate (T : Name) (pts : Array (String × String)) (cs : Array Ctor) (projNames : Array Name := #[]) :
    List String := Id.run do
  let params := pts.map (·.1)
  let t := toString T
  let args := " ".intercalate params.toList
  -- the type, the shape type, and the binders for the parameters
  let tyStr := if params.isEmpty then t else s!"({t} {args})"
  let shTy := if params.isEmpty then s!"{t}.Shape" else s!"({t}.Shape {args})"
  let implB := " ".intercalate (pts.toList.map fun (p, ty) => "{" ++ p ++ " : " ++ ty ++ "}")
  let instB := " ".intercalate (params.toList.map fun p => s!"[Primcodable {p}]")
  let explB := " ".intercalate (pts.toList.map fun (p, ty) => s!"({p} : {ty})")
  let at_ (f : String) : String := if params.isEmpty then f else s!"(@{f} {args})"
  -- a theorem with its parameters given by name, so that its instance arguments are still found
  let named (f : String) : String := if params.isEmpty then f else
    "(" ++ f ++ " " ++ " ".intercalate (params.toList.map fun p => s!"({p} := {p})") ++ ")"
  let n := cs.size
  let ar := s!"{t}.ar"
  let dataTys (c : Ctor) : List String := (c.fields.filter (!·.isRec)).toList.map (·.ty)
  let m (c : Ctor) : ℕ := (c.fields.filter (·.isRec)).size
  let D (c : Ctor) : String := joinR "×" "Unit" (dataTys c)
  let shape := joinR "⊕" "Empty" (cs.toList.map D)
  let ctorName (c : Ctor) : String := toString c.name
  let shortName (c : Ctor) : String := toString c.name.getString!
  let fieldVars (c : Ctor) : List String := (List.range c.fields.size).map fun i => s!"x{i}"
  let dataVars (c : Ctor) : List String :=
    ((List.range c.fields.size).filter fun i => !c.fields[i]!.isRec).map fun i => s!"x{i}"
  let recVars (c : Ctor) : List String :=
    ((List.range c.fields.size).filter fun i => c.fields[i]!.isRec).map fun i => s!"x{i}"
  let mut out : List String := []
  -- shapes and arities
  out := out ++ [s!"/-- The shapes of `{t}`: one summand per constructor, holding its data. -/
abbrev {t}.Shape {explB} := {shape}"]
  let arCases := (List.range n).map fun i =>
    s!"  | {inj n i "_"} => {m cs[i]!}"
  out := out ++ [s!"/-- The number of recursive fields of each shape. -/
def {ar} {implB} : {shTy} → ℕ\n" ++ "\n".intercalate arCases]
  let elimForm : String := Id.run do
    let mut e := s!"fun _ => {m cs[n-1]!}"
    for i in (List.range (n - 1)).reverse do
      e := s!"fun s => s.elim (fun _ => {m cs[i]!}) ({e})"
    return if n == 1 then s!"fun _ => {m cs[0]!}" else e
  let sPat := "rcases s with " ++ " | ".intercalate ((List.range n).map fun _ => "_")
  out := out ++ [s!"instance {t}.factPrimrecAr {implB} {instB} : Fact (Primrec ({ar} : {shTy} → ℕ)) := ⟨by
  have h : Primrec (({elimForm}) : {shTy} → ℕ) := by fun_prop
  exact h.of_eq fun s => by {sPat} <;> rfl⟩"]
  -- the tree of a term, and back
  let toCases := cs.toList.zipIdx.map fun (c, i) =>
    let kids := if m c == 0 then "fun j => absurd j.isLt (by simp [" ++ ar ++ "])" else
      "fun j => " ++ Id.run do
        let rv := recVars c
        let mut e := s!"{t}.toTree {rv.getLast!}"
        for j in (List.range (rv.length - 1)).reverse do
          e := s!"if j.val = {j} then {t}.toTree {rv[j]!} else {e}"
        return e
    s!"  | .{shortName c} {" ".intercalate (fieldVars c)} => .node ({inj n i (tuple (dataVars c))}) ({kids})"
  out := out ++ [s!"/-- A term as a tree. -/
def {t}.toTree {implB} : {tyStr} → DiagonaLean.Foundations.Computability.PTree {shTy} {ar}\n" ++ "\n".intercalate toCases]
  let ofCases := cs.toList.zipIdx.map fun (c, i) =>
    let args := (List.range c.fields.size).map fun l =>
      if c.fields[l]!.isRec then
        let j := ((List.range l).filter fun l' => c.fields[l']!.isRec).length
        s!"({t}.ofTree (cs ⟨{j}, by simp [{ar}]⟩))"
      else s!"x{l}"
    s!"  | .node ({inj n i (tuple (dataVars c))}) cs => {at_ (ctorName c)} {" ".intercalate args}"
  out := out ++ [s!"/-- A tree as a term. -/
def {t}.ofTree {implB} : DiagonaLean.Foundations.Computability.PTree {shTy} {ar} → {tyStr}\n" ++ "\n".intercalate ofCases]
  out := out ++ [s!"theorem {t}.ofTree_toTree {implB} (x : {tyStr}) : {t}.ofTree ({t}.toTree x) = x := by
  induction x <;> simp_all [{t}.toTree, {t}.ofTree]"]
  let rcPat := " | ".intercalate (cs.toList.map fun c => dataPat (dataVars c))
  let caseScripts := cs.toList.map fun c =>
    let pre := s!"    · simp only [{t}.ofTree, {t}.toTree]; congr 1; funext ⟨j, hj⟩"
    if m c == 0 then pre ++ s!"; simp [{ar}] at hj" else
      let alts := " | ".intercalate (List.replicate (m c) "_" ++ ["j"])
      pre ++ s!"\n      rcases j with {alts}\n" ++
        String.join (List.replicate (m c) "      · simp [ih]\n") ++
        s!"      · first | omega | (revert hj; simp [{ar}]) | (revert hj; simp only [{ar}]; omega)"
  out := out ++ [s!"theorem {t}.toTree_ofTree {implB} (t : DiagonaLean.Foundations.Computability.PTree {shTy} {ar}) : {t}.toTree ({t}.ofTree t) = t := by
  induction t with
  | node a cs ih =>
    rcases a with {rcPat}\n" ++ "\n".intercalate caseScripts]
  out := out ++ [s!"/-- `{t}` and its trees. -/
def {t}.treeEquiv {implB} : {tyStr} ≃ DiagonaLean.Foundations.Computability.PTree {shTy} {ar} :=
  ⟨{t}.toTree, {t}.ofTree, {t}.ofTree_toTree, {t}.toTree_ofTree⟩",
    s!"/-- `{t}` is `Primcodable`, through its trees. -/
instance {t}.primcodable {implB} {instB} : Primcodable {tyStr} :=
  Primcodable.ofEquiv _ {at_ (t ++ ".treeEquiv")}",
    s!"@[fun_prop] theorem {t}.toTree_primrec {implB} {instB} : Primrec {at_ (t ++ ".toTree")} :=
  Primrec.of_equiv (e := {at_ (t ++ ".treeEquiv")})",
    s!"@[fun_prop] theorem {t}.ofTree_primrec {implB} {instB} : Primrec {at_ (t ++ ".ofTree")} :=
  Primrec.of_equiv_symm (e := {at_ (t ++ ".treeEquiv")})"]
  -- constructors
  for (c, i) in cs.toList.zipIdx do
    let k := c.fields.size
    if k == 0 then continue
    let tys := c.fields.toList.map fun f => if f.isRec then tyStr else f.ty
    let qTy := joinR "×" "Unit" tys
    let qp := projs "q" k
    let dataQ := ((List.range k).filter fun l => !c.fields[l]!.isRec).map fun l => qp[l]!
    let recQ := ((List.range k).filter fun l => c.fields[l]!.isRec).map fun l => s!"{t}.toTree {qp[l]!}"
    let built := s!"(DiagonaLean.Foundations.Computability.PTree.mkOpt (({inj n i (tuple dataQ)}) : {shTy}) [{", ".intercalate recQ}]).map {t}.ofTree"
    out := out ++ [s!"theorem {t}.{shortName c}_primrec {implB} {instB} :
    Primrec fun q : {qTy} => {at_ (ctorName c)} {" ".intercalate qp} := by
  have hs : ∀ q : {qTy}, ({built}).isSome := fun q => by
    rw [DiagonaLean.Foundations.Computability.PTree.mkOpt, dite_eq_left_of_eq_true (eq_true (by rfl))]; rfl
  have h : Primrec fun q : {qTy} => {built} := by fun_prop
  exact (Primrec.option_get (h := hs) h).of_eq fun q => by
    simp [DiagonaLean.Foundations.Computability.PTree.mkOpt, {ar}, {t}.ofTree, {t}.ofTree_toTree]"]
    let fs := (List.range k).map fun l => s!"f{l}"
    let hyps := (List.range k).map fun l => s!"(h{l} : Primrec f{l})"
    let fArgs := (List.range k).map fun l => s!"\{f{l} : β → {tys[l]!}}"
    let pairs := if k == 1 then "h0" else Id.run do
      let mut e := s!"h{k-1}"
      for l in (List.range (k - 1)).reverse do
        e := s!"(h{l}.pair {e})"
      return e
    out := out ++ [s!"@[fun_prop] theorem {t}.prim_{shortName c} {implB} {instB} \{β : Type*} [Primcodable β] {" ".intercalate fArgs}
    {" ".intercalate hyps} :
    Primrec fun x => {at_ (ctorName c)} {" ".intercalate (fs.map fun f => s!"({f} x)")} :=
  {t}.{shortName c}_primrec.comp {pairs}"]
  -- projections of a structure: field `l` is a component of the root shape
  if n == 1 && projNames.size == cs[0]!.fields.size && cs[0]!.fields.all (!·.isRec) then
    let k := cs[0]!.fields.size
    for (pn, l) in projNames.toList.zipIdx do
      let fld := toString pn
      let comp := Id.run do
        let mut e := s!"(DiagonaLean.Foundations.Computability.PTree.shape_primrec.comp {named (t ++ ".toTree_primrec")})"
        if k == 1 then return e
        for _ in List.range l do
          e := s!"(Primrec.snd.comp {e})"
        if l + 1 < k then e := s!"(Primrec.fst.comp {e})"
        return e
      let shapeOf := "(DiagonaLean.Foundations.Computability.PTree.shape (" ++ t ++ ".toTree t))"
      let sel := (projs shapeOf k)[l]!
      out := out ++ [s!"/-- The projection `{fld}` is primitive recursive. -/
@[fun_prop] theorem {t}.prim_{fld} {implB} {instB} \{β : Type*} [Primcodable β] \{f : β → {tyStr}}
    (hf : Primrec f) : Primrec fun x => (f x).{fld} := by
  have h : Primrec fun t : {tyStr} => {sel} := {comp}
  exact (h.of_eq fun t => by cases t; rfl).comp hf"]
  -- structural recursion
  let gArgs := cs.toList.map fun c =>
    s!"(g_{shortName c} : P → {" → ".intercalate (dataTys c ++ ["List σ → σ"])})"
  let hEqs := cs.toList.map fun c =>
    let fv := fieldVars c
    let lhs := s!"f p ({at_ (ctorName c)} {" ".intercalate fv})"
    let rs := "[" ++ ", ".intercalate ((recVars c).map fun r => s!"f p {r}") ++ "]"
    let binders := if fv.isEmpty then "∀ p" else s!"∀ p {" ".intercalate fv}"
    s!"(h_{shortName c} : {binders}, {lhs} = g_{shortName c} p {" ".intercalate (dataVars c)} {rs})"
  let hPrims := cs.toList.map fun c =>
    let dt := dataTys c
    let k := dt.length
    let qTy := "P × (" ++ joinR "×" "Unit" (dt ++ ["List σ"]) ++ ")"
    let qp := projs "q.2" (k + 1)
    s!"(hg_{shortName c} : Primrec fun q : {qTy} => g_{shortName c} q.1 {" ".intercalate qp})"
  let Q := s!"P × ({shTy} × List σ)"
  let stepBody : String := Id.run do
    let branch (c : Ctor) (d : String) : String :=
      s!"g_{shortName c} p {" ".intercalate (projs d (dataTys c).length)} rs"
    if n == 1 then return branch cs[0]! "s"
    let mut e := s!"fun d => {branch cs[n-1]! "d"}"
    for i in (List.range (n - 1)).reverse do
      e := s!"fun s => s.elim (fun d => {branch cs[i]! "d"}) ({e})"
    return s!"({e}) s"
  -- `hstep`: the case analysis on the shape, proved level by level (`sumStepLines`)
  let G (i : ℕ) (y d : String) : String :=
    let c := cs[i]!
    s!"g_{shortName c} {y}.1 {" ".intercalate (projs d (dataTys c).length)} {y}.2.2"
  let hb (i : ℕ) : String :=
    let c := cs[i]!
    let args := projs "z.2" (dataTys c).length ++ ["z.1.2.2"]
    s!"hg_{shortName c}.comp ({projPrim "z.1.1"}.pair {tuplePrim args} :
      Primrec fun z : ({Q}) × ({D c}) => {tuple (["z.1.1"] ++ [tuple args])})"
  let stepLam := s!"(fun (p : P) (s : {shTy}) (rs : List σ) => {stepBody})"
  let stepLines := sumStepLines Q stepLam (cs.toList.map D) G hb
  let indCases := cs.toList.map fun c =>
    let ihs := (recVars c).map fun r => s!"ih_{r}"
    let rwl := ", ".intercalate ([s!"h_{shortName c}"] ++ ihs)
    s!"    | {shortName c} {" ".intercalate (fieldVars c ++ ihs)} =>
      rw [{rwl}]
      try simp [{t}.toTree, DiagonaLean.Foundations.Computability.PTree.fold, List.ofFn, {ar}, Fin.foldr_succ, Fin.foldr_zero]"
  out := out ++ [s!"/-- **Structural recursion on `{t}` is primitive recursive.** -/
theorem {t}.primrec_of_eqns {implB} {instB} \{P σ : Type*} [Primcodable P] [Primcodable σ] [Inhabited σ]
    \{f : P → {tyStr} → σ} {" ".intercalate gArgs}
    {"\n    ".intercalate hEqs}
    {"\n    ".intercalate hPrims} : Primrec₂ f := by
{"\n".intercalate stepLines}
  have heq : ∀ p x, f p x =
      DiagonaLean.Foundations.Computability.PTree.fold (fun (p : P) (s : {shTy}) (rs : List σ) => {stepBody}) p ({t}.toTree x) := by
    intro p x
    induction x with
{"\n".intercalate indCases}
  exact ((DiagonaLean.Foundations.Computability.PTree.fold_primrec hstep).comp Primrec.fst ({named (t ++ ".toTree_primrec")}.comp Primrec.snd)).of_eq
    fun q => (heq q.1 q.2).symm"]
  return out

/-- The source text of the declarations for a nested `T`: some field has type `List T`. A node
records the length of each such list in its shape, so every tree is the tree of a term. -/
def generateNested (T : Name) (pts : Array (String × String)) (cs : Array Ctor) : List String := Id.run do
  let params := pts.map (·.1)
  let t := toString T
  let C := "DiagonaLean.Foundations.Computability"
  let args := " ".intercalate params.toList
  let tyStr := if params.isEmpty then t else s!"({t} {args})"
  let shTy := if params.isEmpty then s!"{t}.Shape" else s!"({t}.Shape {args})"
  let implB := " ".intercalate (pts.toList.map fun (p, ty) => "{" ++ p ++ " : " ++ ty ++ "}")
  let instB := " ".intercalate (params.toList.map fun p => s!"[Primcodable {p}]")
  let explB := " ".intercalate (pts.toList.map fun (p, ty) => s!"({p} : {ty})")
  let at_ (f : String) : String := if params.isEmpty then f else s!"(@{f} {args})"
  let named (f : String) : String := if params.isEmpty then f else
    "(" ++ f ++ " " ++ " ".intercalate (params.toList.map fun p => s!"({p} := {p})") ++ ")"
  let n := cs.size
  let ar := s!"{t}.ar"
  let tree := s!"{C}.PTree {shTy} {ar}"
  let idxs (c : Ctor) : List ℕ := List.range c.fields.size
  let dIdx (c : Ctor) : List ℕ := (idxs c).filter fun l => !c.fields[l]!.isRec
  let rIdx (c : Ctor) : List ℕ := (idxs c).filter fun l => c.fields[l]!.isRec
  -- the container fields (`List T`, `Option T`): the shape records a length or a `Bool`
  let isL (c : Ctor) (l : ℕ) : Bool := c.fields[l]!.isList
  let isO (c : Ctor) (l : ℕ) : Bool := c.fields[l]!.isOpt
  let lIdx (c : Ctor) : List ℕ := (idxs c).filter fun l => isL c l || isO c l
  let compTy (c : Ctor) (l : ℕ) : String := if isO c l then "Bool" else "ℕ"
  let dataTys (c : Ctor) : List String := (dIdx c).map fun l => c.fields[l]!.ty
  let resTys (c : Ctor) : List String := (rIdx c).map fun l =>
    if isL c l then "List σ" else if isO c l then "Option σ" else "σ"
  -- the shape of a constructor: its data, then a component for each container field
  let D (c : Ctor) : String := joinR "×" "Unit" (dataTys c ++ (lIdx c).map (compTy c))
  let anyL := cs.any fun c => (idxs c).any (isL c)
  let anyO := cs.any fun c => (idxs c).any (isO c)
  let shape := joinR "⊕" "Empty" (cs.toList.map D)
  let ctorName (c : Ctor) : String := toString c.name
  let shortName (c : Ctor) : String := toString c.name.getString!
  let xv (l : ℕ) : String := s!"x{l}"
  let nv (l : ℕ) : String := s!"n{l}"
  -- the number of children of field `l`, written with `len` for the length of a list field
  let cnt (c : Ctor) (len : ℕ → String) (l : ℕ) : String :=
    if isL c l then len l else if isO c l then s!"{len l}.toNat" else "1"
  let arE (c : Ctor) (len : ℕ → String) : String :=
    if (rIdx c).isEmpty then "0" else " + ".intercalate ((rIdx c).map (cnt c len))
  let offE (c : Ctor) (len : ℕ → String) (l : ℕ) : String :=
    let before := (rIdx c).filter (· < l)
    if before.isEmpty then "0" else " + ".intercalate (before.map (cnt c len))
  let mut out : List String := []
  out := out ++ [s!"/-- The shapes of `{t}`: one summand per constructor, holding its data and the
length of each of its list fields. -/
abbrev {t}.Shape {explB} := {shape}"]
  let arCases := cs.toList.zipIdx.map fun (c, i) =>
    let pat := if (lIdx c).isEmpty then "_" else
      tuple ((dIdx c).map (fun _ => "_") ++ (lIdx c).map nv)
    s!"  | {inj n i pat} => {arE c nv}"
  out := out ++ [s!"/-- The number of children of each shape. -/
def {ar} {implB} : {shTy} → ℕ\n" ++ "\n".intercalate arCases]
  -- `ar` as a nested `Sum.elim`, for `fun_prop`
  let arD (c : Ctor) (d : String) : String :=
    let k := (dIdx c).length + (lIdx c).length
    let ps := projs d k
    arE c fun l => ps[(dIdx c).length + (lIdx c).idxOf l]!
  let elimForm : String := Id.run do
    if n == 1 then return s!"fun d => {arD cs[0]! "d"}"
    let mut e := s!"fun d => {arD cs[n-1]! "d"}"
    for i in (List.range (n - 1)).reverse do
      e := s!"fun s => s.elim (fun d => {arD cs[i]! "d"}) ({e})"
    return e
  let sPat := "rcases s with " ++ " | ".intercalate ((List.range n).map fun _ => "_")
  out := out ++ [s!"instance {t}.factPrimrecAr {implB} {instB} : Fact (Primrec ({ar} : {shTy} → ℕ)) := ⟨by
  have h : Primrec (({elimForm}) : {shTy} → ℕ) := by fun_prop
  exact h.of_eq fun s => by {sPat} <;> rfl⟩"]
  -- the tree of a term, with a helper for lists of terms, and back
  let kids (c : Ctor) (v : ℕ → String) : String :=
    if (rIdx c).isEmpty then "[]" else " ++ ".intercalate ((rIdx c).map fun l =>
      if isL c l then s!"({t}.toTreeL {v l}).toList"
      else if isO c l then s!"({t}.toTreeO {v l}).toList" else s!"[{t}.toTree {v l}]")
  let lenTac := "simp only [List.length_append, List.length_singleton, List.Vector.toList_length, List.length_nil]"
  let toCases := cs.toList.zipIdx.map fun (c, i) =>
    let comp (l : ℕ) : String := if isO c l then s!"{xv l}.isSome" else s!"{xv l}.length"
    let sh := inj n i (tuple ((dIdx c).map xv ++ (lIdx c).map comp))
    let ch := if (rIdx c).isEmpty then s!"fun j => absurd j.isLt (by simp [{ar}])" else
      s!"fun j => ({kids c xv})[j.val]'(by have := j.isLt; simp only [{ar}] at this; (try {lenTac}); omega)"
    s!"  | .{shortName c} {" ".intercalate ((idxs c).map xv)} => .node ({sh}) ({ch})"
  let helperL := if !anyL then "" else s!"
/-- A list of terms as a vector of trees. -/
def {t}.toTreeL {implB} : (xs : List {tyStr}) → List.Vector ({tree}) xs.length
  | [] => List.Vector.nil
  | xh :: xt => {t}.toTree xh ::ᵥ {t}.toTreeL xt"
  let helperO := if !anyO then "" else s!"
/-- An optional term as a vector of trees. -/
def {t}.toTreeO {implB} : (o : Option {tyStr}) → List.Vector ({tree}) o.isSome.toNat
  | none => List.Vector.nil
  | some xh => {t}.toTree xh ::ᵥ List.Vector.nil"
  out := out ++ [s!"mutual
/-- A term as a tree. -/
def {t}.toTree {implB} : {tyStr} → {tree}\n" ++ "\n".intercalate toCases ++ helperL ++ helperO ++ "\nend"]
  if anyL then
    out := out ++ [s!"theorem {t}.toTreeL_eq {implB} (xs : List {tyStr}) : ({t}.toTreeL xs).toList = xs.map {t}.toTree := by
  induction xs with
  | nil => rfl
  | cons xh xt ih => simp [{t}.toTreeL, ih]"]
  if anyO then
    out := out ++ [s!"theorem {t}.toTreeO_eq {implB} (o : Option {tyStr}) : ({t}.toTreeO o).toList = o.toList.map {t}.toTree := by
  cases o <;> rfl"]
  -- the simp lemmas for the helpers that exist
  let helperEqs : String := ", ".intercalate ((if anyL then [s!"{t}.toTreeL_eq"] else []) ++
    (if anyO then [s!"{t}.toTreeO_eq"] else []))
  -- one case per constructor and per assignment of `true`/`false` to its option fields
  let boolTac := "simp only [" ++ ar ++ ", Bool.toNat_true, Bool.toNat_false]"
  let ofCases := cs.toList.zipIdx.flatMap fun (c, i) =>
    let oIdx := (lIdx c).filter (isO c)
    let assigns : List (List Bool) := oIdx.foldr (fun _ acc => acc.flatMap fun a => [true :: a, false :: a]) [[]]
    assigns.map fun bs =>
      let val (l : ℕ) : String := match oIdx.idxOf? l with
        | some j => if bs[j]! then "true" else "false"
        | none => nv l
      let pat := inj n i (tuple ((dIdx c).map xv ++ (lIdx c).map val))
      let fargs := (idxs c).map fun l =>
        if !c.fields[l]!.isRec then xv l
        else if isL c l then
          s!"(List.ofFn fun i : Fin {nv l} => {t}.ofTree (cs ⟨{offE c val l} + i.val, by have := i.isLt; {boolTac} <;> omega⟩))"
        else if isO c l then
          if val l == "true" then s!"(some ({t}.ofTree (cs ⟨{offE c val l}, by {boolTac} <;> omega⟩)))"
          else "none"
        else s!"({t}.ofTree (cs ⟨{offE c val l}, by {boolTac} <;> omega⟩))"
      s!"  | .node ({pat}) cs => {at_ (ctorName c)} {" ".intercalate fargs}"
  out := out ++ [s!"/-- A tree as a term. -/
def {t}.ofTree {implB} : {tree} → {tyStr}\n" ++ "\n".intercalate ofCases]
  -- the round trips, by induction with a motive for each container of terms, numbered by first
  -- occurrence, as Lean numbers the auxiliary types of a nested inductive
  let auxKinds : List Bool := Id.run do  -- `true` for `Option T`, `false` for `List T`
    let mut acc : List Bool := []
    for c in cs do
      for l in idxs c do
        if isL c l && !acc.contains false then acc := acc ++ [false]
        if isO c l && !acc.contains true then acc := acc ++ [true]
    return acc
  let motives (P : String) : String := " ".intercalate (auxKinds.zipIdx.map fun (_, j) =>
    s!"(motive_{j + 2} := fun xs => ∀ c ∈ xs, {P})")
  let auxCases (ind : String) : String := "\n".intercalate (auxKinds.map fun o =>
    if o then s!"{ind}next => simp_all
{ind}next xh ihh d hd => (simp only [Option.mem_def, Option.some.injEq] at hd); subst hd; exact ihh"
    else s!"{ind}next => simp_all
{ind}next xh xt ihh iht d hd => rcases List.mem_cons.1 hd with rfl | hd <;> simp_all")
  let rtCases := cs.toList.map fun c =>
    let ihs := (rIdx c).map fun l => s!"ih{l}"
    let head := s!"  next {" ".intercalate ((idxs c).map xv ++ ihs)} =>"
    let splits := String.join (((idxs c).filter (isO c)).map fun l => s!"
    all_goals cases {xv l}")
    if (rIdx c).isEmpty then head ++ s!" simp [{t}.toTree, {t}.ofTree]" else head ++ splits ++ s!"
    all_goals rw [{t}.toTree]
    all_goals try simp only [Option.isSome_some, Option.isSome_none]
    all_goals rw [{t}.ofTree]
    all_goals congr 1
    all_goals try (apply List.ext_getElem (by simp); intro i h1 h2)
    all_goals
      try simp only [{helperEqs}, Option.toList_some, Option.toList_none, List.map_cons, List.map_nil,
        Option.isSome_some, Option.isSome_none, dite_true, dite_false, Bool.false_eq_true, ↓reduceDIte]
      try simp only [List.getElem_ofFn]
      try simp (disch := (simp [{helperEqs}]; try omega)) only
        [List.getElem_append_left, List.getElem_append_right]
      simp [{helperEqs}, *]"
  out := out ++ [s!"theorem {t}.ofTree_toTree {implB} (x : {tyStr}) : {t}.ofTree ({t}.toTree x) = x := by
  induction x using {t}.rec {motives s!"{t}.ofTree ({t}.toTree c) = c"}
" ++ "\n".intercalate rtCases ++ "\n" ++ auxCases "  "]
  let rcPat := " | ".intercalate (cs.toList.map fun c => dataPat ((dIdx c).map xv ++ (lIdx c).map nv))
  let trCases := cs.toList.map fun c =>
    if (rIdx c).isEmpty then
      s!"    · simp only [{t}.ofTree, {t}.toTree]; congr 1; funext ⟨j, hj⟩; simp [{ar}] at hj"
    else
      let splits := ((lIdx c).filter (isO c)).map fun l => s!"all_goals cases {nv l}"
      "    · " ++ "\n      ".intercalate (splits ++ [s!"all_goals rw [{t}.ofTree, {t}.toTree]",
        s!"all_goals refine {C}.PTree.node_congr (by simp) fun i hi => ?_",
        s!"all_goals
        try simp only [{helperEqs}, List.map_ofFn, dite_true, dite_false, ↓reduceDIte,
          List.map_cons, List.map_nil, Option.toList_some, Option.toList_none, Option.isSome_some, Option.isSome_none, Bool.false_eq_true, Bool.toNat_true, Bool.toNat_false]
        simp only [{ar}, List.length_ofFn, Option.toList_some, Option.toList_none, Option.isSome_some, Option.isSome_none, Bool.false_eq_true, Bool.toNat_true, Bool.toNat_false] at hi
        try simp only [List.getElem_append, List.getElem_singleton, List.length_append,
          List.length_singleton, List.length_ofFn, List.length_map, List.getElem_ofFn,
          List.getElem_map, Function.comp_apply, List.length_cons, List.length_nil, Option.toList_some, Option.toList_none, Option.isSome_some, Option.isSome_none, Bool.false_eq_true, Bool.toNat_true, Bool.toNat_false, ih]
        (try split_ifs) <;> (try congr 1) <;> (try ext) <;> (try simp) <;> omega"])
  out := out ++ [s!"theorem {t}.toTree_ofTree {implB} (t : {tree}) : {t}.toTree ({t}.ofTree t) = t := by
  induction t with
  | node a cs ih =>
    rcases a with {rcPat}\n" ++ "\n".intercalate trCases]
  out := out ++ [s!"/-- `{t}` and its trees. -/
def {t}.treeEquiv {implB} : {tyStr} ≃ {tree} :=
  ⟨{t}.toTree, {t}.ofTree, {t}.ofTree_toTree, {t}.toTree_ofTree⟩",
    s!"/-- `{t}` is `Primcodable`, through its trees. -/
instance {t}.primcodable {implB} {instB} : Primcodable {tyStr} :=
  Primcodable.ofEquiv _ {at_ (t ++ ".treeEquiv")}",
    s!"@[fun_prop] theorem {t}.toTree_primrec {implB} {instB} : Primrec {at_ (t ++ ".toTree")} :=
  Primrec.of_equiv (e := {at_ (t ++ ".treeEquiv")})",
    s!"@[fun_prop] theorem {t}.ofTree_primrec {implB} {instB} : Primrec {at_ (t ++ ".ofTree")} :=
  Primrec.of_equiv_symm (e := {at_ (t ++ ".treeEquiv")})"]
  -- constructors
  for (c, i) in cs.toList.zipIdx do
    let k := c.fields.size
    if k == 0 then continue
    let tys := (idxs c).map fun l =>
      if isL c l then s!"List {tyStr}" else if isO c l then s!"Option {tyStr}"
      else if c.fields[l]!.isRec then tyStr else c.fields[l]!.ty
    let qTy := joinR "×" "Unit" tys
    let qp := projs "q" k
    let compQ (l : ℕ) : String := if isO c l then s!"{qp[l]!}.isSome" else s!"{qp[l]!}.length"
    let sh := inj n i (tuple ((dIdx c).map (qp[·]!) ++ (lIdx c).map compQ))
    let built := s!"({C}.PTree.mkOpt (({sh}) : {shTy}) ({kids c (qp[·]!)})).map {t}.ofTree"
    let ctorQ := s!"{at_ (ctorName c)} {" ".intercalate qp}"
    out := out ++ [s!"theorem {t}.{shortName c}_primrec {implB} {instB} :
    Primrec fun q : {qTy} => {ctorQ} := by
  have h : Primrec fun q : {qTy} => {built} := by
    try simp only [{helperEqs}]
    fun_prop
  have hs : ∀ q : {qTy}, {built} = some ({ctorQ}) := fun q => by
    rw [{C}.PTree.mkOpt, dite_eq_left_of_eq_true (eq_true (by simp only [{ar}]; (try {lenTac}); try omega))]
    have := {t}.ofTree_toTree ({ctorQ})
    rw [{t}.toTree] at this
    exact congrArg some this
  exact (Primrec.option_get (h := fun q => by rw [hs q]; rfl) h).of_eq fun q =>
    Option.some_injective _ ((Option.some_get _).trans (hs q))"]
    let fs := (List.range k).map fun l => s!"f{l}"
    let hyps := (List.range k).map fun l => s!"(h{l} : Primrec f{l})"
    let fArgs := (List.range k).map fun l => s!"\{f{l} : β → {tys[l]!}}"
    let pairs := if k == 1 then "h0" else Id.run do
      let mut e := s!"h{k-1}"
      for l in (List.range (k - 1)).reverse do
        e := s!"(h{l}.pair {e})"
      return e
    out := out ++ [s!"@[fun_prop] theorem {t}.prim_{shortName c} {implB} {instB} \{β : Type*} [Primcodable β] {" ".intercalate fArgs}
    {" ".intercalate hyps} :
    Primrec fun x => {at_ (ctorName c)} {" ".intercalate (fs.map fun f => s!"({f} x)")} :=
  {t}.{shortName c}_primrec.comp {pairs}"]
  -- structural recursion: the step sees the data, and the results on each recursive field
  let gArgs := cs.toList.map fun c =>
    s!"(g_{shortName c} : P → {" → ".intercalate (dataTys c ++ resTys c ++ ["σ"])})"
  let hEqs := cs.toList.map fun c =>
    let fv := (idxs c).map xv
    let lhs := s!"f p ({at_ (ctorName c)} {" ".intercalate fv})"
    let res := (rIdx c).map fun l =>
      if isL c l || isO c l then s!"({xv l}.map (f p))" else s!"(f p {xv l})"
    let binders := if fv.isEmpty then "∀ p" else s!"∀ p {" ".intercalate fv}"
    s!"(h_{shortName c} : {binders}, {lhs} = g_{shortName c} p {" ".intercalate ((dIdx c).map xv ++ res)})"
  let hPrims := cs.toList.map fun c =>
    let ts := dataTys c ++ resTys c
    let qTy := "P × (" ++ joinR "×" "Unit" ts ++ ")"
    s!"(hg_{shortName c} : Primrec fun q : {qTy} => g_{shortName c} q.1 {" ".intercalate (projs "q.2" ts.length)})"
  -- the arguments of `g_c` in the step, from the shape `d` and the children's results `rs`
  let gArgsOf (c : Ctor) (d rs : String) : List String :=
    let k := (dIdx c).length + (lIdx c).length
    let ps := projs d k
    let dataP := (List.range (dIdx c).length).map (ps[·]!)
    let len (l : ℕ) : String := ps[(dIdx c).length + (lIdx c).idxOf l]!
    let ch := s!"({C}.chunks [{", ".intercalate ((rIdx c).map (cnt c len))}] {rs})"
    let res := (rIdx c).zipIdx.map fun (l, j) =>
      if isL c l then s!"({ch}.getD {j} [])" else if isO c l then s!"({ch}.getD {j} []).head?"
      else s!"({ch}.getD {j} []).headI"
    dataP ++ res
  let B (c : Ctor) (p d rs : String) : String := s!"g_{shortName c} {p} {" ".intercalate (gArgsOf c d rs)}"
  let stepBody : String := Id.run do
    if n == 1 then return B cs[0]! "p" "s" "rs"
    let mut e := s!"fun d => {B cs[n-1]! "p" "d" "rs"}"
    for i in (List.range (n - 1)).reverse do
      e := s!"fun s => s.elim (fun d => {B cs[i]! "p" "d" "rs"}) ({e})"
    return s!"({e}) s"
  let Q := s!"P × ({shTy} × List σ)"
  let G (i : ℕ) (y d : String) : String := B cs[i]! s!"{y}.1" d s!"{y}.2.2"
  let hb (i : ℕ) : String :=
    let c := cs[i]!
    s!"hg_{shortName c}.comp (by fun_prop : Primrec fun z : ({Q}) × ({D c}) => {tuple (["z.1.1"] ++ [tuple (gArgsOf c "z.2" "z.1.2.2")])})"
  let stepLines := sumStepLines Q "step" (cs.toList.map D) G hb
  let indCases := cs.toList.map fun c =>
    let ihs := (rIdx c).map fun l => s!"ih{l}"
    let head := s!"    next {" ".intercalate ((idxs c).map xv ++ ihs)} =>"
    if (rIdx c).isEmpty then head ++ s!"
      rw [h_{shortName c}, {t}.toTree, {C}.PTree.fold]; rfl" else
    let backs := ", ".intercalate ((rIdx c).map fun l =>
      if isL c l then s!"← List.map_congr_left ih{l}"
      else if isO c l then
        s!"← List.map_congr_left (fun c hc => ih{l} c (Option.mem_def.2 (Option.mem_toList.1 hc)))"
      else s!"← ih{l}")
    head ++ s!"
      rw [h_{shortName c}, {t}.toTree, {C}.PTree.fold, {C}.ofFn_getElem_eq_map' _ _ _ (by
        simp only [{ar}]; try simp only [{helperEqs}, List.length_append, List.length_singleton, List.length_map, {C}.length_toList_option]
        try omega)]
      simp only [{helperEqs}, List.map_append, List.map_map, List.map_cons, List.map_nil,
        Function.comp_def, {backs}, List.append_assoc]
      simp only [step, Sum.elim_inr, Sum.elim_inl]
      repeat rw [{C}.chunks_cons_append _ _ _ _ (by simp [{C}.length_toList_option])]
      try rw [{C}.chunks_singleton _ _ (by simp [{C}.length_toList_option])]
      first | rfl | simp [{C}.head?_map_toList]"
  out := out ++ [s!"/-- **Structural recursion on `{t}` is primitive recursive.** The step of a constructor sees
its data and the results on its recursive fields: a value for a field of type `{t}`, a list of
values for a field of type `List {t}`, an optional value for a field of type `Option {t}`. -/
theorem {t}.primrec_of_eqns {implB} {instB} \{P σ : Type*} [Primcodable P] [Primcodable σ] [Inhabited σ]
    \{f : P → {tyStr} → σ} {" ".intercalate gArgs}
    {"\n    ".intercalate hEqs}
    {"\n    ".intercalate hPrims} : Primrec₂ f := by
  let step : P → {shTy} → List σ → σ := fun p s rs => {stepBody}
{"\n".intercalate stepLines}
  have heq : ∀ p x, f p x = {C}.PTree.fold step p ({t}.toTree x) := by
    intro p x
    induction x using {t}.rec {motives s!"f p c = {C}.PTree.fold step p ({t}.toTree c)"}
{"\n".intercalate indCases}
{auxCases "    "}
  exact (({C}.PTree.fold_primrec hstep).comp Primrec.fst ({named (t ++ ".toTree_primrec")}.comp Primrec.snd)).of_eq
    fun q => (heq q.1 q.2).symm"]
  return out

/-- `stx` with every position replaced by `info`, so that messages about generated code point at
the command that generated it. -/
partial def withInfo (info : SourceInfo) : Syntax → Syntax
  | .node _ k args => .node info k (args.map (withInfo info))
  | .atom _ v => .atom info v
  | .ident _ raw v pre => .ident info raw v pre
  | .missing => .missing

/-- `derive_primcodable T` makes `T` `Primcodable` through its trees; see the module docstring. -/
elab (name := derivePrimcodable) "derive_primcodable " id:ident : command => do
  let T ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let (params, cs) ← readCtors T
  let some (.inductInfo ind) := (← getEnv).find? T | unreachable!
  let inScope := (← getScope).levelNames
  let fresh := ind.levelParams.filter (!inScope.contains ·)
  let univs := if fresh.isEmpty then "" else
    "universe " ++ " ".intercalate (fresh.map toString) ++ " in\n"
  let info := SourceInfo.fromRef id
  let env ← getEnv
  let projNames := if isStructure env T then getStructureFields env T else #[]
  let srcs := if cs.any (·.fields.any fun f => f.isList || f.isOpt) then generateNested T params cs
    else generate T params cs projNames
  for src in srcs do
    -- generic `simp` sets in generated proofs have unused entries by design
    let src := univs ++ "set_option linter.unusedSimpArgs false in\n" ++ src
    let stx ← match Parser.runParserCategory (← getEnv) `command src with
      | .ok stx => pure stx
      | .error e => throwError "derive_primcodable: generated code does not parse: {e}\n{src}"
    elabCommand (withInfo info stx)

end DiagonaLean.Foundations.Computability.DerivePrimcodable
