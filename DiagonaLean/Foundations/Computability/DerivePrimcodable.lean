/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.PolyTree

@[expose] public section

/-! # `derive_primcodable`: inductive types as trees

`derive_primcodable T`, for an inductive type `T` whose parameters are of sort `Type` (and which
has no indices and is not universe polymorphic, mutual or nested), whose constructor fields are
either `T` itself (applied to its parameters) or data of `Primcodable` types, generates (with
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

The command builds Lean source text and elaborates it with `elabCommand`, so every declaration is
elaborated, checked by the kernel and compiled as if written by hand. It changes the environment
in no other way, and `scripts/check_metaprograms.py` permits only the definition of this command
here. `#print` shows what it generated.
-/

namespace DiagonaLean.Foundations.Computability.DerivePrimcodable

open Lean Elab Command Meta

/-- A constructor field: recursive (of type `T`) or data, with its type as source text. -/
structure Field where
  /-- Whether the field has type `T`. -/
  isRec : Bool
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

/-- The `rcases` pattern of the data tuple of a constructor with `k` data fields. -/
def dataPat (vs : List String) : String :=
  match vs with
  | [] => "⟨⟩"
  | [v] => v
  | vs => "⟨" ++ ", ".intercalate vs ++ "⟩"

/-- Names the generated code uses for its own variables, which a parameter must not take. -/
def reserved : List String :=
  ["P", "σ", "β", "p", "q", "t", "f", "s", "d", "x", "y", "z", "a", "j", "rs", "cs", "hj", "ih"]

/-- Reads the parameters (their names) and the constructors of `T`. -/
def readCtors (T : Name) : CommandElabM (Array String × Array Ctor) := do
  let env ← getEnv
  let some (.inductInfo ind) := env.find? T | throwError "derive_primcodable: `{T}` is not an inductive type"
  unless ind.numIndices == 0 do
    throwError "derive_primcodable: `{T}` has indices, which are not supported"
  unless ind.levelParams.isEmpty do
    throwError "derive_primcodable: `{T}` is universe polymorphic; state its parameters as `Type`"
  unless ind.all.length == 1 && !ind.isNested do
    throwError "derive_primcodable: `{T}` is mutual or nested, which is not supported"
  liftTermElabM do
    forallBoundedTelescope ind.type ind.numParams fun ps _ => do
      let names ← ps.mapM fun x => do
        unless (← inferType x) == mkSort levelOne do
          throwError "derive_primcodable: the parameter `{x}` of `{T}` is not a `Type`"
        let n := toString (← x.fvarId!.getUserName)
        if reserved.contains n then
          throwError "derive_primcodable: rename the parameter `{n}` of `{T}`; the generated \
            code uses that name"
        pure n
      let self := mkAppN (mkConst T) ps
      let cs ← ind.ctors.toArray.mapM fun c => do
        let info ← getConstInfoCtor c
        forallTelescopeReducing (← instantiateForall info.type ps) fun xs _ => do
          let fields ← xs.mapM fun x => do
            let ty ← inferType x
            if ty == self then return { isRec := true, ty := "" }
            if (ty.find? (·.isConstOf T)).isSome then
              throwError "derive_primcodable: the field type `{ty}` of `{c}` mentions `{T}`; only \
                fields of type `{self}` itself are supported"
            let s ← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr ty)
            return { isRec := false, ty := toString s }
          return { name := c, fields }
      return (names, cs)

/-- The source text of the declarations for `T`. -/
def generate (T : Name) (params : Array String) (cs : Array Ctor) (projNames : Array Name := #[]) :
    List String := Id.run do
  let t := toString T
  let args := " ".intercalate params.toList
  -- the type, the shape type, and the binders for the parameters
  let tyStr := if params.isEmpty then t else s!"({t} {args})"
  let shTy := if params.isEmpty then s!"{t}.Shape" else s!"({t}.Shape {args})"
  let implB := " ".intercalate (params.toList.map fun p => "{" ++ p ++ " : Type}")
  let instB := " ".intercalate (params.toList.map fun p => s!"[Primcodable {p}]")
  let explB := " ".intercalate (params.toList.map fun p => s!"({p} : Type)")
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
    out := out ++ [s!"@[fun_prop] theorem {t}.prim_{shortName c} {implB} {instB} \{β : Type} [Primcodable β] {" ".intercalate fArgs}
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
@[fun_prop] theorem {t}.prim_{fld} {implB} {instB} \{β : Type} [Primcodable β] \{f : β → {tyStr}}
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
  -- the hypotheses about each branch of `step`, in the form `fun_prop` meets them
  let Q := s!"P × ({shTy} × List σ)"
  let rests : List String := (List.range n).map fun i => joinR "⊕" "Empty" ((cs.toList.drop i).map D)
  let ctxs : List String := Id.run do
    let mut acc := [Q]
    for i in List.range (n - 1) do
      if i == 0 then continue
      acc := acc ++ [s!"({acc.getLast!}) × ({rests[i]!})"]
    return acc
  let branchHyps := cs.toList.zipIdx.map fun (c, i) =>
    let ctxI := if n == 1 then Q else ctxs[min i (n - 2)]!
    let qpath := if n == 1 then "z" else "z" ++ String.join (List.replicate (min (i + 1) (n - 1)) ".1")
    let dvar := if n == 1 then "z.2.1" else "z.2"
    let k := (dataTys c).length
    let dps := projs dvar k
    let zTy := if n == 1 then Q else s!"({ctxI}) × ({D c})"
    let body := s!"g_{shortName c} {qpath}.1 {" ".intercalate dps} {qpath}.2.2"
    let argTuple := tuple ([s!"{qpath}.1"] ++ [tuple (dps ++ [s!"{qpath}.2.2"])])
    s!"  have hb_{shortName c} : Primrec fun z : {zTy} => {body} :=
    hg_{shortName c}.comp (by fun_prop : Primrec fun z : {zTy} => {argTuple})"
  let stepBody : String := Id.run do
    let branch (c : Ctor) (d : String) : String :=
      s!"g_{shortName c} p {" ".intercalate (projs d (dataTys c).length)} rs"
    if n == 1 then return branch cs[0]! "s"
    let mut e := s!"fun d => {branch cs[n-1]! "d"}"
    for i in (List.range (n - 1)).reverse do
      e := s!"fun s => s.elim (fun d => {branch cs[i]! "d"}) ({e})"
    return s!"({e}) s"
  -- `hstep`, written out: nested `prim_sumElim`, one level per constructor but the last
  let G (c : Ctor) (q d : String) : String :=
    s!"g_{shortName c} {q}.1 {" ".intercalate (projs d (dataTys c).length)} {q}.2.2"
  -- `E i q sv`: the elimination of `sv`, a value of the summands from `i` on
  let E (i : ℕ) (q sv : String) : String := Id.run do
    let mut e := G cs[n-1]! q (if i + 1 == n then sv else "s")
    for j in (List.range (n - 1)).reverse do
      if j < i then continue
      let v := if j == i then sv else "s"
      e := s!"{v}.elim (fun d => {G cs[j]! q "d"}) (fun s => {e})"
    return e
  let alphas : List String := ctxs
  let qexpr (i : ℕ) (y : String) : String := y ++ String.join (List.replicate i ".1")
  -- the proof, from the innermost level out
  let P : String := Id.run do
    let mut acc := s!"hb_{shortName cs[n-1]!}"
    for i in (List.range (n - 1)).reverse do
      let α := alphas[i]!
      let o := if i == 0 then "fun y : " ++ α ++ " => y.2.1" else "fun y : " ++ α ++ " => y.2"
      let po := if i == 0 then "(Primrec.fst.comp Primrec.snd)" else "Primrec.snd"
      let f := s!"fun (y : {α}) (d : {D cs[i]!}) => {G cs[i]! (qexpr i "y") "d"}"
      let g := s!"fun (y : {α}) (s : {rests[i + 1]!}) => {E (i + 1) (qexpr i "y") "s"}"
      acc := s!"(DiagonaLean.Foundations.Computability.prim_sumElim (o := {o}) (f := {f}) (g := {g}) {po} hb_{shortName cs[i]!} {acc})"
    return acc
  let hstepProof := if n == 1 then s!"exact hb_{shortName cs[0]!}" else s!"exact {P}"
  let indCases := cs.toList.map fun c =>
    let ihs := (recVars c).map fun r => s!"ih_{r}"
    let rwl := ", ".intercalate ([s!"h_{shortName c}"] ++ ihs)
    s!"    | {shortName c} {" ".intercalate (fieldVars c ++ ihs)} =>
      rw [{rwl}]
      try simp [{t}.toTree, DiagonaLean.Foundations.Computability.PTree.fold, List.ofFn, {ar}, Fin.foldr_succ, Fin.foldr_zero]"
  out := out ++ [s!"/-- **Structural recursion on `{t}` is primitive recursive.** -/
theorem {t}.primrec_of_eqns {implB} {instB} \{P σ : Type} [Primcodable P] [Primcodable σ] [Inhabited σ]
    \{f : P → {tyStr} → σ} {" ".intercalate gArgs}
    {"\n    ".intercalate hEqs}
    {"\n    ".intercalate hPrims} : Primrec₂ f := by
{"\n".intercalate branchHyps}
  have hstep : Primrec fun q : {Q} =>
      (fun (p : P) (s : {shTy}) (rs : List σ) => {stepBody}) q.1 q.2.1 q.2.2 := by
    {hstepProof}
  have heq : ∀ p x, f p x =
      DiagonaLean.Foundations.Computability.PTree.fold (fun (p : P) (s : {shTy}) (rs : List σ) => {stepBody}) p ({t}.toTree x) := by
    intro p x
    induction x with
{"\n".intercalate indCases}
  exact ((DiagonaLean.Foundations.Computability.PTree.fold_primrec hstep).comp Primrec.fst ({named (t ++ ".toTree_primrec")}.comp Primrec.snd)).of_eq
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
  let info := SourceInfo.fromRef id
  let env ← getEnv
  let projNames := if isStructure env T then getStructureFields env T else #[]
  for src in generate T params cs projNames do
    -- generic `simp` sets in generated proofs have unused entries by design
    let src := "set_option linter.unusedSimpArgs false in\n" ++ src
    let stx ← match Parser.runParserCategory (← getEnv) `command src with
      | .ok stx => pure stx
      | .error e => throwError "derive_primcodable: generated code does not parse: {e}\n{src}"
    elabCommand (withInfo info stx)

end DiagonaLean.Foundations.Computability.DerivePrimcodable
