/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.LambdaCalculus.Code
import DiagonaLean.Foundations.Computability.PolyTree
import DiagonaLean.Foundations.Computability.TaggedCode

@[expose] public section

/-! # λ-terms are `Primcodable`, and `tc` is a correct encoding

A locally nameless λ-term over `ℕ` is a tree with shapes `abs` (one child), `app` (two children),
`bvar i` and `fvar x` (none): `Term ℕ ≃ PTree (Fin 2 ⊕ (ℕ ⊕ ℕ)) termAr` (`termEquiv`), so
`Term ℕ` is `Primcodable` (Theorem A). The hand-made code `tc` is primitive recursive (`tc_primrec`,
as a fold) and decodes in one step from its children, so it is a correct encoding
(`primrec_iff_tc`, by `TaggedCode.primrec_iff`).
-/

namespace DiagonaLean.Foundations.LambdaCalculus

open Cslib LambdaCalculus.LocallyNameless.Untyped DiagonaLean.Foundations.Computability PTree

/-- The arities: `abs` has one child, `app` two, variables none. -/
def termAr : Fin 2 ⊕ (ℕ ⊕ ℕ) → ℕ
  | .inl i => if i.val = 0 then 1 else 2
  | .inr _ => 0

instance : Fact (Primrec termAr) := ⟨(Primrec.sumCasesOn Primrec.id
  ((Primrec.dom_finite fun i : Fin 2 => if i.val = 0 then 1 else 2).comp₂ Primrec₂.right)
  ((Primrec.const 0).comp₂ Primrec₂.right)).of_eq fun x => by cases x <;> rfl⟩

/-- The tree of shapes of a λ-term. -/
abbrev TermTree := PTree (Fin 2 ⊕ (ℕ ⊕ ℕ)) termAr

/-- A λ-term as a tree. -/
def toTree : Term ℕ → TermTree
  | .bvar i => .node (.inr (.inl i)) Fin.elim0
  | .fvar x => .node (.inr (.inr x)) Fin.elim0
  | .abs M => .node (.inl 0) fun _ => toTree M
  | .app M N => .node (.inl 1) fun i => if i.val = 0 then toTree M else toTree N

/-- A tree as a λ-term. -/
def ofTree : TermTree → Term ℕ
  | .node (.inr (.inl i)) _ => .bvar i
  | .node (.inr (.inr x)) _ => .fvar x
  | .node (.inl ⟨0, _⟩) cs => .abs (ofTree (cs ⟨0, by simp [termAr]⟩))
  | .node (.inl ⟨1, _⟩) cs =>
    .app (ofTree (cs ⟨0, by simp [termAr]⟩)) (ofTree (cs ⟨1, by simp [termAr]⟩))

theorem ofTree_toTree (M : Term ℕ) : ofTree (toTree M) = M := by
  induction M <;> simp_all [toTree, ofTree]

theorem toTree_ofTree (t : TermTree) : toTree (ofTree t) = t := by
  induction t with
  | node a cs ih =>
    rcases a with ⟨_ | _ | i, hi⟩ | (i | x)
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩
      rcases j with _ | j
      · simp [ih]
      · simp [termAr] at hj
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩
      rcases j with _ | _ | j
      · simp [ih]
      · simp [ih]
      · simp [termAr] at hj
    · omega
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩; simp at hj
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩; simp at hj

/-- λ-terms and their trees. -/
def termEquiv : Term ℕ ≃ TermTree where
  toFun := toTree
  invFun := ofTree
  left_inv := ofTree_toTree
  right_inv := toTree_ofTree

/-- **λ-terms are `Primcodable`**, through their trees. -/
instance primcodable : Primcodable (Term ℕ) := Primcodable.ofEquiv _ termEquiv

@[fun_prop] theorem toTree_primrec : Primrec toTree := Primrec.of_equiv (e := termEquiv)
@[fun_prop] theorem ofTree_primrec : Primrec ofTree := Primrec.of_equiv_symm (e := termEquiv)

/-- `abs` is primitive recursive. -/
theorem abs_primrec : Primrec (Term.abs : Term ℕ → Term ℕ) := by
  have h : Primrec fun M : Term ℕ => ((mkOpt (.inl 0) [toTree M]).map ofTree).getD (.bvar 0) := by
    fun_prop
  exact h.of_eq fun M => by
    rw [mkOpt, dite_eq_left_of_eq_true (eq_true (by rfl))]
    simp [ofTree, ofTree_toTree]

/-- `app` is primitive recursive. -/
theorem app_primrec : Primrec₂ (Term.app : Term ℕ → Term ℕ → Term ℕ) := by
  have h : Primrec fun q : Term ℕ × Term ℕ =>
      ((mkOpt (.inl 1) [toTree q.1, toTree q.2]).map ofTree).getD (.bvar 0) := by fun_prop
  exact h.of_eq fun q => by
    rw [mkOpt, dite_eq_left_of_eq_true (eq_true (by rfl))]
    simp [ofTree, ofTree_toTree]

/-- `bvar` is primitive recursive. -/
theorem bvar_primrec : Primrec (Term.bvar : ℕ → Term ℕ) := by
  have h : Primrec fun i : ℕ => ((mkOpt (.inr (.inl i)) ([] : List TermTree)).map ofTree).getD
      (.bvar 0) := by fun_prop
  exact h.of_eq fun i => by
    rw [mkOpt, dite_eq_left_of_eq_true (eq_true (by rfl))]
    simp [ofTree]

/-- `fvar` is primitive recursive. -/
theorem fvar_primrec : Primrec (Term.fvar : ℕ → Term ℕ) := by
  have h : Primrec fun x : ℕ => ((mkOpt (.inr (.inr x)) ([] : List TermTree)).map ofTree).getD
      (.bvar 0) := by fun_prop
  exact h.of_eq fun x => by
    rw [mkOpt, dite_eq_left_of_eq_true (eq_true (by rfl))]
    simp [ofTree]

@[fun_prop] theorem prim_abs {β : Type} [Primcodable β] {f : β → Term ℕ} (hf : Primrec f) :
    Primrec fun x => Term.abs (f x) := abs_primrec.comp hf
@[fun_prop] theorem prim_app {β : Type} [Primcodable β] {f g : β → Term ℕ} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => Term.app (f x) (g x) := app_primrec.comp hf hg
@[fun_prop] theorem prim_bvar {β : Type} [Primcodable β] {f : β → ℕ} (hf : Primrec f) :
    Primrec fun x => (Term.bvar (f x) : Term ℕ) := bvar_primrec.comp hf
@[fun_prop] theorem prim_fvar {β : Type} [Primcodable β] {f : β → ℕ} (hf : Primrec f) :
    Primrec fun x => (Term.fvar (f x) : Term ℕ) := fvar_primrec.comp hf

/-! ### `tc` is a correct encoding -/

/-- One step of `tc`, on a node with shape `s` and the codes `rs` of its children. -/
def tcStep (_ : Unit) (s : Fin 2 ⊕ (ℕ ⊕ ℕ)) (rs : List ℕ) : ℕ :=
  s.elim (fun i => if i.val = 0 then cl rs.headI else cp rs.headI rs.tail.headI)
    fun v => v.elim cb cf

theorem tc_eq_fold (M : Term ℕ) : tc M = fold tcStep () (toTree M) := by
  induction M with
  | bvar i => rfl
  | fvar x => rfl
  | abs M ih => simp [tc, toTree, fold, tcStep, ih, List.ofFn, termAr, Fin.foldr_succ, Fin.foldr_zero]
  | app M N ihM ihN =>
    simp [tc, toTree, fold, tcStep, ihM, ihN, List.ofFn, termAr, Fin.foldr_succ, Fin.foldr_zero]

/-- **`tc` is primitive recursive.** -/
theorem tc_primrec : Primrec tc := by
  have hs : Primrec fun q : Unit × ((Fin 2 ⊕ (ℕ ⊕ ℕ)) × List ℕ) => tcStep q.1 q.2.1 q.2.2 := by
    unfold tcStep; fun_prop
  exact ((fold_primrec hs).comp (Primrec.const ()) toTree_primrec).of_eq fun M =>
    (tc_eq_fold M).symm

/-- The child codes packed into a `tc` code. -/
def tcKids (n : ℕ) : List ℕ :=
  if n.unpair.1 = 2 then [n.unpair.2]
  else if n.unpair.1 = 3 then [n.unpair.2.unpair.1, n.unpair.2.unpair.2] else []

theorem tcKids_lt (n : ℕ) : ∀ m ∈ tcKids n, m < n := by
  intro m hm
  unfold tcKids at hm
  split_ifs at hm with h₁ h₂
  · simp only [List.mem_singleton] at hm
    exact hm ▸ TaggedCode.unpair_snd_lt (by omega)
  · have h : n.unpair.1 ≠ 0 := by omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt (TaggedCode.unpair_snd_lt h)
    · exact (Nat.unpair_right_le _).trans_lt (TaggedCode.unpair_snd_lt h)
  · simp at hm

/-- One decoding step of `tc`. -/
def tcBuild (n : ℕ) (ts : List (Term ℕ)) : Option (Term ℕ) :=
  if n.unpair.1 = 0 then some (.bvar n.unpair.2)
  else if n.unpair.1 = 1 then some (.fvar n.unpair.2)
  else if n.unpair.1 = 2 then ts[0]?.elim none fun M => some (.abs M)
  else if n.unpair.1 = 3 then ts[0]?.elim none fun M => ts[1]?.elim none fun N => some (.app M N)
  else none

theorem tc_spec (M : Term ℕ) :
    ∃ ts, tcKids (tc M) = ts.map tc ∧ tcBuild (tc M) ts = some M := by
  cases M with
  | bvar i => exact ⟨[], by simp [tcKids, tc, cb], by simp [tcBuild, tc, cb]⟩
  | fvar x => exact ⟨[], by simp [tcKids, tc, cf], by simp [tcBuild, tc, cf]⟩
  | abs M => exact ⟨[M], by simp [tcKids, tc, cl], by simp [tcBuild, tc, cl, Option.elim]⟩
  | app M N => exact ⟨[M, N], by simp [tcKids, tc, cp], by simp [tcBuild, tc, cp, Option.elim]⟩

theorem tcKids_primrec : Primrec tcKids := by unfold tcKids; fun_prop

theorem tcBuild_primrec : Primrec fun q : ℕ × List (Term ℕ) => tcBuild q.1 q.2 := by
  unfold tcBuild; fun_prop

/-- **`tc` is a correct encoding.** A function into λ-terms is primitive recursive exactly when it
is so through `tc`. -/
theorem primrec_iff_tc {β : Type} [Primcodable β] {f : β → Term ℕ} :
    Primrec f ↔ Primrec fun b => tc (f b) :=
  TaggedCode.primrec_iff tcKids tcKids_lt tcBuild tc_spec tc_primrec tcKids_primrec
    tcBuild_primrec

end DiagonaLean.Foundations.LambdaCalculus
