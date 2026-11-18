/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KACommUndecidable.KleeneAlgebra.ExprCode
import DiagonaLean.Foundations.Computability.PolyTree
import DiagonaLean.Foundations.Computability.TaggedCode

@[expose] public section

/-! # Regular expressions are `Primcodable`

`RExp X` is the tree type `PTree (Fin 5 ⊕ X) rexpAr`: a node is one of `zero`, `one`, `plus`,
`mul`, `star` (shapes `inl 0` to `inl 4`, with 0, 0, 2, 2 and 1 children) or a letter `inr x`
(no children). `toTree` and `ofTree` are inverse (`rexpEquiv`), so `RExp X` is `Primcodable` for
any `Primcodable X`, by Theorem A (`PTree.primcodable`). The constructors are primitive recursive
(`plus_primrec` and so on), through `PTree.mkOpt`.

The hand-made code `rc` of `ExprCode.lean` is a correct encoding: it is primitive recursive
(`rc_primrec`, by Theorem B, `PTree.fold_primrec`), it has a primitive recursive decoder
(`rcDec_primrec`, `rcDec_rc`), and so primitive recursion through `rc` is primitive recursion
(`primrec_iff_rc`).
-/

namespace DiagonaLean.KACommUndecidable.KleeneAlgebra

open DiagonaLean.Foundations.Computability PTree

namespace RExp

variable {X : Type}

/-- The arity of each shape of a regular expression. -/
def rexpAr : Fin 5 ⊕ X → ℕ
  | .inl i => if i.val = 2 ∨ i.val = 3 then 2 else if i.val = 4 then 1 else 0
  | .inr _ => 0

/-- The tree of shapes of an expression. -/
abbrev Tree (X : Type) := PTree (Fin 5 ⊕ X) rexpAr

/-- An expression as a tree. -/
def toTree : RExp X → Tree X
  | zero => .node (.inl 0) Fin.elim0
  | one => .node (.inl 1) Fin.elim0
  | sym x => .node (.inr x) Fin.elim0
  | plus e f => .node (.inl 2) fun i => if i.val = 0 then toTree e else toTree f
  | mul e f => .node (.inl 3) fun i => if i.val = 0 then toTree e else toTree f
  | star e => .node (.inl 4) fun _ => toTree e

/-- A tree as an expression. -/
def ofTree : Tree X → RExp X
  | .node (.inl ⟨0, _⟩) _ => zero
  | .node (.inl ⟨1, _⟩) _ => one
  | .node (.inl ⟨2, _⟩) cs => plus (ofTree (cs ⟨0, by simp [rexpAr]⟩)) (ofTree (cs ⟨1, by simp [rexpAr]⟩))
  | .node (.inl ⟨3, _⟩) cs => mul (ofTree (cs ⟨0, by simp [rexpAr]⟩)) (ofTree (cs ⟨1, by simp [rexpAr]⟩))
  | .node (.inl ⟨4, _⟩) cs => star (ofTree (cs ⟨0, by simp [rexpAr]⟩))
  | .node (.inr x) _ => sym x

theorem ofTree_toTree (e : RExp X) : ofTree (toTree e) = e := by
  induction e <;> simp_all [toTree, ofTree]

theorem toTree_ofTree (t : Tree X) : toTree (ofTree t) = t := by
  induction t with
  | node a cs ih =>
    rcases a with ⟨_ | _ | _ | _ | _ | i, hi⟩ | x
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩; simp at hj
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩; simp at hj
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩
      rcases j with _ | _ | j
      · simp [ih]
      · simp [ih]
      · simp [rexpAr] at hj
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩
      rcases j with _ | _ | j
      · simp [ih]
      · simp [ih]
      · simp [rexpAr] at hj
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩
      rcases j with _ | j
      · simp [ih]
      · simp [rexpAr] at hj
    · omega
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩; simp at hj

/-- Expressions and their trees. -/
def rexpEquiv : RExp X ≃ Tree X where
  toFun := toTree
  invFun := ofTree
  left_inv := ofTree_toTree
  right_inv := toTree_ofTree

section Prim

variable [Primcodable X]

/-- The arities are primitive recursive. -/
instance : Fact (Primrec (rexpAr (X := X))) := ⟨(Primrec.sumCasesOn Primrec.id
  ((Primrec.dom_finite fun i : Fin 5 =>
    if i.val = 2 ∨ i.val = 3 then 2 else if i.val = 4 then 1 else 0).comp₂ Primrec₂.right)
  ((Primrec.const 0).comp₂ Primrec₂.right)).of_eq fun x => by cases x <;> rfl⟩

/-- **Regular expressions are `Primcodable`**, through their trees. -/
instance primcodable : Primcodable (RExp X) := Primcodable.ofEquiv _ rexpEquiv

/-- `toTree` is primitive recursive. -/
theorem toTree_primrec : Primrec (toTree (X := X)) := Primrec.of_equiv (e := rexpEquiv)

/-- `ofTree` is primitive recursive. -/
theorem ofTree_primrec : Primrec (ofTree (X := X)) := Primrec.of_equiv_symm (e := rexpEquiv)

attribute [fun_prop] toTree_primrec ofTree_primrec

omit [Primcodable X] in
/-- A constructor through `mkOpt`: building the node, then reading it back. -/
theorem ofTree_mkOpt {a : Fin 5 ⊕ X} {l : List (Tree X)} (h : l.length = rexpAr a) :
    (mkOpt a l).map ofTree = some (ofTree (.node a fun i => l[i.val]'(by have := i.isLt; omega))) := by
  rw [mkOpt, dite_eq_left_of_eq_true (eq_true h)]
  rfl

/-- `plus` is primitive recursive. -/
theorem plus_primrec : Primrec₂ (plus : RExp X → RExp X → RExp X) := by
  have h : Primrec fun q : RExp X × RExp X =>
      ((mkOpt (.inl 2) [toTree q.1, toTree q.2]).map ofTree).getD zero := by fun_prop
  exact h.of_eq fun q => by
    rw [ofTree_mkOpt (by rfl)]
    simp [ofTree, ofTree_toTree]

/-- `mul` is primitive recursive. -/
theorem mul_primrec : Primrec₂ (mul : RExp X → RExp X → RExp X) := by
  have h : Primrec fun q : RExp X × RExp X =>
      ((mkOpt (.inl 3) [toTree q.1, toTree q.2]).map ofTree).getD zero := by fun_prop
  exact h.of_eq fun q => by
    rw [ofTree_mkOpt (by rfl)]
    simp [ofTree, ofTree_toTree]

/-- `star` is primitive recursive. -/
theorem star_primrec : Primrec (star : RExp X → RExp X) := by
  have h : Primrec fun e : RExp X => ((mkOpt (.inl 4) [toTree e]).map ofTree).getD zero := by
    fun_prop
  exact h.of_eq fun e => by
    rw [ofTree_mkOpt (by rfl)]
    simp [ofTree, ofTree_toTree]

/-- `sym` is primitive recursive. -/
theorem sym_primrec : Primrec (sym : X → RExp X) := by
  have h : Primrec fun x : X => ((mkOpt (.inr x) ([] : List (Tree X))).map ofTree).getD zero := by
    fun_prop
  exact h.of_eq fun x => by
    rw [ofTree_mkOpt (by rfl)]
    simp [ofTree]

@[fun_prop] theorem prim_plus {β : Type} [Primcodable β] {f g : β → RExp X} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => plus (f x) (g x) := plus_primrec.comp hf hg
@[fun_prop] theorem prim_mul {β : Type} [Primcodable β] {f g : β → RExp X} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => mul (f x) (g x) := mul_primrec.comp hf hg
@[fun_prop] theorem prim_star {β : Type} [Primcodable β] {f : β → RExp X} (hf : Primrec f) :
    Primrec fun x => star (f x) := star_primrec.comp hf
@[fun_prop] theorem prim_sym {β : Type} [Primcodable β] {f : β → X} (hf : Primrec f) :
    Primrec fun x => sym (f x) := sym_primrec.comp hf

end Prim

/-! ### The hand-made code `rc` is primitive recursive -/

/-- `symC` is primitive recursive. -/
theorem symC_primrec : Primrec symC := by
  have h : Primrec fun x : ℕ ⊕ ℕ => x.elim (fun a => 2 * a) (fun a => 2 * a + 1) := by fun_prop
  exact h.of_eq fun x => by cases x <;> rfl

/-- One step of `rc`, on a node with shape `s` and the codes `rs` of its children. -/
def rcStep (_ : Unit) (s : Fin 5 ⊕ (ℕ ⊕ ℕ)) (rs : List ℕ) : ℕ :=
  s.elim (fun i => if i.val = 0 then cz else if i.val = 1 then co
      else if i.val = 2 then cp rs.headI rs.tail.headI
      else if i.val = 3 then cm rs.headI rs.tail.headI else ct rs.headI)
    fun x => cs (symC x)

/-- `rc` is a fold over the tree of an expression. -/
theorem rc_eq_fold (e : RExp (ℕ ⊕ ℕ)) : rc e = fold rcStep () (toTree e) := by
  induction e with
  | zero => rfl
  | one => rfl
  | sym x => rfl
  | plus e f ihe ihf => simp [rc, toTree, fold, rcStep, ihe, ihf, List.ofFn, rexpAr, Fin.foldr_succ, Fin.foldr_zero]
  | mul e f ihe ihf => simp [rc, toTree, fold, rcStep, ihe, ihf, List.ofFn, rexpAr, Fin.foldr_succ, Fin.foldr_zero]
  | star e ih => simp [rc, toTree, fold, rcStep, ih, List.ofFn, rexpAr, Fin.foldr_succ, Fin.foldr_zero]

/-- **The hand-made code `rc` is primitive recursive** with respect to the `Primcodable` encoding
of expressions. -/
theorem rc_primrec : Primrec rc := by
  have hs : Primrec fun q : Unit × ((Fin 5 ⊕ (ℕ ⊕ ℕ)) × List ℕ) => rcStep q.1 q.2.1 q.2.2 := by
    have := symC_primrec
    unfold rcStep
    fun_prop
  exact (((fold_primrec hs).comp (Primrec.const ()) toTree_primrec)).of_eq fun e =>
    (rc_eq_fold e).symm

/-! ### Decoding `rc` codes -/

/-- The letter with code `p`: the inverse of `symC`. -/
def symDec (p : ℕ) : ℕ ⊕ ℕ := if p % 2 = 0 then .inl (p / 2) else .inr (p / 2)

theorem symDec_symC (x : ℕ ⊕ ℕ) : symDec (symC x) = x := by
  cases x <;> simp [symDec, symC]; omega

theorem symDec_primrec : Primrec symDec := by unfold symDec; fun_prop

/-- The second component of a code with a positive tag is smaller than the code. -/
theorem unpair_snd_lt {n : ℕ} (h : n.unpair.1 ≠ 0) : n.unpair.2 < n := by
  have := lt_of_le_of_lt (Nat.right_le_pair 0 n.unpair.2)
    (Nat.pair_lt_pair_left n.unpair.2 (Nat.pos_of_ne_zero h))
  rwa [Nat.pair_unpair] at this

/-- The child codes packed into an `rc` code. -/
def rcKids (n : ℕ) : List ℕ :=
  if n.unpair.1 = 3 ∨ n.unpair.1 = 4 then [n.unpair.2.unpair.1, n.unpair.2.unpair.2]
  else if n.unpair.1 = 5 then [n.unpair.2] else []

theorem rcKids_lt (n : ℕ) : ∀ m ∈ rcKids n, m < n := by
  intro m hm
  unfold rcKids at hm
  split_ifs at hm with h₁ h₂
  · have h : n.unpair.1 ≠ 0 := by omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt (unpair_snd_lt h)
    · exact (Nat.unpair_right_le _).trans_lt (unpair_snd_lt h)
  · simp only [List.mem_singleton] at hm
    exact hm ▸ unpair_snd_lt (by omega)
  · simp at hm

/-- One decoding step of `rc`: the node of code `n`, from its decoded children `ts`. -/
def rcBuild (n : ℕ) (ts : List (RExp (ℕ ⊕ ℕ))) : Option (RExp (ℕ ⊕ ℕ)) :=
  if n.unpair.1 = 0 then (if n.unpair.2 = 0 then some zero else none)
  else if n.unpair.1 = 1 then (if n.unpair.2 = 0 then some one else none)
  else if n.unpair.1 = 2 then some (sym (symDec n.unpair.2))
  else if n.unpair.1 = 3 then ts[0]?.elim none fun e => ts[1]?.elim none fun f => some (plus e f)
  else if n.unpair.1 = 4 then ts[0]?.elim none fun e => ts[1]?.elim none fun f => some (mul e f)
  else if n.unpair.1 = 5 then ts[0]?.elim none fun e => some (star e)
  else none

/-- `rc` decodes in one step from its children. -/
theorem rc_spec (e : RExp (ℕ ⊕ ℕ)) :
    ∃ ts, rcKids (rc e) = ts.map rc ∧ rcBuild (rc e) ts = some e := by
  cases e with
  | zero => exact ⟨[], by simp [rcKids, rc, cz], by simp [rcBuild, rc, cz]⟩
  | one => exact ⟨[], by simp [rcKids, rc, co], by simp [rcBuild, rc, co]⟩
  | sym x => exact ⟨[], by simp [rcKids, rc, cs], by simp [rcBuild, rc, cs, symDec_symC]⟩
  | plus e f => exact ⟨[e, f], by simp [rcKids, rc, cp], by simp [rcBuild, rc, cp, Option.elim]⟩
  | mul e f => exact ⟨[e, f], by simp [rcKids, rc, cm], by simp [rcBuild, rc, cm, Option.elim]⟩
  | star e => exact ⟨[e], by simp [rcKids, rc, ct], by simp [rcBuild, rc, ct, Option.elim]⟩

theorem rcKids_primrec : Primrec rcKids := by unfold rcKids; fun_prop

theorem rcBuild_primrec : Primrec fun q : ℕ × List (RExp (ℕ ⊕ ℕ)) => rcBuild q.1 q.2 := by
  have := symDec_primrec
  unfold rcBuild
  fun_prop

/-- The decoder of `rc`, from `TaggedCode`. -/
abbrev rcDec : ℕ → Option (RExp (ℕ ⊕ ℕ)) := TaggedCode.decode rcKids rcKids_lt rcBuild

/-- **`rcDec` decodes `rc`.** -/
theorem rcDec_rc (e : RExp (ℕ ⊕ ℕ)) : rcDec (rc e) = some e :=
  TaggedCode.decode_code rcKids rcKids_lt rcBuild rc_spec e

/-- **The decoder of `rc` is primitive recursive.** -/
theorem rcDec_primrec : Primrec rcDec :=
  TaggedCode.decode_primrec rcKids rcKids_lt rcBuild rcKids_primrec rcBuild_primrec

/-- **`rc` is a correct encoding.** A function into expressions is primitive recursive exactly
when it is so through `rc`: the hand-made code and the `Primcodable` encoding are primitive
recursively isomorphic. -/
theorem primrec_iff_rc {β : Type} [Primcodable β] {f : β → RExp (ℕ ⊕ ℕ)} :
    Primrec f ↔ Primrec fun b => rc (f b) :=
  TaggedCode.primrec_iff rcKids rcKids_lt rcBuild rc_spec rc_primrec rcKids_primrec rcBuild_primrec

end RExp

end DiagonaLean.KACommUndecidable.KleeneAlgebra
