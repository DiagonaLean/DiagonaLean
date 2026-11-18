/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.CombinatoryLogic.Code
import DiagonaLean.Foundations.Computability.PolyTree
import DiagonaLean.Foundations.Computability.TaggedCode

@[expose] public section

/-! # SKI terms are `Primcodable`, and `skc` is a correct encoding

An SKI term is a tree with shapes `S`, `K`, `I` (no children) and application (two children):
`SKI ≃ PTree (Fin 4) skiAr` (`skiEquiv`), so `SKI` is `Primcodable` (Theorem A). The hand-made code
`skc` is primitive recursive (`skc_primrec`, as a fold) and decodes in one step from its children,
so it is a correct encoding (`primrec_iff_skc`, by `TaggedCode.primrec_iff`).
-/

namespace DiagonaLean.Foundations.CombinatoryLogic

open Cslib SKI DiagonaLean.Foundations.Computability PTree

/-- The arities: application has two children, `S`, `K`, `I` none. -/
def skiAr (i : Fin 4) : ℕ := if i.val = 3 then 2 else 0

instance : Fact (Primrec skiAr) := ⟨Primrec.dom_finite _⟩

/-- The tree of shapes of an SKI term. -/
abbrev SKITree := PTree (Fin 4) skiAr

/-- An SKI term as a tree. -/
def toTree : SKI → SKITree
  | S => .node 0 Fin.elim0
  | K => .node 1 Fin.elim0
  | I => .node 2 Fin.elim0
  | app x y => .node 3 fun i => if i.val = 0 then toTree x else toTree y

/-- A tree as an SKI term. -/
def ofTree : SKITree → SKI
  | .node ⟨0, _⟩ _ => S
  | .node ⟨1, _⟩ _ => K
  | .node ⟨2, _⟩ _ => I
  | .node ⟨3, _⟩ cs => app (ofTree (cs ⟨0, by simp [skiAr]⟩)) (ofTree (cs ⟨1, by simp [skiAr]⟩))

theorem ofTree_toTree (x : SKI) : ofTree (toTree x) = x := by
  induction x <;> simp_all [toTree, ofTree]

theorem toTree_ofTree (t : SKITree) : toTree (ofTree t) = t := by
  induction t with
  | node a cs ih =>
    rcases a with ⟨_ | _ | _ | _ | i, hi⟩
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩; simp at hj
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩; simp at hj
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩; simp at hj
    · simp only [ofTree, toTree]; congr 1; funext ⟨j, hj⟩
      rcases j with _ | _ | j
      · simp [ih]
      · simp [ih]
      · simp [skiAr] at hj; omega
    · omega

/-- SKI terms and their trees. -/
def skiEquiv : SKI ≃ SKITree where
  toFun := toTree
  invFun := ofTree
  left_inv := ofTree_toTree
  right_inv := toTree_ofTree

/-- **SKI terms are `Primcodable`**, through their trees. -/
instance primcodable : Primcodable SKI := Primcodable.ofEquiv _ skiEquiv

@[fun_prop] theorem toTree_primrec : Primrec toTree := Primrec.of_equiv (e := skiEquiv)
@[fun_prop] theorem ofTree_primrec : Primrec ofTree := Primrec.of_equiv_symm (e := skiEquiv)

/-- Application is primitive recursive. -/
theorem app_primrec : Primrec₂ app := by
  have h : Primrec fun q : SKI × SKI => ((mkOpt 3 [toTree q.1, toTree q.2]).map ofTree).getD S := by
    fun_prop
  exact h.of_eq fun q => by
    rw [mkOpt, dite_eq_left_of_eq_true (eq_true (by rfl))]
    simp [ofTree, ofTree_toTree]

@[fun_prop] theorem prim_app {β : Type} [Primcodable β] {f g : β → SKI} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => app (f x) (g x) := app_primrec.comp hf hg

/-! ### `skc` is a correct encoding -/

/-- One step of `skc`, on a node with shape `i` and the codes `rs` of its children. -/
def skcStep (_ : Unit) (i : Fin 4) (rs : List ℕ) : ℕ :=
  if i.val = 0 then cS else if i.val = 1 then cK else if i.val = 2 then cI
  else ca rs.headI rs.tail.headI

theorem skc_eq_fold (x : SKI) : skc x = fold skcStep () (toTree x) := by
  induction x with
  | S => rfl
  | K => rfl
  | I => rfl
  | app x y ihx ihy =>
    simp [skc, toTree, fold, skcStep, ihx, ihy, List.ofFn, skiAr, Fin.foldr_succ, Fin.foldr_zero]

/-- **`skc` is primitive recursive.** -/
theorem skc_primrec : Primrec skc := by
  have hs : Primrec fun q : Unit × (Fin 4 × List ℕ) => skcStep q.1 q.2.1 q.2.2 := by
    unfold skcStep; fun_prop
  exact ((fold_primrec hs).comp (Primrec.const ()) toTree_primrec).of_eq fun x =>
    (skc_eq_fold x).symm

/-- The child codes packed into an `skc` code. -/
def skcKids (n : ℕ) : List ℕ :=
  if n.unpair.1 = 3 then [n.unpair.2.unpair.1, n.unpair.2.unpair.2] else []

theorem skcKids_lt (n : ℕ) : ∀ m ∈ skcKids n, m < n := by
  intro m hm
  unfold skcKids at hm
  split_ifs at hm with h
  · have h' : n.unpair.1 ≠ 0 := by omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt (TaggedCode.unpair_snd_lt h')
    · exact (Nat.unpair_right_le _).trans_lt (TaggedCode.unpair_snd_lt h')
  · simp at hm

/-- One decoding step of `skc`. -/
def skcBuild (n : ℕ) (ts : List SKI) : Option SKI :=
  if n = cS then some S else if n = cK then some K else if n = cI then some I
  else if n.unpair.1 = 3 then ts[0]?.elim none fun x => ts[1]?.elim none fun y => some (app x y)
  else none

theorem skc_spec (x : SKI) : ∃ ts, skcKids (skc x) = ts.map skc ∧ skcBuild (skc x) ts = some x := by
  cases x with
  | S => exact ⟨[], by simp [skcKids, skc, cS], by simp [skcBuild, skc]⟩
  | K => exact ⟨[], by simp [skcKids, skc, cK], by simp [skcBuild, skc, cS, cK]⟩
  | I => exact ⟨[], by simp [skcKids, skc, cI], by simp [skcBuild, skc, cS, cK, cI]⟩
  | app x y => exact ⟨[x, y], by simp [skcKids, skc, ca],
      by simp [skcBuild, skc, ca, cS, cK, cI, Option.elim]⟩

theorem skcKids_primrec : Primrec skcKids := by unfold skcKids; fun_prop

theorem skcBuild_primrec : Primrec fun q : ℕ × List SKI => skcBuild q.1 q.2 := by
  unfold skcBuild; fun_prop

/-- **`skc` is a correct encoding.** A function into SKI terms is primitive recursive exactly when it
is so through `skc`. -/
theorem primrec_iff_skc {β : Type} [Primcodable β] {f : β → SKI} :
    Primrec f ↔ Primrec fun b => skc (f b) :=
  TaggedCode.primrec_iff skcKids skcKids_lt skcBuild skc_spec skc_primrec skcKids_primrec
    skcBuild_primrec

end DiagonaLean.Foundations.CombinatoryLogic
