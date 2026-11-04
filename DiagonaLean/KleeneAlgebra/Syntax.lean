/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Automata
import DiagonaLean.KleeneAlgebra.Expansion
import Mathlib.Logic.Encodable.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

/-! # Syntax-level constructions

The undecidability reduction (M7) must produce *syntax*: a pair of expressions computed from the
machine, not elements of the quotient `T Σ̈`. This file supplies the syntax-level tools.

* `RExp.nu`, `RExp.guarded`: syntactic nullability, and "every starred subterm is
  non-nullable". `nullable_mk` shows `nu` agrees with `Nullable`.
* `RExp.bnd`: a syntax-directed bound. For guarded `e`, `mk e` is finite-state with every state
  below `mk (bnd e)` (`finiteStateLe_mk`). This makes the residue of Lemma 34 an explicit term.
* `RExp.sumL`, `RExp.prodL`: finite sums and products of lists of expressions.
* `enumL`: a computable duplicate-free enumeration of a `Fintype` with an `Encodable` structure,
  so `Finset.univ` sums become `sumL`s.
* `RExp.map`: renaming the alphabet. Renaming along `Sum.map g g` preserves provability
  (`le_map`) and, for injective `g`, reflects inclusion in the language model (`pl_le_of_map`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Lemma 26
-/

open scoped Computability

namespace DiagonaLean.KAComm

namespace RExp

variable {X Y : Type*}

/-- Syntactic nullability. -/
def nu : RExp X → Bool
  | zero => false
  | one => true
  | sym _ => false
  | plus e f => nu e || nu f
  | mul e f => nu e && nu f
  | star _ => true

/-- Every starred subterm is non-nullable. -/
def guarded : RExp X → Bool
  | zero => true
  | one => true
  | sym _ => true
  | plus e f => guarded e && guarded f
  | mul e f => guarded e && guarded f
  | star e => !nu e && guarded e

/-- The syntax-directed bound on the states of the automaton of `e` (Lemma 26). -/
def bnd : RExp X → RExp X
  | zero => one
  | one => one
  | sym x => plus one (sym x)
  | plus e f => plus one (plus (bnd e) (bnd f))
  | mul e f => plus one (mul (bnd e) (bnd f))
  | star e => plus one (mul (bnd e) (star e))

/-- The sum of a list of expressions. -/
def sumL : List (RExp X) → RExp X
  | [] => zero
  | e :: l => plus e (sumL l)

/-- The product of a list of expressions. -/
def prodL : List (RExp X) → RExp X
  | [] => one
  | e :: l => mul e (prodL l)

/-- Renaming the alphabet. -/
def map (φ : X → Y) : RExp X → RExp Y
  | zero => zero
  | one => one
  | sym x => sym (φ x)
  | plus e f => plus (map φ e) (map φ f)
  | mul e f => mul (map φ e) (map φ f)
  | star e => star (map φ e)

@[simp] theorem nu_bnd (e : RExp X) : nu (bnd e) = true := by
  cases e <;> simp [bnd, nu]

@[simp] theorem nu_sumL (l : List (RExp X)) : nu (sumL l) = l.any nu := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [sumL, nu, ih]

@[simp] theorem guarded_sumL (l : List (RExp X)) : guarded (sumL l) = l.all guarded := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [sumL, guarded, ih]

@[simp] theorem guarded_prodL (l : List (RExp X)) : guarded (prodL l) = l.all guarded := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [prodL, guarded, ih]

/-- Renaming preserves provable equality, when it maps commuting pairs to commuting pairs. -/
theorem Equiv.map {C : X → X → Prop} {C' : Y → Y → Prop} (φ : X → Y)
    (hφ : ∀ x y, C x y → C' (φ x) (φ y)) {e f : RExp X} (h : Equiv C e f) :
    Equiv C' (e.map φ) (f.map φ) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | plus _ _ ih₁ ih₂ => exact .plus ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact .mul ih₁ ih₂
  | star _ ih => exact .star ih
  | plus_assoc => exact .plus_assoc _ _ _
  | plus_comm => exact .plus_comm _ _
  | zero_plus => exact .zero_plus _
  | plus_idem => exact .plus_idem _
  | mul_assoc => exact .mul_assoc _ _ _
  | one_mul => exact .one_mul _
  | mul_one => exact .mul_one _
  | zero_mul => exact .zero_mul _
  | mul_zero => exact .mul_zero _
  | left_distrib => exact .left_distrib _ _ _
  | right_distrib => exact .right_distrib _ _ _
  | unfold => exact .unfold _
  | comm hxy => exact .comm (hφ _ _ hxy)

end RExp

/-! ### Enumerating a finite encodable type -/

section enum

variable (α : Type*) [Fintype α] [Encodable α]

/-- The elements of `α`, without duplicates, in order of their codes. -/
def enumL : List α :=
  (List.range (Finset.univ.sup (Encodable.encode : α → ℕ) + 1)).filterMap (Encodable.decode₂ α)

variable {α}

theorem mem_enumL (a : α) : a ∈ enumL α := by
  simp only [enumL, List.mem_filterMap, List.mem_range]
  refine ⟨Encodable.encode a, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a)), ?_⟩
  exact Encodable.mem_decode₂.2 rfl

theorem nodup_enumL : (enumL α).Nodup := by
  refine List.nodup_range.filterMap fun n n' a h h' => ?_
  rw [Encodable.mem_decode₂] at h h'
  rw [← h, ← h']

theorem sum_enumL {β : Type*} [AddCommMonoid β] (g : α → β) :
    ((enumL α).map g).sum = ∑ a, g a := by
  classical
  rw [← List.sum_toFinset g nodup_enumL]
  congr 1
  ext a; simp [mem_enumL]

theorem sum_enumL_filter {β : Type*} [AddCommMonoid β] (p : α → Prop) [DecidablePred p]
    (g : α → β) : (((enumL α).filter p).map g).sum = ∑ a ∈ Finset.univ.filter p, g a := by
  classical
  rw [← List.sum_toFinset g (nodup_enumL.filter _)]
  congr 1
  ext a; simp [mem_enumL]

end enum

namespace FreePreKA

open RExp

variable {X : Type*} {C : X → X → Prop}

theorem mk_sumL (l : List (RExp X)) : (mk (sumL l) : FreePreKA X C) = (l.map mk).sum := by
  induction l with
  | nil => rfl
  | cons e l ih => rw [sumL, mk_plus, ih, List.map_cons, List.sum_cons]

theorem mk_prodL (l : List (RExp X)) : (mk (prodL l) : FreePreKA X C) = (l.map mk).prod := by
  induction l with
  | nil => rfl
  | cons e l ih => rw [prodL, mk_mul, ih, List.map_cons, List.prod_cons]

/-- `≤` in `FreePreKA` is provability of `e + f = f`. -/
theorem mk_le_mk {e f : RExp X} : (mk e : FreePreKA X C) ≤ mk f ↔ Equiv C (plus e f) f := by
  rw [← add_eq_right_iff_le, ← mk_plus, mk_eq_mk]

theorem mk_map_le_mk_map {Y : Type*} {C' : Y → Y → Prop} (φ : X → Y)
    (hφ : ∀ x y, C x y → C' (φ x) (φ y)) {e f : RExp X}
    (h : (mk e : FreePreKA X C) ≤ mk f) : (mk (e.map φ) : FreePreKA Y C') ≤ mk (f.map φ) :=
  mk_le_mk.2 ((mk_le_mk.1 h).map φ hφ)

end FreePreKA

namespace TD

open FreePreKA RExp

variable {A B : Type*}

/-! ### Nullability and the explicit bound -/

theorem nullable_mk (e : RExp (A ⊕ A)) : Nullable (mk e : TD A) ↔ nu e = true := by
  induction e with
  | zero => exact iff_of_false not_nullable_zero (by simp [nu])
  | one => exact iff_of_true nullable_one rfl
  | sym x => exact iff_of_false (not_nullable_of x) (by simp [nu])
  | plus e f ihe ihf => rw [mk_plus, nullable_add, ihe, ihf, nu, Bool.or_eq_true]
  | mul e f ihe ihf => rw [mk_mul, nullable_mul, ihe, ihf, nu, Bool.and_eq_true]
  | star e _ => rw [mk_star, nu]; exact iff_of_true (nullable_kstar _) rfl

variable [Fintype A]

/-- For guarded `e`, `mk e` is finite-state, with every state below `mk (bnd e)`. -/
theorem finiteStateLe_mk (e : RExp (A ⊕ A)) (hg : guarded e = true) :
    FiniteStateLe (mk e : TD A) (mk (bnd e)) := by
  induction e with
  | zero => exact FiniteStateLe.zero
  | one => exact FiniteStateLe.one
  | sym x => exact FiniteStateLe.of x
  | plus e f ihe ihf =>
    simp only [guarded, Bool.and_eq_true] at hg
    exact (ihe hg.1).add (ihf hg.2)
  | mul e f ihe ihf =>
    simp only [guarded, Bool.and_eq_true] at hg
    exact (ihe hg.1).mul (ihf hg.2)
  | star e ihe =>
    simp only [guarded, Bool.and_eq_true, Bool.not_eq_true'] at hg
    refine (ihe hg.2).kstar fun h => ?_
    rw [nullable_mk, hg.1] at h
    exact Bool.false_ne_true h

omit [Fintype A]

/-! ### Renaming and the language model -/

/-- Renaming letters of a doubled alphabet. -/
abbrev dmap (g : A → B) : A ⊕ A → B ⊕ B := Sum.map g g

theorem dComm_dmap (g : A → B) : ∀ x y, DComm x y → DComm (dmap g x) (dmap g y)
  | .inl _, .inr _, _ => trivial
  | .inr _, .inl _, _ => trivial

/-- Renaming strings of `Σ̈`. -/
def wmap (g : A → B) : W A →* W B :=
  MonoidHom.prodMap (FreeMonoid.map g) (FreeMonoid.map g)

theorem wmap_injective {g : A → B} (hg : Function.Injective g) :
    Function.Injective (wmap g) := by
  have h : Function.Injective (FreeMonoid.map g) := fun u v huv => by
    have := congrArg FreeMonoid.toList huv
    simp only [FreeMonoid.toList_map] at this
    exact FreeMonoid.toList.injective ((List.map_injective_iff.2 hg) this)
  exact Prod.map_injective.2 ⟨h, h⟩

/-- The language of a renamed expression is the image of the language. -/
theorem mem_pl_map (g : A → B) (e : RExp (A ⊕ A)) (y : W B) :
    SetSemiring.Mem y (pl (mk (e.map (dmap g)))) ↔
      ∃ x, SetSemiring.Mem x (pl (mk e)) ∧ wmap g x = y := by
  induction e generalizing y with
  | zero =>
    simp only [RExp.map, mk_zero, pl_zero]
    exact iff_of_false (SetSemiring.mem_zero y) fun ⟨x, hx, _⟩ => SetSemiring.mem_zero x hx
  | one =>
    simp only [RExp.map, mk_one, pl_one, SetSemiring.mem_one]
    exact ⟨fun h => ⟨1, rfl, by rw [map_one, h]⟩, fun ⟨x, hx, h⟩ => by rw [← h, hx, map_one]⟩
  | sym x =>
    rcases x with a | a
    · change SetSemiring.Mem y (gen (dmap g (Sum.inl a))) ↔
        ∃ x, SetSemiring.Mem x (gen (Sum.inl a)) ∧ wmap g x = y
      simp only [gen, mem_single, dmap, Sum.map_inl, exists_eq_left]
      simp [wmap, eq_comm]
    · change SetSemiring.Mem y (gen (dmap g (Sum.inr a))) ↔
        ∃ x, SetSemiring.Mem x (gen (Sum.inr a)) ∧ wmap g x = y
      simp only [gen, mem_single, dmap, Sum.map_inr, exists_eq_left]
      simp [wmap, eq_comm]
  | plus e f ihe ihf =>
    simp only [RExp.map, mk_plus, pl_add, SetSemiring.mem_add, ihe, ihf]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      exacts [⟨x, Or.inl hx, rfl⟩, ⟨x, Or.inr hx, rfl⟩]
    · rintro ⟨x, hx | hx, rfl⟩
      exacts [Or.inl ⟨x, hx, rfl⟩, Or.inr ⟨x, hx, rfl⟩]
  | mul e f ihe ihf =>
    simp only [RExp.map, mk_mul, pl_mul, SetSemiring.mem_mul, ihe, ihf]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, map_mul _ _ _⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, (map_mul _ _ _).symm⟩
  | star e ihe =>
    simp only [RExp.map, mk_star, pl_kstar, SetSemiring.mem_kstar]
    constructor
    · rintro ⟨l, hl, rfl⟩
      induction l with
      | nil => exact ⟨1, ⟨[], by simp, rfl⟩, by simp⟩
      | cons z l ih =>
        obtain ⟨x, hx, rfl⟩ := (ihe z).1 (hl z (by simp))
        obtain ⟨x', ⟨l', hl', rfl⟩, hx'⟩ := ih fun y hy => hl y (by simp [hy])
        refine ⟨x * l'.prod, ⟨x :: l', ?_, List.prod_cons⟩, ?_⟩
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          exacts [hx, hl' y hy]
        · rw [map_mul, hx', List.prod_cons]
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨l.map (wmap g), fun y hy => ?_, (map_list_prod _ _).symm⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact (ihe _).2 ⟨x, hl x hx, rfl⟩

/-- Renaming along an injective map reflects inclusion in the language model. -/
theorem pl_le_of_map {g : A → B} (hg : Function.Injective g) {e f : RExp (A ⊕ A)}
    (h : pl (mk (e.map (dmap g))) ≤ pl (mk (f.map (dmap g)))) : pl (mk e) ≤ pl (mk f) := by
  intro x hx
  obtain ⟨x', hx', he⟩ := (mem_pl_map g f _).1 (h ((mem_pl_map g e _).2 ⟨x, hx, rfl⟩))
  rwa [← wmap_injective hg he]

/-- Renaming preserves inclusion in the language model. -/
theorem pl_map_le_of_le (g : A → B) {e f : RExp (A ⊕ A)} (h : pl (mk e) ≤ pl (mk f)) :
    pl (mk (e.map (dmap g))) ≤ pl (mk (f.map (dmap g))) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_pl_map g e y).1 hy
  exact (mem_pl_map g f _).2 ⟨x, h hx, rfl⟩

/-- Renaming preserves provable inclusion. -/
theorem le_map (g : A → B) {e f : RExp (A ⊕ A)} (h : (mk e : TD A) ≤ mk f) :
    (mk (e.map (dmap g)) : TD B) ≤ mk (f.map (dmap g)) :=
  mk_map_le_mk_map _ (dComm_dmap g) h

end TD

end DiagonaLean.KAComm
