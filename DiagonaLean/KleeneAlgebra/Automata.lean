/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Doubled
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.NAry
import Mathlib.Tactic.Abel

@[expose] public section

/-! # Derivatives and finite-state terms (§5.1, Lemmas 24 and 26)

Without the induction axioms, derivatives exist only for some terms. A term is *derivable*
(Def 23) when it can be written `e = [e]₀ + Σₓ x δₓ(e)`; a *finite-state automaton* (Def 25) is a
finite set of terms containing `1`, closed under sums, whose elements have derivatives inside it.

## Design

* "Closed under finite sums" is stated as `0 ∈ S` plus closure under `+`; `IsAutomaton.sum_mem`
  recovers finite sums.
* Each closure case of Lemma 26 builds a *pre-automaton* `P` (derivatives are sums of elements of
  `P ∪ {1}`) and closes it under sums with `cl P` (`IsAutomaton.cl`), as in the paper's `S̄`.
* Derivative formulas of Lemma 24 are the `HasDerivs.*` lemmas.

## Main statements

* `TD.HasDerivs`: Definition 23 with a chosen family of derivatives.
* `TD.IsAutomaton`, `TD.FiniteState`: Definition 25.
* `TD.FiniteState.zero/one/of/add/mul/kstar`: Lemma 26 (the effectivity claim is not formalized).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Def 23, Lemma 24,
  Def 25, Lemma 26
-/

open scoped Computability

namespace DiagonaLean.KAComm

namespace TD

open FreePreKA Classical

variable {A : Type*}

/-! ### Facts about `[−]₀` -/

theorem nul_zero : nul (0 : TD A) = 0 := by
  unfold nul; rw [ite_eq_right not_nullable_zero]

theorem nul_one : nul (1 : TD A) = 1 := by
  unfold nul; rw [ite_eq_left nullable_one]

theorem nul_of (x : A ⊕ A) : nul (of x : TD A) = 0 := by
  unfold nul; rw [ite_eq_right (not_nullable_of x)]

theorem nul_kstar (e : TD A) : nul e∗ = 1 := by
  unfold nul; rw [ite_eq_left (nullable_kstar e)]

theorem nul_eq_zero_of_not {e : TD A} (h : ¬ Nullable e) : nul e = 0 := by
  unfold nul; rw [ite_eq_right h]

theorem nul_eq_zero_or_one (e : TD A) : nul e = 0 ∨ nul e = 1 := by
  unfold nul; split_ifs <;> simp

variable [Fintype A]

/-- Definition 23: `δ` is a family of derivatives of `e`, i.e. `e = [e]₀ + Σₓ x δₓ`. -/
def HasDerivs (e : TD A) (δ : A ⊕ A → TD A) : Prop := e = nul e + ∑ x, of x * δ x

/-! ### Lemma 24: derivative formulas -/

theorem hasDerivs_zero : HasDerivs (0 : TD A) 0 := by
  simp [HasDerivs, nul_zero]

theorem hasDerivs_one : HasDerivs (1 : TD A) 0 := by
  simp [HasDerivs, nul_one]

theorem hasDerivs_of (y : A ⊕ A) : HasDerivs (of y : TD A) (fun x => if x = y then 1 else 0) := by
  simp only [HasDerivs, nul_of, zero_add, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem HasDerivs.add {a b : TD A} {δa δb : A ⊕ A → TD A} (ha : HasDerivs a δa)
    (hb : HasDerivs b δb) : HasDerivs (a + b) (δa + δb) := by
  unfold HasDerivs at *
  calc a + b = (nul a + ∑ x, of x * δa x) + (nul b + ∑ x, of x * δb x) := by rw [← ha, ← hb]
    _ = nul (a + b) + ∑ x, of x * (δa + δb) x := by
      simp only [nul_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]; abel

theorem HasDerivs.mul {a b : TD A} {δa δb : A ⊕ A → TD A} (ha : HasDerivs a δa)
    (hb : HasDerivs b δb) : HasDerivs (a * b) (fun x => nul a * δb x + δa x * b) := by
  unfold HasDerivs at *
  have hnb : nul a * b = nul a * nul b + ∑ x, of x * (nul a * δb x) := by
    conv_lhs => rw [hb]
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← mul_assoc, (nul_commute a (of x)).eq, mul_assoc]
  calc a * b = nul a * b + ∑ x, of x * (δa x * b) := by
        conv_lhs => rw [ha]
        rw [add_mul, Finset.sum_mul]
        simp only [mul_assoc]
    _ = nul (a * b) + ∑ x, of x * (nul a * δb x + δa x * b) := by
        rw [hnb, nul_mul]
        simp only [mul_add, Finset.sum_add_distrib]
        abel

theorem HasDerivs.kstar {e : TD A} {δ : A ⊕ A → TD A} (he : HasDerivs e δ) (h0 : ¬ Nullable e) :
    HasDerivs e∗ (fun x => δ x * e∗) := by
  unfold HasDerivs at *
  rw [nul_kstar]
  conv_lhs => rw [kstar_unfold]
  congr 1
  rw [show e * e∗ = (nul e + ∑ x, of x * δ x) * e∗ from congrArg (· * e∗) he,
    nul_eq_zero_of_not h0, zero_add, Finset.sum_mul]
  simp only [mul_assoc]

/-! ### Automata -/

/-- Definition 25: a finite-state automaton. -/
structure IsAutomaton (S : Finset (TD A)) : Prop where
  one_mem : 1 ∈ S
  zero_mem : 0 ∈ S
  add_mem : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S
  deriv : ∀ e ∈ S, ∃ δ : A ⊕ A → TD A, (∀ x, δ x ∈ S) ∧ HasDerivs e δ

/-- `e` is a state of some finite-state automaton. -/
def FiniteState (e : TD A) : Prop := ∃ S : Finset (TD A), IsAutomaton S ∧ e ∈ S

namespace IsAutomaton

variable {S : Finset (TD A)} (hS : IsAutomaton S)
include hS

theorem sum_mem {ι : Type*} (T : Finset ι) (f : ι → TD A) (hf : ∀ i ∈ T, f i ∈ S) :
    ∑ i ∈ T, f i ∈ S := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hS.zero_mem
  | insert i T hi ih =>
    rw [Finset.sum_insert hi]
    exact hS.add_mem _ (hf i (by simp)) _ (ih fun j hj => hf j (by simp [hj]))

theorem nul_mem (e : TD A) : nul e ∈ S := by
  rcases nul_eq_zero_or_one e with h | h <;> rw [h]
  exacts [hS.zero_mem, hS.one_mem]

theorem nul_mul_mem (e : TD A) {a : TD A} (ha : a ∈ S) : nul e * a ∈ S := by
  rcases nul_eq_zero_or_one e with h | h <;> rw [h]
  exacts [by rw [zero_mul]; exact hS.zero_mem, by rw [one_mul]; exact ha]

end IsAutomaton

/-- The sum closure `S̄` of `P ∪ {1}`. -/
noncomputable def cl (P : Finset (TD A)) : Finset (TD A) :=
  (insert 1 P).powerset.image fun U => ∑ u ∈ U, u

omit [Fintype A] in
theorem sum_union_idem {ι : Type*} [DecidableEq ι] (U V : Finset ι) (f : ι → TD A) :
    ∑ i ∈ U ∪ V, f i = ∑ i ∈ U, f i + ∑ i ∈ V, f i := by
  rw [← Finset.sum_union_inter]
  refine le_antisymm (le_add_right le_rfl) (add_le le_rfl ?_)
  exact sum_le_of_forall _ _ fun i hi =>
    le_sum_of_mem f (Finset.mem_union_left V (Finset.mem_inter.1 hi).1)

omit [Fintype A] in
theorem mem_cl_iff {P : Finset (TD A)} {e : TD A} :
    e ∈ cl P ↔ ∃ U ⊆ insert 1 P, ∑ u ∈ U, u = e := by
  simp [cl]

omit [Fintype A] in
theorem mem_cl_of_mem {P : Finset (TD A)} {e : TD A} (h : e ∈ P) : e ∈ cl P :=
  mem_cl_iff.2 ⟨{e}, by simp [h], Finset.sum_singleton _ _⟩

omit [Fintype A] in
theorem one_mem_cl (P : Finset (TD A)) : 1 ∈ cl P :=
  mem_cl_iff.2 ⟨{1}, by simp, Finset.sum_singleton _ _⟩

omit [Fintype A] in
theorem zero_mem_cl (P : Finset (TD A)) : 0 ∈ cl P :=
  mem_cl_iff.2 ⟨∅, Finset.empty_subset _, Finset.sum_empty⟩

omit [Fintype A] in
theorem add_mem_cl {P : Finset (TD A)} {a b : TD A} (ha : a ∈ cl P) (hb : b ∈ cl P) :
    a + b ∈ cl P := by
  obtain ⟨U, hU, rfl⟩ := mem_cl_iff.1 ha
  obtain ⟨V, hV, rfl⟩ := mem_cl_iff.1 hb
  exact mem_cl_iff.2 ⟨U ∪ V, Finset.union_subset hU hV, sum_union_idem U V id⟩

omit [Fintype A] in
theorem sum_mem_cl {P : Finset (TD A)} {ι : Type*} (T : Finset ι) (f : ι → TD A)
    (hf : ∀ i ∈ T, f i ∈ cl P) : ∑ i ∈ T, f i ∈ cl P := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact zero_mem_cl P
  | insert i T hi ih =>
    rw [Finset.sum_insert hi]
    exact add_mem_cl (hf i (by simp)) (ih fun j hj => hf j (by simp [hj]))

/-- A pre-automaton: every element has derivatives that are sums of elements of `P ∪ {1}`. -/
def IsPreAutomaton (P : Finset (TD A)) : Prop :=
  ∀ e ∈ P, ∃ δ : A ⊕ A → TD A, (∀ x, δ x ∈ cl P) ∧ HasDerivs e δ

theorem hasDerivs_sum {ι : Type*} (T : Finset ι) (f : ι → TD A) (δ : ι → A ⊕ A → TD A)
    (h : ∀ i ∈ T, HasDerivs (f i) (δ i)) :
    HasDerivs (∑ i ∈ T, f i) (fun x => ∑ i ∈ T, δ i x) := by
  induction T using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hasDerivs_zero
  | insert i T hi ih =>
    have := (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))
    rw [Finset.sum_insert hi]
    convert this using 1
    funext x
    rw [Finset.sum_insert hi]; rfl

/-- The sum closure of a pre-automaton is an automaton. -/
theorem IsPreAutomaton.cl {P : Finset (TD A)} (hP : IsPreAutomaton P) : IsAutomaton (cl P) where
  one_mem := one_mem_cl P
  zero_mem := zero_mem_cl P
  add_mem _ ha _ hb := add_mem_cl ha hb
  deriv e he := by
    obtain ⟨U, hU, rfl⟩ := mem_cl_iff.1 he
    have hd : ∀ u ∈ insert 1 P, ∃ δ : A ⊕ A → TD A, (∀ x, δ x ∈ TD.cl P) ∧ HasDerivs u δ := by
      intro u hu
      by_cases huP : u ∈ P
      · exact hP u huP
      · rw [Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · exact ⟨0, fun _ => zero_mem_cl P, hasDerivs_one⟩
        · exact absurd hu huP
    choose! δ hδS hδ using hd
    exact ⟨fun x => ∑ u ∈ U, δ u x,
      fun x => sum_mem_cl U _ fun u hu => hδS u (hU hu) x,
      hasDerivs_sum U id δ fun u hu => hδ u (hU hu)⟩

/-! ### Lemma 26: closure of finite-state terms -/

namespace FiniteState

theorem of_preAutomaton {P : Finset (TD A)} (hP : IsPreAutomaton P) {e : TD A} (he : e ∈ P) :
    FiniteState e :=
  ⟨cl P, hP.cl, mem_cl_of_mem he⟩

theorem one : FiniteState (1 : TD A) :=
  ⟨cl ∅, IsPreAutomaton.cl (fun _ h => absurd h (Finset.notMem_empty _)), one_mem_cl ∅⟩

theorem zero : FiniteState (0 : TD A) :=
  ⟨cl ∅, IsPreAutomaton.cl (fun _ h => absurd h (Finset.notMem_empty _)), zero_mem_cl ∅⟩

theorem of (y : A ⊕ A) : FiniteState (FreePreKA.of y : TD A) := by
  refine of_preAutomaton (P := {FreePreKA.of y}) ?_ (Finset.mem_singleton_self _)
  intro e he
  rw [Finset.mem_singleton] at he
  subst he
  refine ⟨_, fun x => ?_, hasDerivs_of y⟩
  split_ifs
  exacts [one_mem_cl _, zero_mem_cl _]

theorem add {a b : TD A} (ha : FiniteState a) (hb : FiniteState b) : FiniteState (a + b) := by
  obtain ⟨S₁, h₁, ha⟩ := ha
  obtain ⟨S₂, h₂, hb⟩ := hb
  refine of_preAutomaton (P := Finset.image₂ (· + ·) S₁ S₂) ?_ (Finset.mem_image₂_of_mem ha hb)
  intro e he
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Finset.mem_image₂.1 he
  obtain ⟨δ₁, hδ₁, hd₁⟩ := h₁.deriv e₁ he₁
  obtain ⟨δ₂, hδ₂, hd₂⟩ := h₂.deriv e₂ he₂
  exact ⟨δ₁ + δ₂, fun x => mem_cl_of_mem (Finset.mem_image₂_of_mem (hδ₁ x) (hδ₂ x)),
    hd₁.add hd₂⟩

theorem mul {a b : TD A} (ha : FiniteState a) (hb : FiniteState b) : FiniteState (a * b) := by
  obtain ⟨S₁, h₁, ha⟩ := ha
  obtain ⟨S₂, h₂, hb⟩ := hb
  refine of_preAutomaton (P := Finset.image₂ (· * ·) S₁ S₂) ?_ (Finset.mem_image₂_of_mem ha hb)
  intro e he
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Finset.mem_image₂.1 he
  obtain ⟨δ₁, hδ₁, hd₁⟩ := h₁.deriv e₁ he₁
  obtain ⟨δ₂, hδ₂, hd₂⟩ := h₂.deriv e₂ he₂
  refine ⟨_, fun x => add_mem_cl ?_ ?_, hd₁.mul hd₂⟩
  · exact mem_cl_of_mem (Finset.mem_image₂_of_mem (h₁.nul_mem e₁) (hδ₂ x))
  · exact mem_cl_of_mem (Finset.mem_image₂_of_mem (hδ₁ x) he₂)

theorem kstar {e : TD A} (he : FiniteState e) (h0 : ¬ Nullable e) : FiniteState e∗ := by
  obtain ⟨S, hS, heS⟩ := he
  obtain ⟨δ, hδS, hδ⟩ := hS.deriv e heS
  have hstar := hδ.kstar h0
  refine of_preAutomaton (P := S.image (· * e∗)) ?_ (Finset.mem_image.2 ⟨1, hS.one_mem, one_mul _⟩)
  intro p hp
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨δ', hδ'S, hδ'⟩ := hS.deriv e' he'
  refine ⟨_, fun x => add_mem_cl ?_ ?_, hδ'.mul hstar⟩
  · rw [← mul_assoc]
    exact mem_cl_of_mem (Finset.mem_image.2 ⟨_, hS.nul_mul_mem e' (hδS x), rfl⟩)
  · exact mem_cl_of_mem (Finset.mem_image.2 ⟨_, hδ'S x, rfl⟩)

end FiniteState

end TD

end DiagonaLean.KAComm
