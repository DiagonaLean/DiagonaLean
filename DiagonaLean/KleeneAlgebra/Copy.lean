/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Representable
import DiagonaLean.KleeneAlgebra.Expansion

@[expose] public section

/-! # Copy terms and language computations

Building blocks for transition terms of machines: `cpf f = Σₒ (f o)_l (f o)_r` copies one letter
from a family `f`, and `(cpf f)∗` copies a whole word over it. This file computes the languages
of products of such terms with strings, and shows that these building blocks are finite state.

## Main statements

* `TD.mem_cpf_star`: `l((cpf f)∗) = {(w, w) | w ∈ (range f)∗}`.
* `TD.mem_mul_ofPair`, `TD.mem_mul_cpf_star`: languages of right products.
* `TD.FiniteState.ofPair`, `TD.FiniteState.sum`, `TD.FiniteState.cpf_star`.
* `TD.list_prod_le_kstar`: a product of elements below `x` is below `x∗`.
-/

open scoped Computability

namespace DiagonaLean.KAComm

namespace TD

open FreePreKA Classical

variable {A : Type*}

theorem mem_ofPair (p s : W A) : SetSemiring.Mem s (pl (ofPair p)) ↔ s = p := by
  rw [pl_ofPair, mem_single]

theorem mem_mul_ofPair (e : TD A) (q s : W A) :
    SetSemiring.Mem s (pl (e * ofPair q)) ↔ ∃ w, SetSemiring.Mem w (pl e) ∧ s = w * q := by
  rw [pl_mul, SetSemiring.mem_mul]
  constructor
  · rintro ⟨w, hw, q', hq', rfl⟩
    rw [mem_ofPair] at hq'
    exact ⟨w, hw, by rw [hq']⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, q, (mem_ofPair q q).2 rfl, rfl⟩

theorem list_prod_le_kstar [PreKleeneAlgebra α] (x : α) (l : List α) (h : ∀ a ∈ l, a ≤ x) :
    l.prod ≤ x∗ :=
  (mul_one _).symm.le.trans ((mul_le_mul' le_rfl (one_le_kstar' x)).trans
    (list_prod_mul_kstar_le x l h))

variable {ι : Type*} [Fintype ι]

/-- Copy one letter from the family `f`: `Σₒ (f o)_l (f o)_r`. -/
noncomputable def cpf (f : ι → A) : TD A := ∑ o, dg (FreeMonoid.of (f o))

theorem mem_cpf (f : ι → A) (s : W A) :
    SetSemiring.Mem s (pl (cpf f)) ↔ ∃ o, s = (FreeMonoid.of (f o), FreeMonoid.of (f o)) := by
  rw [cpf, mem_pl_sum]
  simp only [Finset.mem_univ, true_and, dg, mem_ofPair]

/-- The language of `(cpf f)∗`: copies of words over the range of `f`. -/
theorem mem_cpf_star (f : ι → A) (s : W A) :
    SetSemiring.Mem s (pl (cpf f)∗) ↔
      ∃ c : List ι, s = (FreeMonoid.ofList (c.map f), FreeMonoid.ofList (c.map f)) := by
  rw [pl_kstar, SetSemiring.mem_kstar]
  constructor
  · rintro ⟨l, hl, rfl⟩
    induction l with
    | nil => exact ⟨[], rfl⟩
    | cons y l ih =>
      obtain ⟨o, hyo⟩ := (mem_cpf f y).1 (hl y List.mem_cons_self)
      obtain ⟨c, hc⟩ := ih fun z hz => hl z (List.mem_cons_of_mem _ hz)
      refine ⟨o :: c, ?_⟩
      rw [List.prod_cons, hyo, hc]
      rfl
  · rintro ⟨c, rfl⟩
    refine ⟨c.map fun o => (FreeMonoid.of (f o), FreeMonoid.of (f o)), ?_, ?_⟩
    · intro y hy
      obtain ⟨o, -, rfl⟩ := List.mem_map.1 hy
      exact (mem_cpf f _).2 ⟨o, rfl⟩
    · induction c with
      | nil => rfl
      | cons o c ih => rw [List.map_cons, List.prod_cons, ih]; rfl

theorem mem_mul_cpf_star (e : TD A) (f : ι → A) (s : W A) :
    SetSemiring.Mem s (pl (e * (cpf f)∗)) ↔ ∃ w, ∃ c : List ι, SetSemiring.Mem w (pl e) ∧
      s = w * (FreeMonoid.ofList (c.map f), FreeMonoid.ofList (c.map f)) := by
  rw [pl_mul, SetSemiring.mem_mul]
  constructor
  · rintro ⟨w, hw, k, hk, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_cpf_star f k).1 hk
    exact ⟨w, c, hw, rfl⟩
  · rintro ⟨w, c, hw, rfl⟩
    exact ⟨w, hw, _, (mem_cpf_star f _).2 ⟨c, rfl⟩, rfl⟩

theorem not_nullable_cpf (f : ι → A) : ¬ Nullable (cpf f) := fun h => by
  obtain ⟨o, ho⟩ := (mem_cpf f 1).1 h
  exact FreeMonoid.of_ne_one (f o) (congrArg Prod.fst ho).symm

/-! ### Finite-state building blocks -/

variable [Fintype A]

theorem FiniteState.L (u : FreeMonoid A) : FiniteState (L u) := by
  induction u using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact FiniteState.one
  | of_mul a u ih => rw [map_mul, L_of]; exact (FiniteState.of _).mul ih

theorem FiniteState.R (v : FreeMonoid A) : FiniteState (R v) := by
  induction v using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact FiniteState.one
  | of_mul a v ih => rw [map_mul, R_of]; exact (FiniteState.of _).mul ih

theorem FiniteState.ofPair (t : W A) : FiniteState (ofPair t) :=
  (FiniteState.L t.1).mul (FiniteState.R t.2)

theorem FiniteState.sum {κ : Type*} (T : Finset κ) (g : κ → TD A)
    (h : ∀ i ∈ T, FiniteState (g i)) : FiniteState (∑ i ∈ T, g i) := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact FiniteState.zero
  | insert i T hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

theorem FiniteState.cpf_star (f : ι → A) : FiniteState (cpf f)∗ :=
  (FiniteState.sum _ _ fun _ _ => FiniteState.ofPair _).kstar (not_nullable_cpf f)

end TD

end DiagonaLean.KAComm
