/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Syntax
import DiagonaLean.KleeneAlgebra.SingleStep
import DiagonaLean.KleeneAlgebra.FiniteLangCounterexample

@[expose] public section

/-! # Repair of Theorem 6, Corollary 7 and Theorem 9

Theorem 6 fails at `1∗` (`FiniteLangCounterexample.lean`): its proof, by induction on terms, has no
valid star case. The repair restricts to **guarded** terms, where every starred subterm is
non-nullable (`[e]₀ = 0`). Then the star case goes through: if `e ≠ 0` and `ε ∉ l(e)`, the
language of `e∗` is infinite, and if `l(e) = ∅` then `e = 0` (Corollary 8) and `e∗ = 1`.

The restriction covers every use of Theorem 6 / Corollary 7 in the undecidability proof: those
are applied to finite sums of strings `Σ s`, which contain no star (`guarded_sumL_ofPair`).

We state the repair for the doubled alphabet `T Σ̈` with its language model `pl`, the setting in
which the paper uses these results.

## Main statements

* `TD.eq_sum_of_guarded_of_finite_lang`: a guarded term with finite language is the sum of the strings in its language.
* `TD.eq_of_guarded_of_lang_eq`: guarded terms with the same finite language are equal.
* `TD.mul_sigAll_kstar_le_of_guarded`: a guarded term `e` with finite language satisfies `e Σ̈∗ ≤ Σ̈∗`.
* `TD.guarded_one_kstar`: `1∗` is not guarded, so the counterexample is excluded.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 6,
  Corollary 7, Theorem 9
-/

open scoped Computability

namespace DiagonaLean.KAComm

namespace TD

open FreePreKA RExp

variable {A : Type*}

/-- The language of `e`, as a set of strings. -/
def lng (e : TD A) : Set (W A) := {s | SetSemiring.Mem s (pl e)}

/-- In an idempotent semiring, summing `g ∘ φ` over `U` is summing `g` over the image. -/
theorem sum_comp_eq_sum_image {ι κ : Type*} [DecidableEq κ] (U : Finset ι) (φ : ι → κ)
    (g : κ → TD A) : ∑ i ∈ U, g (φ i) = ∑ k ∈ U.image φ, g k := by
  refine le_antisymm (sum_le_of_forall _ _ fun i hi => le_sum_of_mem g (Finset.mem_image_of_mem φ hi))
    (sum_le_of_forall _ _ fun k hk => ?_)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hk
  exact le_sum_of_mem (fun i => g (φ i)) hi

theorem size_pow (s : W A) (n : ℕ) : size (s ^ n) = n * size s := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, size_mul, ih]; ring

theorem eq_zero_of_lng_eq_empty {e : TD A} (h : lng e = ∅) : e = 0 :=
  eq_zero_of_pl_eq_zero e fun s hs => (Set.eq_empty_iff_forall_notMem.1 h s) hs

/-- `1∗` is not guarded, so the counterexample to Theorem 6 is excluded. -/
theorem guarded_one_kstar : guarded (star one : RExp (A ⊕ A)) = false := rfl

/-- Finite sums of strings are guarded (they contain no star). -/
theorem guarded_sumL_ofPair (l : List (RExp (A ⊕ A))) (hl : ∀ r ∈ l, guarded r = true) :
    guarded (sumL l) = true := by
  simpa [List.all_eq_true] using hl

variable [DecidableEq A]

/-- **Theorem 6 (repaired).** A guarded term with a finite language is the sum of the strings in
its language. -/
theorem eq_sum_of_guarded_of_finite_lang (r : RExp (A ⊕ A)) (hg : guarded r = true) (hfin : (lng (mk r : TD A)).Finite) :
    (mk r : TD A) = ∑ s ∈ hfin.toFinset, ofPair s := by
  induction r with
  | zero =>
    have : hfin.toFinset = ∅ := by
      ext s; simp only [Set.Finite.mem_toFinset, Finset.notMem_empty, iff_false]
      exact SetSemiring.mem_zero s
    rw [this, Finset.sum_empty]; rfl
  | one =>
    have : hfin.toFinset = {1} := by
      ext s; simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]; rfl
    rw [this, Finset.sum_singleton, ofPair_one]; rfl
  | sym x =>
    have : hfin.toFinset = {letter x} := by
      ext s; simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
      rcases x with a | a <;> rfl
    rw [this, Finset.sum_singleton, ofPair_letter]; rfl
  | plus e f ihe ihf =>
    simp only [guarded, Bool.and_eq_true] at hg
    have hl : lng (mk (plus e f) : TD A) = lng (mk e) ∪ lng (mk f) := by
      ext s
      show SetSemiring.Mem s (pl (mk e + mk f)) ↔ _
      rw [pl_add, SetSemiring.mem_add]; rfl
    have hfe : (lng (mk e : TD A)).Finite := hfin.subset (hl ▸ Set.subset_union_left)
    have hff : (lng (mk f : TD A)).Finite := hfin.subset (hl ▸ Set.subset_union_right)
    have : hfin.toFinset = hfe.toFinset ∪ hff.toFinset := by
      ext s
      rw [Set.Finite.mem_toFinset, Finset.mem_union, Set.Finite.mem_toFinset,
        Set.Finite.mem_toFinset, hl, Set.mem_union]
    rw [this, sum_union_idem, mk_plus, ← ihe hg.1 hfe, ← ihf hg.2 hff]
  | mul e f ihe ihf =>
    simp only [guarded, Bool.and_eq_true] at hg
    by_cases he : lng (mk e : TD A) = ∅
    · have h0 : (mk (mul e f) : TD A) = 0 := by rw [mk_mul, eq_zero_of_lng_eq_empty he, zero_mul]
      have : hfin.toFinset = ∅ := by
        ext s; simp only [Set.Finite.mem_toFinset, Finset.notMem_empty, iff_false]
        rw [h0]; exact SetSemiring.mem_zero s
      rw [this, Finset.sum_empty, h0]
    by_cases hf : lng (mk f : TD A) = ∅
    · have h0 : (mk (mul e f) : TD A) = 0 := by rw [mk_mul, eq_zero_of_lng_eq_empty hf, mul_zero]
      have : hfin.toFinset = ∅ := by
        ext s; simp only [Set.Finite.mem_toFinset, Finset.notMem_empty, iff_false]
        rw [h0]; exact SetSemiring.mem_zero s
      rw [this, Finset.sum_empty, h0]
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 he
    obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 hf
    have hmem : ∀ x y, x ∈ lng (mk e : TD A) → y ∈ lng (mk f : TD A) →
        x * y ∈ lng (mk (mul e f) : TD A) := fun x y hx hy => by
      show SetSemiring.Mem _ _
      rw [mk_mul, pl_mul, SetSemiring.mem_mul]; exact ⟨x, hx, y, hy, rfl⟩
    have hfe : (lng (mk e : TD A)).Finite :=
      (hfin.preimage (mul_left_injective b).injOn).subset fun x hx => hmem x b hx hb
    have hff : (lng (mk f : TD A)).Finite :=
      (hfin.preimage (mul_right_injective a).injOn).subset fun y hy => hmem a y ha hy
    have himg : hfin.toFinset = (hfe.toFinset ×ˢ hff.toFinset).image fun p => p.1 * p.2 := by
      ext s
      rw [Set.Finite.mem_toFinset, Finset.mem_image]
      constructor
      · intro hs
        have : SetSemiring.Mem s (pl (mk e * mk f)) := hs
        rw [pl_mul, SetSemiring.mem_mul] at this
        obtain ⟨x, hx, y, hy, rfl⟩ := this
        exact ⟨(x, y), Finset.mem_product.2 ⟨hfe.mem_toFinset.2 hx, hff.mem_toFinset.2 hy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, hp, rfl⟩
        rw [Finset.mem_product] at hp
        exact hmem x y (hfe.mem_toFinset.1 hp.1) (hff.mem_toFinset.1 hp.2)
    rw [himg, ← sum_comp_eq_sum_image, Finset.sum_product, mk_mul]
    refine (congrArg₂ (· * ·) (ihe hg.1 hfe) (ihf hg.2 hff)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => (ofPair_mul x y).symm
  | star e ihe =>
    simp only [guarded, Bool.and_eq_true, Bool.not_eq_true'] at hg
    by_cases he : lng (mk e : TD A) = ∅
    · have h1 : (mk (star e) : TD A) = 1 := by
        rw [mk_star, eq_zero_of_lng_eq_empty he, kstar_unfold, zero_mul, add_zero]
      have : hfin.toFinset = {1} := by
        ext s; simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
        show SetSemiring.Mem s (pl (mk (star e))) ↔ _
        rw [h1]; rfl
      rw [this, Finset.sum_singleton, ofPair_one, h1]
    · exfalso
      obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.2 he
      have hs1 : s ≠ 1 := fun h => by
        have : Nullable (mk e : TD A) := by subst h; exact hs
        rw [nullable_mk, hg.1] at this
        exact Bool.false_ne_true this
      have hsize : 0 < size s := by
        by_contra h0
        exact hs1 (eq_one_of_size_eq_zero (by omega))
      refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => s ^ n) ?_ ?_ hfin
      · intro m n hmn
        have := congrArg size hmn
        simp only [size_pow] at this
        exact Nat.eq_of_mul_eq_mul_right hsize this
      · intro n
        show SetSemiring.Mem _ (pl (mk e)∗)
        rw [pl_kstar, SetSemiring.mem_kstar]
        exact ⟨List.replicate n s, fun y hy => (List.eq_of_mem_replicate hy) ▸ hs,
          List.prod_replicate n s⟩

/-- **Corollary 7 (repaired).** Guarded terms with the same finite language are equal. -/
theorem eq_of_guarded_of_lang_eq (r₁ r₂ : RExp (A ⊕ A)) (hg₁ : guarded r₁ = true) (hg₂ : guarded r₂ = true)
    (hfin : (lng (mk r₁ : TD A)).Finite) (h : lng (mk r₁ : TD A) = lng (mk r₂)) :
    (mk r₁ : TD A) = mk r₂ := by
  rw [eq_sum_of_guarded_of_finite_lang r₁ hg₁ hfin, eq_sum_of_guarded_of_finite_lang r₂ hg₂ (h ▸ hfin)]
  congr 1
  ext s; simp [h]

/-- **Theorem 9 (repaired).** A guarded term `e` with finite language satisfies `e Σ̈∗ ≤ Σ̈∗`. -/
theorem mul_sigAll_kstar_le_of_guarded [Fintype A] (r : RExp (A ⊕ A)) (hg : guarded r = true)
    (hfin : (lng (mk r : TD A)).Finite) : (mk r : TD A) * sigAll∗ ≤ sigAll∗ := by
  rw [eq_sum_of_guarded_of_finite_lang r hg hfin, Finset.sum_mul]
  exact sum_le_of_forall _ _ fun s _ => ofPair_mul_kstar_le s

end TD

end DiagonaLean.KAComm
