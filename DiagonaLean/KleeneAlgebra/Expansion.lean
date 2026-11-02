/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Automata
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

/-! # The expansion lemma (Lemma 27)

A state `e` of a finite-state automaton `S` can be unfolded `k` times:
`e = Σ {s | s ≤ e, |s| < k} + Σ_{|s| = k} s eₛ` with every `eₛ ∈ S`.

## Design

The paper sums over *all* strings of size `k`. We sum over a finite set `T` of strings of size
`k` (those reachable by `k` derivative steps); taking `eₛ = 0` off `T` gives the paper's form.
This avoids enumerating all strings of a given size.

The step "`[eₛ]₀ = 1` iff `s ≤ e`" is the paper's language argument: a string of size `k` can only
come from the middle summand. It is `mem_iff` in the proof below, via Theorem 5.

## Main statements

* `TD.letter`, `TD.ofPair_letter`: one-symbol strings.
* `TD.mem_pl_sum`: membership in the language of a finite sum.
* `TD.IsAutomaton.expansion`: Lemma 27.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Lemma 27
-/

open scoped Computability

namespace DiagonaLean.KAComm

namespace TD

open FreePreKA Classical

variable {A : Type*}

/-- The one-symbol string `x`. -/
def letter : A ⊕ A → W A
  | .inl a => (FreeMonoid.of a, 1)
  | .inr a => (1, FreeMonoid.of a)

theorem ofPair_letter : ∀ x : A ⊕ A, ofPair (letter x) = of x
  | .inl a => by simp [ofPair, letter]
  | .inr a => by simp [ofPair, letter]

theorem size_letter : ∀ x : A ⊕ A, size (letter x) = 1
  | .inl _ => rfl
  | .inr _ => rfl

theorem eq_one_of_size_eq_zero {s : W A} (h : size s = 0) : s = 1 := by
  unfold size at h
  exact Prod.ext (FreeMonoid.length_eq_zero.1 (by omega)) (FreeMonoid.length_eq_zero.1 (by omega))

theorem mem_pl_sum {ι : Type*} (T : Finset ι) (f : ι → TD A) (s : W A) :
    SetSemiring.Mem s (pl (∑ i ∈ T, f i)) ↔ ∃ i ∈ T, SetSemiring.Mem s (pl (f i)) := by
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, pl_zero, Finset.notMem_empty, false_and, exists_false,
      iff_false]
    exact SetSemiring.mem_zero s
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, pl_add, SetSemiring.mem_add, ih, Finset.exists_mem_insert]

theorem mem_pl_ofPair_mul (t s : W A) (e : TD A) :
    SetSemiring.Mem s (pl (ofPair t * e)) ↔ ∃ w, SetSemiring.Mem w (pl e) ∧ t * w = s := by
  rw [pl_mul, pl_ofPair, SetSemiring.mem_mul]
  constructor
  · rintro ⟨a, rfl, w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨t, rfl, w, hw, rfl⟩

variable [Fintype A]

/-- **Lemma 27** (expansion). -/
theorem IsAutomaton.expansion {S : Finset (TD A)} (hS : IsAutomaton S) {e : TD A} (he : e ∈ S)
    (k : ℕ) : ∃ (B T : Finset (W A)) (es : W A → TD A),
      (∀ s, s ∈ B ↔ ofPair s ≤ e ∧ size s < k) ∧ (∀ s ∈ T, size s = k) ∧ (∀ s, es s ∈ S) ∧
      e = ∑ s ∈ B, ofPair s + ∑ s ∈ T, ofPair s * es s := by
  induction k with
  | zero =>
    refine ⟨∅, {1}, fun _ => e, fun s => by simp, fun s hs => by simp_all, fun _ => he, ?_⟩
    rw [Finset.sum_empty, zero_add, Finset.sum_singleton, ofPair_one, one_mul]
  | succ k ih =>
    obtain ⟨B, T, es, hB, hT, hes, heq⟩ := ih
    choose δ hδS hδ using fun s => hS.deriv (es s) (hes s)
    let g : W A × (A ⊕ A) → W A := fun p => p.1 * letter p.2
    let P := T ×ˢ (Finset.univ : Finset (A ⊕ A))
    refine ⟨B ∪ T.filter (fun s => Nullable (es s)), P.image g,
      fun s' => ∑ p ∈ P with g p = s', δ p.1 p.2, ?_, ?_, ?_, ?_⟩
    · -- Membership: the strings of size `< k + 1` below `e`.
      have hTe : ∑ s ∈ T, ofPair s * es s ≤ e := by
        conv_rhs => rw [heq]
        exact le_add_left le_rfl
      intro s
      rw [Finset.mem_union, Finset.mem_filter, hB]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨hsT, hn⟩)
        · exact ⟨h1, by omega⟩
        · refine ⟨?_, by rw [hT s hsT]; omega⟩
          calc ofPair s = ofPair s * 1 := (mul_one _).symm
            _ ≤ ofPair s * es s := mul_le_mul' le_rfl ((nullable_iff _).1 hn)
            _ ≤ ∑ s ∈ T, ofPair s * es s := le_sum_of_mem (fun s => ofPair s * es s) hsT
            _ ≤ e := hTe
      · rintro ⟨hle, hsize⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hsize with hlt | hk
        · exact Or.inl ⟨hle, hlt⟩
        · right
          have hmem := (ofPair_le_iff_mem s e).1 hle
          rw [heq, pl_add, SetSemiring.mem_add, mem_pl_sum, mem_pl_sum] at hmem
          rcases hmem with ⟨b, hbB, hb⟩ | ⟨t, htT, ht⟩
          · rw [pl_ofPair, mem_single] at hb
            subst hb
            exact absurd (hB s |>.1 hbB).2 (by omega)
          · obtain ⟨w, hw, rfl⟩ := (mem_pl_ofPair_mul t s _).1 ht
            have hw1 : w = 1 := eq_one_of_size_eq_zero (by rw [size_mul, hT t htT] at hk; omega)
            subst hw1
            rw [mul_one]
            exact ⟨htT, hw⟩
    · -- Sizes.
      intro s' hs'
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs'
      rw [size_mul, size_letter, hT p.1 (Finset.mem_product.1 hp).1]
    · -- Residuals are states.
      exact fun s' => hS.sum_mem _ _ fun p _ => hδS p.1 p.2
    · -- The equation.
      have hsplit : ∑ s ∈ T, ofPair s * es s =
          ∑ s ∈ T with Nullable (es s), ofPair s + ∑ p ∈ P, ofPair (g p) * δ p.1 p.2 := by
        calc ∑ s ∈ T, ofPair s * es s
            = ∑ s ∈ T, (ofPair s * nul (es s) + ∑ x, ofPair s * of x * δ s x) := by
              refine Finset.sum_congr rfl fun s _ => ?_
              conv_lhs => rw [hδ s]
              rw [mul_add, Finset.mul_sum]
              simp only [mul_assoc]
          _ = ∑ s ∈ T with Nullable (es s), ofPair s + ∑ p ∈ P, ofPair (g p) * δ p.1 p.2 := by
              rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_product]
              congr 1
              · refine Finset.sum_congr rfl fun s _ => ?_
                unfold nul; split_ifs <;> simp
              · refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => ?_
                simp only [g, ofPair_mul, ofPair_letter]
      have hfib : ∑ p ∈ P, ofPair (g p) * δ p.1 p.2 =
          ∑ s' ∈ P.image g, ofPair s' * ∑ p ∈ P with g p = s', δ p.1 p.2 := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := P.image g)
          (fun p hp => Finset.mem_image_of_mem g hp)]
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [(Finset.mem_filter.1 hp).2]
      conv_lhs => rw [heq]
      rw [hsplit, hfib, sum_union_idem, add_assoc]

end TD

end DiagonaLean.KAComm
