/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Doubled
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Finite.Basic

@[expose] public section

/-! # Representable relations (§4)

A term `e ∈ T Σ̈` describes a relation `u →ₑ v :↔ u_l v_r ≤ e` on words over `Σ`. It is
*representable* on a set of words `L` (Def 20) when its single steps can be bounded, in pre-Kleene
algebra, by the strings it actually produces plus an "error" term `Σ∗ Σ^≠ ρ`. Lemma 21 iterates
this bound through `e∗`, and Theorem 22 is the terminating case.

## Notation (paper ↦ Lean)

* a word `u` over `Σ` viewed in `T Σ̈` (`x ↦ x_l x_r`): `dg u`; a finite set `Λ`: `dgS Λ`.
* `Λ_r`: `rtS Λ`.  `Σ`: `sig` (so `Σ∗` is `sig∗`).  `Σ^≠ = Σ_{x ≠ y} x_l y_r`: `sigNe`.
* `Σ∗ Σ^≠ ρ`: `err ρ`.  `Next_e(Λ)`: `Next e Λ`.

## Design

* `L` is a set of words, not a term over `Σ`: the paper only uses `L` through "`s ≤ L`" for
  strings `s`, which by Theorem 5 is membership in its language.
* Def 20 asks for the residue bound only for `Λ ⊆ L`. The paper's Def 20 omits this, but Lemma 21
  only uses it there and Lemma 34 needs it (it uses prefix-freeness of `L` at `s ∈ Λ`).
* `Next^{<n}` is defined by the recursion the proof of Lemma 21 uses,
  `Next^{<n+1}(Λ) = Λ ∪ Next^{<n}(Next(Λ))`, instead of as a union over `i < n`.

## Main statements

* `TD.Rel`: Definition 20.
* `TD.Rel.lemma21`: Lemma 21.
* `TD.Rel.theorem22`: Theorem 22.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], §4
-/

open scoped Computability

namespace DiagonaLean.KAComm

namespace TD

open FreePreKA

variable {A : Type*}

/-! ### Words over `Σ` as terms -/

/-- A word `u` over `Σ` viewed in `T Σ̈`, each `x` read as `x_l x_r`. -/
def dg (u : FreeMonoid A) : TD A := ofPair (u, u)

theorem dg_one : dg (1 : FreeMonoid A) = 1 := ofPair_one

theorem dg_of_mul (a : A) (u : FreeMonoid A) :
    dg (FreeMonoid.of a * u) = dg (FreeMonoid.of a) * dg u := by
  rw [dg, dg, dg, ← ofPair_mul]; rfl

/-- A diagonal string followed by `x∗` stays below `x∗`, if every letter is below `x`. This is
the surviving form of Theorem 9. -/
theorem dg_mul_kstar_le (x : TD A) (hx : ∀ a, dg (FreeMonoid.of a) ≤ x) (u : FreeMonoid A) :
    dg u * x∗ ≤ x∗ := by
  induction u using FreeMonoid.inductionOn' with
  | one => rw [dg_one, one_mul]
  | of_mul a u ih =>
    rw [dg_of_mul, mul_assoc]
    exact (mul_le_mul' le_rfl ih).trans (mul_kstar_le_of_le (hx a))

/-- `Λ` viewed in `T Σ̈`. -/
def dgS (Λ : Finset (FreeMonoid A)) : TD A := ∑ u ∈ Λ, dg u

/-- `Λ_r`. -/
def rtS (Λ : Finset (FreeMonoid A)) : TD A := ∑ u ∈ Λ, R u

theorem rtS_mono {Λ Λ' : Finset (FreeMonoid A)} (h : Λ ⊆ Λ') : rtS Λ ≤ rtS Λ' :=
  sum_le_of_forall _ _ fun _ hu => le_sum_of_mem _ (h hu)

@[simp] theorem rtS_empty : rtS (∅ : Finset (FreeMonoid A)) = 0 := Finset.sum_empty

variable [Fintype A]

/-- The alphabet `Σ`, as diagonal letters `x_l x_r`. -/
def sig : TD A := ∑ a, dg (FreeMonoid.of a)

theorem dg_of_le_sig (a : A) : dg (FreeMonoid.of a) ≤ sig :=
  le_sum_of_mem (fun a => dg (FreeMonoid.of a)) (Finset.mem_univ a)

theorem dgS_mul_kstar_le (Λ : Finset (FreeMonoid A)) : dgS Λ * sig∗ ≤ (sig : TD A)∗ := by
  rw [dgS, Finset.sum_mul]
  exact sum_le_of_forall _ _ fun u _ => dg_mul_kstar_le _ dg_of_le_sig u

variable [DecidableEq A]

instance : DecidableEq (FreeMonoid A) := inferInstanceAs (DecidableEq (List A))

/-- `Σ^≠ = Σ_{x ≠ y} x_l y_r`. -/
def sigNe : TD A := ∑ a, ∑ b ∈ Finset.univ.filter (· ≠ a), of (Sum.inl a) * of (Sum.inr b)

/-- The error term `Σ∗ Σ^≠ ρ`. -/
def err (ρ : TD A) : TD A := sig∗ * (sigNe * ρ)

theorem dgS_mul_err_le (Λ : Finset (FreeMonoid A)) (ρ : TD A) : dgS Λ * err ρ ≤ err ρ := by
  rw [err, ← mul_assoc]; exact mul_le_mul' (dgS_mul_kstar_le Λ) le_rfl

/-! ### Representable relations -/

/-- `Next_e(Λ)`: the image of `Λ` under `→ₑ`. -/
def Next (e : TD A) (Λ : Set (FreeMonoid A)) : Set (FreeMonoid A) :=
  {v | ∃ u ∈ Λ, SetSemiring.Mem (u, v) (pl e)}

/-- **Definition 20.** `e` is a representable relation on `L`. -/
structure Rel (L : Set (FreeMonoid A)) (e : TD A) : Prop where
  left : ∀ s, SetSemiring.Mem s (pl e) → s.1 ∈ L
  right : ∀ s, SetSemiring.Mem s (pl e) → s.2 ∈ L
  finite : ∀ Λ : Finset (FreeMonoid A), (Next e ↑Λ).Finite
  resid : ∃ ρ : TD A, ∀ Λ : Finset (FreeMonoid A), (↑Λ ⊆ L) →
    rtS Λ * e ≤ dgS Λ * rtS (finite Λ).toFinset + err ρ

namespace Rel

variable {L : Set (FreeMonoid A)} {e : TD A} (h : Rel L e)
include h

/-- `ρ` is a residue for `e` in the sense of Def 20. -/
def ResidBy (ρ : TD A) : Prop :=
  ∀ Λ : Finset (FreeMonoid A), (↑Λ ⊆ L) → rtS Λ * e ≤ dgS Λ * rtS (h.finite Λ).toFinset + err ρ

/-- `Next_e(Λ)` as a finite set. -/
noncomputable def next (Λ : Finset (FreeMonoid A)) : Finset (FreeMonoid A) := (h.finite Λ).toFinset

theorem next_subset {Λ : Finset (FreeMonoid A)} : ↑(h.next Λ) ⊆ L := fun v hv => by
  obtain ⟨u, -, huv⟩ := (h.finite Λ).mem_toFinset.1 hv
  exact h.right _ huv

/-- `Nextⁿ_e(Λ)`. -/
noncomputable def iter : ℕ → Finset (FreeMonoid A) → Finset (FreeMonoid A)
  | 0, Λ => Λ
  | n + 1, Λ => iter n (h.next Λ)

/-- `Next^{<n}_e(Λ)`, by the recursion `Next^{<n+1}(Λ) = Λ ∪ Next^{<n}(Next(Λ))`. -/
noncomputable def below : ℕ → Finset (FreeMonoid A) → Finset (FreeMonoid A)
  | 0, _ => ∅
  | n + 1, Λ => Λ ∪ below n (h.next Λ)

/-- **Lemma 21**, for a given residue `ρ'`: the bound holds with `ρ = ρ' e∗`. -/
theorem lemma21 {ρ' : TD A} (hρ' : h.ResidBy ρ') : ∀ (n : ℕ) (Λ : Finset (FreeMonoid A)),
    ↑Λ ⊆ L →
    rtS Λ * e∗ ≤ sig∗ * rtS (h.below n Λ) + sig∗ * rtS (h.iter n Λ) * e∗ + err (ρ' * e∗) := by
  intro n
  have hone : (1 : TD A) ≤ sig∗ := one_le_kstar' _
  induction n with
  | zero =>
    intro Λ _
    simp only [below, iter, rtS_empty, mul_zero, zero_add]
    refine le_add_right ?_
    rw [mul_assoc]
    exact (one_mul _).symm.le.trans (mul_le_mul' hone le_rfl)
  | succ n ih =>
    intro Λ hΛ
    set Λ' := h.next Λ
    set S : TD A := sig∗
    set ε := err (ρ' * e∗)
    simp only [below, iter]
    -- One step: `Λ_r e∗ = Λ_r + Λ_r e e∗`, and `Λ_r e ≤ Λ Λ'_r + Σ∗Σ^≠ρ'`.
    have step : rtS Λ * e * e∗ ≤ dgS Λ * (rtS Λ' * e∗) + ε := by
      calc rtS Λ * e * e∗ ≤ (dgS Λ * rtS Λ' + err ρ') * e∗ := mul_le_mul' (hρ' Λ hΛ) le_rfl
        _ = dgS Λ * (rtS Λ' * e∗) + ε := by simp only [add_mul, err, ε, mul_assoc]
    -- The induction hypothesis on `Λ'`, absorbed by `Λ`.
    have ih' := mul_le_mul' (le_refl (dgS Λ)) (ih Λ' h.next_subset)
    have hDS : ∀ y : TD A, dgS Λ * (S * y) ≤ S * y := fun y => by
      rw [← mul_assoc]; exact mul_le_mul' (dgS_mul_kstar_le Λ) le_rfl
    have absorb : dgS Λ * (S * rtS (h.below n Λ') + S * rtS (h.iter n Λ') * e∗ + ε) ≤
        S * rtS (h.below n Λ') + S * rtS (h.iter n Λ') * e∗ + ε := by
      rw [mul_add, mul_add, mul_assoc S]
      exact add_le_add (add_le_add (hDS _) (hDS _)) (dgS_mul_err_le Λ _)
    have hsub1 : S * rtS Λ ≤ S * rtS (Λ ∪ h.below n Λ') :=
      mul_le_mul' le_rfl (rtS_mono Finset.subset_union_left)
    have hsub2 : S * rtS (h.below n Λ') ≤ S * rtS (Λ ∪ h.below n Λ') :=
      mul_le_mul' le_rfl (rtS_mono Finset.subset_union_right)
    have hΛS : rtS Λ ≤ S * rtS Λ := (one_mul _).symm.le.trans (mul_le_mul' hone le_rfl)
    calc rtS Λ * e∗ = rtS Λ + rtS Λ * e * e∗ := by
          conv_lhs => rw [kstar_unfold e]
          rw [mul_add, mul_one, mul_assoc]
      _ ≤ S * rtS Λ + ((S * rtS (h.below n Λ') + S * rtS (h.iter n Λ') * e∗ + ε) + ε) :=
          add_le_add hΛS (step.trans (add_le_add (ih'.trans absorb) le_rfl))
      _ ≤ S * rtS (Λ ∪ h.below n Λ') + S * rtS (h.iter n Λ') * e∗ + ε := by
          refine add_le (le_add_right (le_add_right hsub1)) (add_le (add_le (add_le ?_ ?_) ?_) ?_)
          · exact le_add_right (le_add_right hsub2)
          · exact le_add_right (le_add_left le_rfl)
          · exact le_add_left le_rfl
          · exact le_add_left le_rfl

/-- **Theorem 22.** If `Nextⁿ_e(Λ) = ∅`, then `Λ_r e∗ ≤ Σ∗ Next^{<n}_e(Λ)_r + Σ∗ Σ^≠ ρ`, with
`ρ = ρ' e∗` for any residue `ρ'` of `e`. -/
theorem theorem22 {ρ' : TD A} (hρ' : h.ResidBy ρ') : ∀ (n : ℕ) (Λ : Finset (FreeMonoid A)),
    ↑Λ ⊆ L → h.iter n Λ = ∅ → rtS Λ * e∗ ≤ sig∗ * rtS (h.below n Λ) + err (ρ' * e∗) := by
  intro n Λ hΛ hn
  have := h.lemma21 hρ' n Λ hΛ
  rwa [hn, rtS_empty, mul_zero, zero_mul, add_zero] at this

end Rel

end TD

end DiagonaLean.KAComm
