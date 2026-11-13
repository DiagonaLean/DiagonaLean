/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import Mathlib.Algebra.Order.Kleene
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # Pre-Kleene algebras

A (left-biased) *pre-Kleene algebra* is an idempotent semiring with a star operation that
satisfies only the left-unfolding law `a∗ = 1 + a * a∗`. Unlike Mathlib's `KleeneAlgebra`, it
does not assume the induction axioms. Every `KleeneAlgebra` is a `PreKleeneAlgebra`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi,
    *Kleene algebra with commutativity conditions is undecidable*][AmorimZhangGaboardi2024],
    Section 2
-/

open scoped Computability

namespace DiagonaLean.Foundations.KleeneAlgebra

/-- A pre-Kleene algebra: an idempotent semiring with a star satisfying left unfolding
`a∗ = 1 + a * a∗`. No induction axioms are assumed. -/
class PreKleeneAlgebra (α : Type*) extends IdemSemiring α, KStar α where
  /-- Left unfolding. -/
  protected kstar_unfold (a : α) : a∗ = 1 + a * a∗

section
variable {α : Type*} [PreKleeneAlgebra α]

/-- Left unfolding: `a∗ = 1 + a * a∗`. -/
theorem kstar_unfold (a : α) : a∗ = 1 + a * a∗ := PreKleeneAlgebra.kstar_unfold a

/-- `1 ≤ a∗`. -/
theorem one_le_kstar' (a : α) : 1 ≤ a∗ := by
  rw [kstar_unfold a]; exact le_sup_left.trans_eq (add_eq_sup _ _).symm

/-- `a * a∗ ≤ a∗`. -/
theorem mul_kstar_le_kstar' (a : α) : a * a∗ ≤ a∗ := by
  conv_rhs => rw [kstar_unfold a]
  exact le_sup_right.trans_eq (add_eq_sup _ _).symm

/-- `a ≤ a∗`. -/
theorem le_kstar' (a : α) : a ≤ a∗ := by
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * a∗ := mul_le_mul_right (one_le_kstar' a) a
    _ ≤ a∗ := mul_kstar_le_kstar' a

/-- `a ^ n ≤ a∗`, by `n` uses of left unfolding. -/
theorem pow_le_kstar' (a : α) : ∀ n : ℕ, a ^ n ≤ a∗
  | 0 => by rw [pow_zero]; exact one_le_kstar' a
  | n + 1 => by
    rw [pow_succ']
    exact (mul_le_mul_right (pow_le_kstar' a n) a).trans (mul_kstar_le_kstar' a)

/-- The star of `0` is `1`. -/
@[simp] theorem kstar_zero' : (0 : α)∗ = 1 := by
  rw [kstar_unfold, zero_mul, add_zero]

/-- If `a ≤ x` then `a x∗ ≤ x∗`, by one left unfolding. -/
theorem mul_kstar_le_of_le {a x : α} (h : a ≤ x) : a * x∗ ≤ x∗ :=
  (mul_le_mul' h le_rfl).trans (mul_kstar_le_kstar' x)

/-- A product of elements below `x`, followed by `x∗`, is below `x∗`. This is the form of the
paper's Theorem 9 that survives (`not_forall_finite_lang_mul_kstar_le`): it applies to strings
rather than to arbitrary finite languages. -/
theorem list_prod_mul_kstar_le (x : α) :
    ∀ l : List α, (∀ a ∈ l, a ≤ x) → l.prod * x∗ ≤ x∗
  | [], _ => by rw [List.prod_nil, one_mul]
  | a :: l, h => by
    rw [List.prod_cons, mul_assoc]
    exact (mul_le_mul' le_rfl (list_prod_mul_kstar_le x l fun b hb => h b (by simp [hb]))).trans
      (mul_kstar_le_of_le (h a (by simp)))

/-- A finite sum is below `b` if every summand is. -/
theorem sum_le_of_forall {ι : Type*} (s : Finset ι) (f : ι → α) {b : α}
    (h : ∀ i ∈ s, f i ≤ b) : ∑ i ∈ s, f i ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ← add_eq_right_iff_le, zero_add]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add_le (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

/-- Each summand of a finite sum is below the sum. -/
theorem le_sum_of_mem {ι : Type*} {s : Finset ι} (f : ι → α) {i : ι} (hi : i ∈ s) :
    f i ≤ ∑ j ∈ s, f j := by
  classical
  rw [← Finset.insert_erase hi, Finset.sum_insert (Finset.notMem_erase i s)]
  exact le_add_right le_rfl

/-- Finite sums are monotone in the summands. -/
theorem sum_le_sum_of_le {ι : Type*} (s : Finset ι) {f g : ι → α} (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i :=
  sum_le_of_forall s f fun i hi => (h i hi).trans (le_sum_of_mem g hi)

end

/-- Every Kleene algebra is a pre-Kleene algebra. -/
instance (priority := 100) PreKleeneAlgebra.ofKleeneAlgebra (α : Type*) [KleeneAlgebra α] :
    PreKleeneAlgebra α where
  kstar_unfold a := (one_add_mul_kstar (a := a)).symm

end DiagonaLean.Foundations.KleeneAlgebra
