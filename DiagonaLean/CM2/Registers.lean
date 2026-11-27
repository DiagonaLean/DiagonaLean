/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Arithmetic
import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

/-! # Three registers in two counters

The first counter holds `2 ^ l * 3 ^ r * 5 ^ t` and the second is zero (`encode`). The exponent
of a prime `p` is a register (`factor`): an increment multiplies the first counter by `p`, and a
decrement divides it by `p`, restoring it when the remainder is not zero. The exponents of 2, 3
and 5 are registers (`models_two`, `models_three`, `models_five`).

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967], Section 14.1
-/

namespace DiagonaLean.CM2.Register

/-- The two counters are two registers stored together. -/
private theorem pairModels_physical : PairModels (physical false) (physical true) Prod.mk :=
  ⟨models_left, models_right⟩

/-- The register of the exponent of `p` in the first counter. -/
def factor (p : ℕ) : Register where
  inc k := multiply (physical false) (physical true) p k
  dec z s := divide (physical false) (physical true) p fun r =>
    if r = 0 then s else multiply (physical false) (physical true) p ((physical false).add r z)

/-- The exponent of `p` in `p ^ n * co` is a register when `p` does not divide `co`. -/
theorem models_factor (p co : ℕ) (hp : 0 < p) (hc : co % p ≠ 0) :
    (factor p).Models (fun n => (p ^ n * co, 0)) where
  inc {α k n i w} h := by
    apply pairModels_physical.multiply
    simpa [pow_succ, Nat.mul_right_comm] using h
  zero {α z s i w} h := by
    simp only [pow_zero, Nat.one_mul] at h ⊢
    have eqn := Nat.mod_add_div co p
    rw [Nat.mul_comm p] at eqn
    conv => arg 2; rw [← eqn]
    apply pairModels_physical.divide (Nat.mod_lt co hp)
    simp only [hc, ite_false, Nat.zero_add]
    apply pairModels_physical.multiply
    apply (models_left 0).add
    simpa [Nat.add_comm, eqn] using h
  succ {α z s n i w} h := by
    have eqn : p ^ (n + 1) * co = 0 + (p ^ n * co) * p := by
      simp [pow_succ, Nat.mul_right_comm]
    rw [eqn]
    apply pairModels_physical.divide hp
    simpa using h

/-- The counters that store the three values `l`, `r` and `t`. -/
def encode (l r t : ℕ) : ℕ × ℕ := (2 ^ l * 3 ^ r * 5 ^ t, 0)

/-- A prime that divides neither `a` nor `b` does not divide `a ^ i * b ^ j`. -/
private theorem pow_mul_pow_mod_ne_zero {p a b : ℕ} (hp : Nat.Prime p) (ha : ¬p ∣ a) (hb : ¬p ∣ b)
    (i j : ℕ) : a ^ i * b ^ j % p ≠ 0 := by
  intro h
  rcases hp.dvd_mul.mp (Nat.dvd_of_mod_eq_zero h) with h | h
  · exact ha (hp.dvd_of_dvd_pow h)
  · exact hb (hp.dvd_of_dvd_pow h)

/-- The exponent of 2 is a register. -/
theorem models_two (r t : ℕ) : (factor 2).Models (fun l => encode l r t) := by
  simpa [encode, Nat.mul_assoc] using
    models_factor 2 _ (by decide) (pow_mul_pow_mod_ne_zero Nat.prime_two (a := 3) (b := 5)
      (by decide) (by decide) r t)

/-- The exponent of 3 is a register. -/
theorem models_three (l t : ℕ) : (factor 3).Models (fun r => encode l r t) := by
  simpa [encode, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    models_factor 3 _ (by decide) (pow_mul_pow_mod_ne_zero Nat.prime_three (a := 2) (b := 5)
      (by decide) (by decide) l t)

/-- The exponent of 5 is a register. -/
theorem models_five (l r : ℕ) : (factor 5).Models (fun t => encode l r t) := by
  simpa [encode, Nat.mul_comm] using
    models_factor 5 _ (by decide) (pow_mul_pow_mod_ne_zero (by decide : Nat.Prime 5) (a := 2)
      (b := 3) (by decide) (by decide) l r)

end DiagonaLean.CM2.Register
