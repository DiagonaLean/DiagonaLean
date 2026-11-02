/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.PreKleene

@[expose] public section

/-! # A pre-Kleene algebra that is not a Kleene algebra (Example 1)

The carrier is `ℕ + {⊥, ⊤}` ordered by `⊥ ≤ n ≤ ⊤`. Addition is the maximum, multiplication
is `+` on `ℕ`, with `⊥` absorbing and `⊤` absorbing every non-`⊥` element. Star sends `⊥` to
`0` (the unit) and everything else to `⊤`.

## Main statements

* `Ex1.instPreKleeneAlgebra`: `Ex1` is a pre-Kleene algebra.
* `Ex1.kstar_kstar_ne`: `(⊥∗)∗ ≠ ⊥∗`, so `Ex1` is not a Kleene algebra.
* `Ex1.not_left_induction`: left induction fails at `a = b = 1`.
* `Ex1.one_kstar`: `1∗ = ⊤ ≠ 1`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Example 1,
  adapted from [Kozen 1990].
-/

open scoped Computability

namespace DiagonaLean.KAComm

/-- The carrier `ℕ + {⊥, ⊤}` of Example 1. -/
inductive Ex1 where
  | bot
  | nat (n : ℕ)
  | top
  deriving DecidableEq

namespace Ex1

/-- Addition is the maximum for `⊥ ≤ n ≤ ⊤`. -/
def add : Ex1 → Ex1 → Ex1
  | bot, y => y
  | nat m, bot => nat m
  | nat m, nat n => nat (max m n)
  | nat _, top => top
  | top, _ => top

/-- Multiplication: `⊥` absorbs, then `⊤` absorbs, else `+` on `ℕ`. -/
def mul : Ex1 → Ex1 → Ex1
  | bot, _ => bot
  | nat _, bot => bot
  | nat m, nat n => nat (m + n)
  | nat _, top => top
  | top, bot => bot
  | top, _ => top

/-- Star: `⊥∗ = 0` (the unit), otherwise `⊤`. -/
def star : Ex1 → Ex1
  | bot => nat 0
  | _ => top

instance : Zero Ex1 := ⟨bot⟩
instance : One Ex1 := ⟨nat 0⟩
instance : Add Ex1 := ⟨add⟩
instance : Mul Ex1 := ⟨mul⟩
instance : KStar Ex1 := ⟨star⟩

@[simp] lemma zero_def : (0 : Ex1) = bot := rfl
@[simp] lemma one_def : (1 : Ex1) = nat 0 := rfl
@[simp] lemma add_def (a b : Ex1) : a + b = add a b := rfl
@[simp] lemma mul_def (a b : Ex1) : a * b = mul a b := rfl
@[simp] lemma kstar_def (a : Ex1) : a∗ = star a := rfl

instance : Semiring Ex1 where
  add_assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp [add, max_assoc]
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> simp [add, max_comm]
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp [mul, Nat.add_assoc]
  one_mul a := by cases a <;> simp [mul]
  mul_one a := by cases a <;> simp [mul]
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  left_distrib a b c := by
    cases a <;> cases b <;> cases c <;> simp [add, mul, Nat.add_max_add_left]
  right_distrib a b c := by
    cases a <;> cases b <;> cases c <;> simp [add, mul, Nat.add_max_add_right]
  nsmul := nsmulRec

instance : IdemSemiring Ex1 :=
  IdemSemiring.ofSemiring fun a => by cases a <;> simp [add]

instance instPreKleeneAlgebra : PreKleeneAlgebra Ex1 where
  kstar_unfold a := by cases a <;> rfl

/-- The unit's star is `⊤`, not the unit. -/
theorem one_kstar : (1 : Ex1)∗ = top := rfl

theorem one_kstar_ne : (1 : Ex1)∗ ≠ 1 := by simp [star]

theorem top_not_le_one : ¬ (top : Ex1) ≤ 1 := fun h =>
  Ex1.noConfusion (h : Ex1.add Ex1.top (Ex1.nat 0) = Ex1.nat 0)

/-- `(⊥∗)∗ ≠ ⊥∗`. The law `a∗∗ = a∗` holds in every Kleene algebra. -/
theorem kstar_kstar_ne : ((0 : Ex1)∗)∗ ≠ (0 : Ex1)∗ := by simp [star]

/-- Left induction `a * b ≤ b → a∗ * b ≤ b` fails at `a = b = 1`. -/
theorem not_left_induction : ¬ ∀ a b : Ex1, a * b ≤ b → a∗ * b ≤ b := by
  intro h
  have := h 1 1 le_rfl
  revert this
  change ¬ (add (mul (star (nat 0)) (nat 0)) (nat 0) = nat 0)
  simp [star, mul, add]

/-- `Ex1` admits no Kleene algebra structure with the same semiring and star. -/
theorem not_kleeneAlgebra (K : KleeneAlgebra Ex1)
    (hstar : ∀ a, @KStar.kstar Ex1 K.toKStar a = a∗)
    (hle : ∀ a b : Ex1, @LE.le Ex1 K.toLE a b ↔ a ≤ b)
    (hmul : ∀ a b : Ex1, @HMul.hMul Ex1 Ex1 Ex1 (@instHMul Ex1 K.toMul) a b = a * b) :
    False := by
  apply not_left_induction
  intro a b hab
  have := @KleeneAlgebra.kstar_mul_le_self Ex1 K a b
  rw [hle, hle, hmul, hmul, hstar] at this
  exact this hab

end Ex1

end DiagonaLean.KAComm
