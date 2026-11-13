/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.PreKleene

@[expose] public section

/-! # A pre-Kleene algebra that is not a Kleene algebra (Example 1)

The carrier is `ℕ + {⊥, ⊤}` ordered by `⊥ ≤ n ≤ ⊤`. Addition is the maximum, multiplication
is `+` on `ℕ`, with `⊥` absorbing and `⊤` absorbing every non-`⊥` element. Star sends `⊥` to
`0` (the unit) and everything else to `⊤`. This structure is a pre-Kleene algebra in which
left induction fails, so it is not a Kleene algebra.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Example 1,
  adapted from [Kozen 1990].
-/

open scoped Computability

namespace DiagonaLean.Foundations.KleeneAlgebra

/-- The carrier `ℕ + {⊥, ⊤}` of Example 1. -/
inductive NatBotTop where
  /-- The bottom element `⊥`, which is also the zero. -/
  | bot
  /-- A natural number; `nat 0` is the unit. -/
  | nat (n : ℕ)
  /-- The top element `⊤`. -/
  | top
  deriving DecidableEq

namespace NatBotTop

/-- Addition is the maximum for `⊥ ≤ n ≤ ⊤`. -/
def add : NatBotTop → NatBotTop → NatBotTop
  | bot, y => y
  | nat m, bot => nat m
  | nat m, nat n => nat (max m n)
  | nat _, top => top
  | top, _ => top

/-- Multiplication: `⊥` absorbs, then `⊤` absorbs, else `+` on `ℕ`. -/
def mul : NatBotTop → NatBotTop → NatBotTop
  | bot, _ => bot
  | nat _, bot => bot
  | nat m, nat n => nat (m + n)
  | nat _, top => top
  | top, bot => bot
  | top, _ => top

/-- Star: `⊥∗ = 0` (the unit), otherwise `⊤`. -/
def star : NatBotTop → NatBotTop
  | bot => nat 0
  | _ => top

/-- Zero is `⊥`. -/
instance : Zero NatBotTop := ⟨bot⟩
/-- One is `nat 0`. -/
instance : One NatBotTop := ⟨nat 0⟩
/-- Addition is `NatBotTop.add`. -/
instance : Add NatBotTop := ⟨add⟩
/-- Multiplication is `NatBotTop.mul`. -/
instance : Mul NatBotTop := ⟨mul⟩
/-- Star is `NatBotTop.star`. -/
instance : KStar NatBotTop := ⟨star⟩

/-- `0` unfolds to `bot`. -/
@[simp] lemma zero_def : (0 : NatBotTop) = bot := rfl
/-- `1` unfolds to `nat 0`. -/
@[simp] lemma one_def : (1 : NatBotTop) = nat 0 := rfl
/-- `+` unfolds to `NatBotTop.add`. -/
@[simp] lemma add_def (a b : NatBotTop) : a + b = add a b := rfl
/-- `*` unfolds to `NatBotTop.mul`. -/
@[simp] lemma mul_def (a b : NatBotTop) : a * b = mul a b := rfl
/-- `∗` unfolds to `NatBotTop.star`. -/
@[simp] lemma kstar_def (a : NatBotTop) : a∗ = star a := rfl

/-- `NatBotTop` is a semiring. -/
instance : Semiring NatBotTop where
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

/-- Addition in `NatBotTop` is idempotent. -/
instance : IdemSemiring NatBotTop :=
  IdemSemiring.ofSemiring fun a => by cases a <;> simp [add]

/-- `NatBotTop` is a pre-Kleene algebra. -/
instance instPreKleeneAlgebra : PreKleeneAlgebra NatBotTop where
  kstar_unfold a := by cases a <;> rfl

/-- The unit's star is `⊤`, not the unit. -/
theorem one_kstar : (1 : NatBotTop)∗ = top := rfl

/-- The star of the unit is not the unit. -/
theorem one_kstar_ne : (1 : NatBotTop)∗ ≠ 1 := by simp [star]

/-- `⊤` is not below the unit. -/
theorem top_not_le_one : ¬ (top : NatBotTop) ≤ 1 := fun h =>
  NatBotTop.noConfusion (h : NatBotTop.add NatBotTop.top (NatBotTop.nat 0) = NatBotTop.nat 0)

/-- `(⊥∗)∗ ≠ ⊥∗`. The law `a∗∗ = a∗` holds in every Kleene algebra. -/
theorem kstar_kstar_ne : ((0 : NatBotTop)∗)∗ ≠ (0 : NatBotTop)∗ := by simp [star]

/-- Left induction `a * b ≤ b → a∗ * b ≤ b` fails at `a = b = 1`. -/
theorem not_left_induction : ¬ ∀ a b : NatBotTop, a * b ≤ b → a∗ * b ≤ b := by
  intro h
  have := h 1 1 le_rfl
  revert this
  change ¬ (add (mul (star (nat 0)) (nat 0)) (nat 0) = nat 0)
  simp [star, mul, add]

/-- `NatBotTop` admits no Kleene algebra structure with the same semiring and star. -/
theorem not_kleeneAlgebra (K : KleeneAlgebra NatBotTop)
    (hstar : ∀ a, @KStar.kstar NatBotTop K.toKStar a = a∗)
    (hle : ∀ a b : NatBotTop, @LE.le NatBotTop K.toLE a b ↔ a ≤ b)
    (hmul : ∀ a b : NatBotTop, @HMul.hMul NatBotTop NatBotTop NatBotTop (@instHMul NatBotTop K.toMul) a b = a * b) :
    False := by
  apply not_left_induction
  intro a b hab
  have := @KleeneAlgebra.kstar_mul_le_self NatBotTop K a b
  rw [hle, hle, hmul, hmul, hstar] at this
  exact this hab

end NatBotTop

end DiagonaLean.Foundations.KleeneAlgebra
