/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.PreKleene
import Mathlib.Data.Set.Semiring

@[expose] public section

/-! # The power set of a monoid as a pre-Kleene algebra

For a monoid `M`, Mathlib's `SetSemiring M` is an idempotent semiring (union, pointwise product).
This file adds the star `A∗ = {a₁ ⋯ aₙ | aᵢ ∈ A}` and proves left unfolding, so `SetSemiring M`
is a pre-Kleene algebra. This is the language model `P X` of Section 2.2 of Azevedo de Amorim,
Zhang, and Gaboardi.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi,
    *Kleene algebra with commutativity conditions is undecidable*][AmorimZhangGaboardi2024],
    Section 2.2
-/

open scoped Computability Pointwise

namespace DiagonaLean.Foundations.KleeneAlgebra

namespace SetSemiring

open _root_.SetSemiring (down)

variable {M : Type*}

/-- Membership in an element of `SetSemiring M`. -/
def Mem (x : M) (s : _root_.SetSemiring M) : Prop := x ∈ s.down

/-- Two elements of `SetSemiring M` with the same members are equal. -/
theorem ext {s t : _root_.SetSemiring M} (h : ∀ x, Mem x s ↔ Mem x t) : s = t :=
  Set.ext h

/-- Nothing is a member of `0`. -/
theorem mem_zero (x : M) : ¬ Mem x (0 : _root_.SetSemiring M) := fun h => h

/-- `x ∈ s + t` iff `x ∈ s` or `x ∈ t`. -/
theorem mem_add (x : M) (s t : _root_.SetSemiring M) : Mem x (s + t) ↔ Mem x s ∨ Mem x t :=
  Iff.rfl

/-- `x ∈ Set.up s` iff `x ∈ s`. -/
theorem mem_up (x : M) (s : Set M) : Mem x (Set.up s) ↔ x ∈ s := Iff.rfl

/-- `s ≤ t` iff every member of `s` is a member of `t`. -/
theorem le_iff (s t : _root_.SetSemiring M) : s ≤ t ↔ ∀ x, Mem x s → Mem x t := Iff.rfl

variable [Monoid M]

/-- `x ∈ 1` iff `x = 1`. -/
theorem mem_one (x : M) : Mem x (1 : _root_.SetSemiring M) ↔ x = 1 := Iff.rfl

/-- `x ∈ s * t` iff `x = a * b` for some `a ∈ s` and `b ∈ t`. -/
theorem mem_mul (x : M) (s t : _root_.SetSemiring M) :
    Mem x (s * t) ↔ ∃ a, Mem a s ∧ ∃ b, Mem b t ∧ a * b = x := by
  unfold Mem; rw [_root_.SetSemiring.down_mul, Set.mem_mul]

/-- The star of `s` is the set of finite products of members of `s`. -/
instance instKStar : KStar (_root_.SetSemiring M) :=
  ⟨fun s => Set.up {x | ∃ l : List M, (∀ y ∈ l, Mem y s) ∧ l.prod = x}⟩

/-- `x ∈ s∗` iff `x` is the product of a list of members of `s`. -/
theorem mem_kstar (x : M) (s : _root_.SetSemiring M) :
    Mem x s∗ ↔ ∃ l : List M, (∀ y ∈ l, Mem y s) ∧ l.prod = x := Iff.rfl

/-- `x ∈ s∗` iff `x = 1` or `x = a * b` with `a ∈ s` and `b ∈ s∗`. -/
theorem mem_kstar_iff_unfold (x : M) (s : _root_.SetSemiring M) :
    Mem x s∗ ↔ x = 1 ∨ ∃ a, Mem a s ∧ ∃ b, Mem b s∗ ∧ a * b = x := by
  rw [mem_kstar]
  constructor
  · rintro ⟨l, hl, rfl⟩
    cases l with
    | nil => exact Or.inl rfl
    | cons a l =>
      exact Or.inr ⟨a, hl a (by simp), l.prod, ⟨l, fun y hy => hl y (by simp [hy]), rfl⟩,
        (List.prod_cons).symm⟩
  · rintro (rfl | ⟨a, ha, b, ⟨l, hl, rfl⟩, rfl⟩)
    · exact ⟨[], by simp, rfl⟩
    · refine ⟨a :: l, ?_, List.prod_cons⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      exacts [ha, hl y hy]

/-- `SetSemiring M` is a pre-Kleene algebra. -/
noncomputable instance instPreKleeneAlgebra : PreKleeneAlgebra (_root_.SetSemiring M) where
  kstar_unfold s := ext fun x => by
    rw [mem_kstar_iff_unfold, mem_add, mem_one, mem_mul]

/-- `x ∈ sⁿ` iff `x` is a product of `n` elements of `s`. -/
theorem mem_pow (x : M) (s : _root_.SetSemiring M) (n : ℕ) :
    Mem x (s ^ n) ↔ ∃ l : List M, l.length = n ∧ (∀ y ∈ l, Mem y s) ∧ l.prod = x := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero, mem_one]
    constructor
    · rintro rfl; exact ⟨[], rfl, by simp, rfl⟩
    · rintro ⟨l, hl, -, rfl⟩; rw [List.length_eq_zero_iff.1 hl]; rfl
  | succ n ih =>
    rw [pow_succ', mem_mul]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨l, hl, hls, rfl⟩ := (ih b).1 hb
      refine ⟨a :: l, by simp [hl], ?_, List.prod_cons⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      exacts [ha, hls y hy]
    · rintro ⟨l, hl, hls, rfl⟩
      cases l with
      | nil => simp at hl
      | cons a l =>
        exact ⟨a, hls a (by simp), l.prod,
          (ih _).2 ⟨l, by simpa using hl, fun y hy => hls y (by simp [hy]), rfl⟩,
          List.prod_cons.symm⟩

/-- `x ∈ s∗` iff `x ∈ sⁿ` for some `n`. -/
theorem mem_kstar_iff_pow (x : M) (s : _root_.SetSemiring M) :
    Mem x s∗ ↔ ∃ n, Mem x (s ^ n) := by
  simp only [mem_kstar, mem_pow]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact ⟨l.length, l, rfl, hl, rfl⟩
  · rintro ⟨n, l, -, hl, rfl⟩; exact ⟨l, hl, rfl⟩

end SetSemiring

end DiagonaLean.Foundations.KleeneAlgebra
