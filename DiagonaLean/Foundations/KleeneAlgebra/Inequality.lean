/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.FreeKA
import DiagonaLean.Foundations.KleeneAlgebra.Syntax

@[expose] public section

/-! # Instances and inequalities over the doubled alphabet

An instance (`EqInstance α`) is a pair of expressions over the doubled alphabet `α ⊕ α`, in which
every left letter commutes with every right letter (`DComm`). `Inst` and `InstB` are the instances
over `ℕ` and over `Bool`. For an instance `(e, f)` over `ℕ`, `Provable` is `e ≤ f` in pre-Kleene
algebra, `KAProvable` is `e ≤ f` in Kleene algebra, and `ModelLe` is inclusion in the language
model; each implies the next.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Section 3
-/

namespace DiagonaLean.Foundations.KleeneAlgebra

open RExp TD FreePreKA

/-- An instance of equality: two expressions over the doubled alphabet `α ⊕ α`. -/
abbrev EqInstance (α : Type) := RExp (α ⊕ α) × RExp (α ⊕ α)

/-- An instance over the doubled alphabet `ℕ ⊕ ℕ`. -/
abbrev Inst := EqInstance ℕ

/-- An instance over the doubled alphabet `Bool ⊕ Bool`, the paper's `Σ = {0, 1}`. -/
abbrev InstB := EqInstance Bool

/-- `e ≤ f` is provable in pre-Kleene algebra, with left letters commuting with right letters. -/
def Provable (i : Inst) : Prop := (mk i.1 : TD ℕ) ≤ mk i.2

/-- `e ≤ f` holds in the language model. -/
def ModelLe (i : Inst) : Prop := pl (mk i.1 : TD ℕ) ≤ pl (mk i.2)

/-- A provable inequality holds in the language model. -/
theorem Provable.modelLe {i : Inst} (h : Provable i) : ModelLe i := pl_mono h

/-- `Provable` is provable equality of `e + f` and `f` in `T Σ̈`. -/
theorem provable_iff_equiv (i : Inst) : Provable i ↔ Equiv DComm (plus i.1 i.2) i.2 := mk_le_mk

/-- `ModelLe` is equality of the languages of `e + f` and `f`. -/
theorem modelLe_iff_langEq (i : Inst) :
    ModelLe i ↔ pl (mk (plus i.1 i.2) : TD ℕ) = pl (mk i.2) := by
  rw [mk_plus, pl_add]
  exact add_eq_right_iff_le.symm

/-- `e ≤ f` is provable in Kleene algebra with commutativity. -/
def KAProvable (i : Inst) : Prop := KAEquiv DComm (plus i.1 i.2) i.2

/-- `KAProvable i` holds iff `i.1 ≤ i.2` in the free Kleene algebra. -/
theorem kaProvable_iff_le (i : Inst) :
    KAProvable i ↔ (FreeKA.mk i.1 : FreeKA (ℕ ⊕ ℕ) DComm) ≤ FreeKA.mk i.2 :=
  FreeKA.mk_eq_mk.symm.trans (add_eq_right_iff_le (a := FreeKA.mk i.1) (b := FreeKA.mk i.2))

/-- An inequality provable in `T Σ̈` is provable in Kleene algebra. -/
theorem Provable.kaProvable {i : Inst} (h : Provable i) : KAProvable i :=
  .ofEquiv ((provable_iff_equiv i).1 h)

/-- An inequality provable in Kleene algebra holds in the language model. -/
theorem KAProvable.modelLe {i : Inst} (h : KAProvable i) : ModelLe i :=
  (modelLe_iff_langEq i).2 (RExp.eval_ka_sound gen gen_comm h)

end DiagonaLean.Foundations.KleeneAlgebra
