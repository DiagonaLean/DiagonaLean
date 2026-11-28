/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.CombinatoryLogic.Conv

@[expose] public section

/-! # Convertibility of SKI terms

Two SKI terms `x`, `y` are **convertible** when they have a common reduct under Cslib's reduction
`Red`: `Convertible x y`, which is `∃ z, x ↠ z ∧ y ↠ z` (`convertible_iff`). Partially applied,
`Convertible x` is the convertibility class of `x`. By confluence (`join_mRed_equivalence`) this is
the equivalence closure of `Red` (`convertible_iff_eqvGen`), which Hindley and Seldin call weak
equality. The relation is `Foundations.CombinatoryLogic.Conv`, in a file of definitions only.

The decision problem takes one argument, a pair (`DecisionProblem`), since the reductions and the
computability statements are about predicates on one type; `decisionProblem_mk` states it curried,
by `Iff.rfl`. `SKIConvProblem` names it.

To audit the definition, read `Convertible`, `decisionProblem_mk` and `convertible_iff`, which
states the problem in Cslib's and Mathlib's terms; all are pinned in `scripts/HeadlineTest.lean`.

## Main definitions

* `Convertible`: the problem, curried. `DecisionProblem`, `SKIConvProblem`: on pairs.

## Main statements

* `decisionProblem_mk`: the problem on pairs is the curried problem.
* `convertible_iff`: the problem in Cslib's and Mathlib's terms, a common reduct under `Red`.
* `convertible_iff_eqvGen`, `decisionProblem_iff_eqvGen`: the equivalence closure of `Red`.

## References

* [J. R. Hindley, J. P. Seldin,
  *Lambda-Calculus and Combinators: An Introduction*][HindleySeldin2008]
-/

namespace DiagonaLean.SKIConv

open Cslib SKI Relation

/-! ### The problem -/

/-- **Convertibility of SKI terms**: do `x` and `y` have a common reduct? Partially applied,
`Convertible x` is the convertibility class of `x`. -/
abbrev Convertible (x y : SKI) : Prop := Foundations.CombinatoryLogic.Conv x y

/-- **Convertibility in Cslib's and Mathlib's terms**: a common reduct under `Red`. -/
theorem convertible_iff (x y : SKI) :
    Convertible x y ↔ ∃ z, ReflTransGen Red x z ∧ ReflTransGen Red y z := Iff.rfl

/-- Two SKI terms are convertible iff they are related by `EqvGen Red`. -/
theorem convertible_iff_eqvGen (x y : SKI) : Convertible x y ↔ EqvGen Red x y := by
  constructor
  · rintro ⟨c, h₁, h₂⟩
    exact .trans _ _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ h₁)
      (.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ h₂))
  · intro h
    exact join_mRed_equivalence.eqvGen_iff.1
      (EqvGen.mono (fun a b h => ⟨b, .single h, .refl⟩) _ _ h)

/-! ### The problem on a pair, for the reductions and the computability statements -/

/-- **The problem on a pair**, for the reductions and the computability statements:
`Convertible` on its two terms. Read it curried, `decisionProblem_mk`. -/
def DecisionProblem (i : SKI × SKI) : Prop := Convertible i.1 i.2

/-- Convertibility of SKI terms. -/
abbrev SKIConvProblem : SKI × SKI → Prop := DecisionProblem

/-- The problem on a pair is the curried problem. -/
@[simp] theorem decisionProblem_mk (x y : SKI) : DecisionProblem (x, y) ↔ Convertible x y :=
  Iff.rfl

/-- Two SKI terms have a common reduct iff they are related by `EqvGen Red`. -/
theorem decisionProblem_iff_eqvGen (i : SKI × SKI) : DecisionProblem i ↔ EqvGen Red i.1 i.2 :=
  convertible_iff_eqvGen i.1 i.2

end DiagonaLean.SKIConv
