/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.LambdaCalculus.Conv

@[expose] public section

/-! # β-conversion of λ-terms

Two locally nameless λ-terms `M`, `N` over the variables `ℕ` are **β-convertible** when they have a
common reduct under Cslib's full β-reduction `FullBeta`: `Convertible M N`, which is
`∃ P, M ↠βᶠ P ∧ N ↠βᶠ P` (`convertible_iff`). Partially applied, `Convertible M` is the
β-convertibility class of `M`. By confluence (`confluent_fullBeta`) this is the equivalence closure
of `FullBeta` (`convertible_iff_eqvGen`). The relation is `Foundations.LambdaCalculus.Conv`, in a
file of definitions only.

The locally closed terms of `Term ℕ` are the λ-terms up to α-equivalence, and on them this is
β-conversion. Cslib's `FullBeta` takes no step from a term that is not locally closed
(`FullBeta.steps_lc_or_rfl`), so on such a term the problem is syntactic equality. Every instance
built by the reductions is locally closed (`Foundations.LambdaCalculus.lc_tr`).

The decision problem takes one argument, a pair (`DecisionProblem`); `decisionProblem_mk` states it
curried, by `Iff.rfl`. `BetaConvProblem` names it.

To audit the definition, read `Convertible`, `decisionProblem_mk` and `convertible_iff`, which
states the problem in Cslib's and Mathlib's terms; all are pinned in `scripts/HeadlineTest.lean`.

## Main definitions

* `Convertible`: the problem, curried. `DecisionProblem`, `BetaConvProblem`: on pairs.

## Main statements

* `decisionProblem_mk`: the problem on pairs is the curried problem.
* `convertible_iff`: the problem in Cslib's and Mathlib's terms, a common reduct under `FullBeta`.
* `convertible_iff_eqvGen`, `decisionProblem_iff_eqvGen`: the equivalence closure of `FullBeta`.

## References

* [A. Church, *An Unsolvable Problem of Elementary Number Theory*][Church1936]
  (for the λI-calculus)
-/

namespace DiagonaLean.BetaConv

open Cslib LambdaCalculus.LocallyNameless.Untyped Term Relation

/-! ### The problem -/

/-- **β-convertibility of λ-terms**: do `M` and `N` have a common β-reduct? Partially applied,
`Convertible M` is the β-convertibility class of `M`. -/
abbrev Convertible (M N : Term ℕ) : Prop := Foundations.LambdaCalculus.Conv M N

/-- **β-convertibility in Cslib's and Mathlib's terms**: a common reduct under `FullBeta`. -/
theorem convertible_iff (M N : Term ℕ) :
    Convertible M N ↔ ∃ P, ReflTransGen FullBeta M P ∧ ReflTransGen FullBeta N P := Iff.rfl

/-- Two λ-terms are β-convertible iff they are related by `EqvGen FullBeta`. -/
theorem convertible_iff_eqvGen (M N : Term ℕ) : Convertible M N ↔ EqvGen FullBeta M N :=
  ⟨fun h => join_reflTransGen_le_eqvGen _ _ h, fun h => confluent_fullBeta.to_churchRosser h⟩

/-! ### The problem on a pair, for the reductions and the computability statements -/

/-- **The problem on a pair**, for the reductions and the computability statements:
`Convertible` on its two terms. Read it curried, `decisionProblem_mk`. -/
def DecisionProblem (i : Term ℕ × Term ℕ) : Prop := Convertible i.1 i.2

/-- β-conversion of λ-terms. -/
abbrev BetaConvProblem : Term ℕ × Term ℕ → Prop := DecisionProblem

/-- The problem on a pair is the curried problem. -/
@[simp] theorem decisionProblem_mk (M N : Term ℕ) : DecisionProblem (M, N) ↔ Convertible M N :=
  Iff.rfl

/-- Two λ-terms have a common β-reduct iff they are related by `EqvGen FullBeta`. -/
theorem decisionProblem_iff_eqvGen (i : Term ℕ × Term ℕ) :
    DecisionProblem i ↔ EqvGen FullBeta i.1 i.2 :=
  convertible_iff_eqvGen i.1 i.2

end DiagonaLean.BetaConv
