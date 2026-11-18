/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence

@[expose] public section

/-! # β-conversion of λ-terms

An instance is a pair of locally nameless λ-terms over the variables `ℕ`. `DecisionProblem` asks
whether the two terms are β-convertible, that is, whether they have a common reduct under
Cslib's full β-reduction `FullBeta`. By confluence (`confluent_fullBeta`) this is the
equivalence closure of `FullBeta` (`decisionProblem_iff_eqvGen`). `BetaConvProblem` names it.

The locally closed terms of `Term ℕ` are the λ-terms up to α-equivalence, and on them this is
β-conversion. Cslib's `FullBeta` takes no step from a term that is not locally closed
(`FullBeta.steps_lc_or_rfl`), so on such a term the problem is syntactic equality. Every instance
built by the reductions is locally closed (`Foundations.LambdaCalculus.lc_tr`).

## References

* [A. Church, *An Unsolvable Problem of Elementary Number Theory*][Church1936]
  (for the λI-calculus)
-/

namespace DiagonaLean.BetaConv

open Cslib LambdaCalculus.LocallyNameless.Untyped Term Relation

/-- `DecisionProblem i` holds iff the two terms of `i` have a common β-reduct. -/
def DecisionProblem (i : Term ℕ × Term ℕ) : Prop := Join (ReflTransGen FullBeta) i.1 i.2

/-- β-conversion of λ-terms. -/
abbrev BetaConvProblem : Term ℕ × Term ℕ → Prop := DecisionProblem

/-- Two λ-terms have a common β-reduct iff they are related by `EqvGen FullBeta`. -/
theorem decisionProblem_iff_eqvGen (i : Term ℕ × Term ℕ) :
    DecisionProblem i ↔ EqvGen FullBeta i.1 i.2 :=
  ⟨fun h => join_reflTransGen_le_eqvGen _ _ h, fun h => confluent_fullBeta.to_churchRosser h⟩

end DiagonaLean.BetaConv
