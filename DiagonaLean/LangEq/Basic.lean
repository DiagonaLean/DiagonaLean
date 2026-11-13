/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.Inequality

@[expose] public section

/-! # Language equality with commutativity

An instance (`EqInstance α`) is a pair of expressions over the doubled alphabet `α ⊕ α`.
`DecisionProblem` asks whether the two sides have the same language in the model `TD.pl`, in which
every left letter commutes with every right letter, that is, whether they are equal in `L Σ̈`.
`LangEqProblem` fixes the paper's alphabet `Σ = {0, 1}`, here `Bool`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.LangEq

open DiagonaLean.Foundations.KleeneAlgebra

/-- `DecisionProblem i` holds iff the two sides of `i` have the same language in the model
`TD.pl`: equality on `L Σ̈`. -/
def DecisionProblem {α : Type} (i : EqInstance α) : Prop :=
  TD.pl (FreePreKA.mk i.1 : TD α) = TD.pl (FreePreKA.mk i.2)

/-- Equality on `L Σ̈` over `Σ = {0, 1}`. -/
abbrev LangEqProblem : EqInstance Bool → Prop := DecisionProblem

end DiagonaLean.LangEq
