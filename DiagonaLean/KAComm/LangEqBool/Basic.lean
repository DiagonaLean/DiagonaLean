/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KleeneAlgebra.Inequality

@[expose] public section

/-! # Equality on `L Σ̈` over `{0, 1}`

An instance (`InstB`) is a pair of expressions over the doubled alphabet `Bool ⊕ Bool`, in which
every left letter commutes with every right letter (`DComm`). `DecisionProblem` asks whether the two
sides have the same language in the model `TD.pl`, that is, whether they are equal in `L Σ̈` for
`Σ = {0, 1}`. `LangEqBoolProblem` names it.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.LangEqBool

open DiagonaLean.KAComm.KleeneAlgebra

/-- `DecisionProblem i` holds iff the two sides of `i` have the same language in the model
`TD.pl`. -/
def DecisionProblem (i : InstB) : Prop :=
  TD.pl (FreePreKA.mk i.1 : TD Bool) = TD.pl (FreePreKA.mk i.2)

/-- Equality on `L Σ̈` over `Σ = {0, 1}`. -/
abbrev LangEqBoolProblem : InstB → Prop := DecisionProblem

end DiagonaLean.KAComm.LangEqBool
