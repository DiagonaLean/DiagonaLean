/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KleeneAlgebra.Inequality

@[expose] public section

/-! # Equality on `L Σ̈`

An instance (`Inst`) is a pair of expressions over the doubled alphabet `ℕ ⊕ ℕ`, in which every left
letter commutes with every right letter (`DComm`). `DecisionProblem` asks whether the two sides have
the same language in the model `TD.pl`, that is, whether they are equal in `L Σ̈` for `Σ = ℕ`.
`LangEqProblem` names it.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.LangEq

open DiagonaLean.KAComm.KleeneAlgebra

/-- `DecisionProblem i` holds iff the two sides of `i` have the same language in the model
`TD.pl`. -/
def DecisionProblem (i : Inst) : Prop :=
  TD.pl (FreePreKA.mk i.1 : TD ℕ) = TD.pl (FreePreKA.mk i.2)

/-- Equality on `L Σ̈` over `Σ = ℕ`. -/
abbrev LangEqProblem : Inst → Prop := DecisionProblem

end DiagonaLean.KAComm.LangEq
