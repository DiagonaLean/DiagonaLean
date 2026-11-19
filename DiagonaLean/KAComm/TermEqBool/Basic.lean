/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KleeneAlgebra.Inequality

@[expose] public section

/-! # Equality on `T Σ̈` over `{0, 1}`

An instance (`InstB`) is a pair of expressions over the doubled alphabet `Bool ⊕ Bool`, in which
every left letter commutes with every right letter (`DComm`). `DecisionProblem` asks whether the two
sides are provably equal in pre-Kleene algebra with these commutations (`RExp.Equiv DComm`), that
is, equal in `T Σ̈` for `Σ = {0, 1}`. `TermEqBoolProblem` names it.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.TermEqBool

open DiagonaLean.KAComm.KleeneAlgebra

/-- `DecisionProblem i` holds iff the two sides of `i` are provably equal in pre-Kleene algebra with
the commutations `DComm` between left and right letters. -/
def DecisionProblem (i : InstB) : Prop :=
  RExp.Equiv DComm i.1 i.2

/-- Equality on `T Σ̈` over `Σ = {0, 1}`. -/
abbrev TermEqBoolProblem : InstB → Prop := DecisionProblem

end DiagonaLean.KAComm.TermEqBool
