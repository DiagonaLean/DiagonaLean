/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.Inequality

@[expose] public section

/-! # Equality in pre-Kleene algebra with commutativity

An instance (`EqInstance α`) is a pair of expressions over the doubled alphabet `α ⊕ α`.
`DecisionProblem` asks whether the two sides are provably equal in pre-Kleene algebra in which
every left letter commutes with every right letter (`DComm`), that is, equal in `T Σ̈`.
`TermEqProblem` fixes the paper's alphabet `Σ = {0, 1}`, here `Bool`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.TermEq

open DiagonaLean.Foundations.KleeneAlgebra

/-- `DecisionProblem i` holds iff the two sides of `i` are provably equal in pre-Kleene algebra
with the commutations `DComm` between left and right letters: equality on `T Σ̈`. -/
def DecisionProblem {α : Type} (i : EqInstance α) : Prop := RExp.Equiv DComm i.1 i.2

/-- Equality on `T Σ̈` over `Σ = {0, 1}`. -/
abbrev TermEqProblem : EqInstance Bool → Prop := DecisionProblem

end DiagonaLean.TermEq
