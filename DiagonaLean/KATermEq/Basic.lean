/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.Inequality

@[expose] public section

/-! # Equality in Kleene algebra with commutativity

An instance (`EqInstance α`) is a pair of expressions over the doubled alphabet `α ⊕ α`.
`DecisionProblem` asks whether the two sides are provably equal in Kleene algebra in which every
left letter commutes with every right letter (`DComm`), that is, equal in `K Σ̈`.
`KATermEqProblem` fixes the paper's alphabet `Σ = {0, 1}`, here `Bool`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KATermEq

open DiagonaLean.Foundations.KleeneAlgebra

/-- `DecisionProblem i` holds iff the two sides of `i` are provably equal in Kleene algebra with
the commutations `DComm` between left and right letters: equality on `K Σ̈`. -/
def DecisionProblem {α : Type} (i : EqInstance α) : Prop := RExp.KAEquiv DComm i.1 i.2

/-- Equality on `K Σ̈` over `Σ = {0, 1}`. -/
abbrev KATermEqProblem : EqInstance Bool → Prop := DecisionProblem

end DiagonaLean.KATermEq
