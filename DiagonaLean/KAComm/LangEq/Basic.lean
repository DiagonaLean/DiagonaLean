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

To audit the definition, read `decisionProblem_mk`: the problem on a pair `(e, f)` in its curried
form. It is pinned in `scripts/HeadlineTest.lean`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.LangEq

open DiagonaLean.KAComm.KleeneAlgebra

/-! ### The problem on instances, for the reductions and the computability statements -/

/-- **The problem on a pair `(e, f)` of expressions**, for the reductions and the computability
statements: equality of the languages of `e` and `f`. Read it curried, `decisionProblem_mk`. -/
def DecisionProblem (i : Inst) : Prop :=
  TD.pl (FreePreKA.mk i.1 : TD ℕ) = TD.pl (FreePreKA.mk i.2)

/-- Equality on `L Σ̈` over `Σ = ℕ`. -/
abbrev LangEqProblem : Inst → Prop := DecisionProblem

/-- The problem on a pair `(e, f)` of expressions is the curried problem. -/
@[simp] theorem decisionProblem_mk (e f : RExp (ℕ ⊕ ℕ)) :
    DecisionProblem (e, f) ↔ TD.pl (FreePreKA.mk e : TD ℕ) = TD.pl (FreePreKA.mk f) := Iff.rfl

end DiagonaLean.KAComm.LangEq
