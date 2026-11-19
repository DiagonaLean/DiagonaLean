/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KleeneAlgebra.Inequality

@[expose] public section

/-! # Inclusion in `L Σ̈`

An instance (`Inst`) is a pair of expressions over the doubled alphabet `ℕ ⊕ ℕ`, in which every left
letter commutes with every right letter (`DComm`). `DecisionProblem` asks whether the language of
the first side is contained in the language of the second in the model `TD.pl`, that is, whether
`e ≤ f` holds in `L Σ̈` for `Σ = ℕ`. `ModelLeProblem` names it.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.ModelLe

open DiagonaLean.KAComm.KleeneAlgebra

/-- `DecisionProblem i` holds iff the language of `i.1` is contained in the language of `i.2` in the
model `TD.pl`. -/
def DecisionProblem (i : Inst) : Prop :=
  TD.pl (FreePreKA.mk i.1 : TD ℕ) ≤ TD.pl (FreePreKA.mk i.2)

/-- Inclusion in `L Σ̈` over `Σ = ℕ`. -/
abbrev ModelLeProblem : Inst → Prop := DecisionProblem

end DiagonaLean.KAComm.ModelLe
