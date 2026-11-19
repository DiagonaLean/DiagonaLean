/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KleeneAlgebra.Inequality

@[expose] public section

/-! # Inclusion in `L Σ̈` over `{0, 1}`

An instance (`InstB`) is a pair of expressions over the doubled alphabet `Bool ⊕ Bool`, in which
every left letter commutes with every right letter (`DComm`). `DecisionProblem` asks whether the
language of the first side is contained in the language of the second in the model `TD.pl`, that is,
whether `e ≤ f` holds in `L Σ̈` for `Σ = {0, 1}`. `ModelLeBoolProblem` names it.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.ModelLeBool

open DiagonaLean.KAComm.KleeneAlgebra

/-- `DecisionProblem i` holds iff the language of `i.1` is contained in the language of `i.2` in the
model `TD.pl`. -/
def DecisionProblem (i : InstB) : Prop :=
  TD.pl (FreePreKA.mk i.1 : TD Bool) ≤ TD.pl (FreePreKA.mk i.2)

/-- Inclusion in `L Σ̈` over `Σ = {0, 1}`. -/
abbrev ModelLeBoolProblem : InstB → Prop := DecisionProblem

end DiagonaLean.KAComm.ModelLeBool
