/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.Inequality

@[expose] public section

/-! # Language inclusion with commutativity

An instance (`EqInstance α`) is a pair of expressions over the doubled alphabet `α ⊕ α`.
`DecisionProblem` asks whether the language of the first side is contained in the language of the
second in the model `TD.pl`, in which every left letter commutes with every right letter, that is,
whether `e ≤ f` holds in `L Σ̈`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.ModelLe

open DiagonaLean.Foundations.KleeneAlgebra

/-- `DecisionProblem i` holds iff the language of `i.1` is contained in the language of `i.2` in
the model `TD.pl`: `e ≤ f` in `L Σ̈`. -/
def DecisionProblem {α : Type} (i : EqInstance α) : Prop :=
  TD.pl (FreePreKA.mk i.1 : TD α) ≤ TD.pl (FreePreKA.mk i.2)

end DiagonaLean.ModelLe
