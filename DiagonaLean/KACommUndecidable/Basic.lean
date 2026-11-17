/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KACommUndecidable.KleeneAlgebra.Inequality

@[expose] public section

/-! # The decision problems of "Kleene algebra with commutativity conditions is undecidable"

An instance (`EqInstance α`) is a pair of expressions over the doubled alphabet `α ⊕ α`, in which
every left letter `.inl a` commutes with every right letter `.inr b` (`DComm`). The paper asks
four questions about such a pair, from the most syntactic to the most semantic:

* `TermEq.DecisionProblem`: are the two sides provably equal in pre-Kleene algebra with these
  commutations, that is, equal in `T Σ̈`?
* `KATermEq.DecisionProblem`: are they provably equal in Kleene algebra with these commutations,
  that is, equal in `K Σ̈`? This is the theory of the paper's title.
* `LangEq.DecisionProblem`: do they have the same language in the model `TD.pl`, that is, are they
  equal in `L Σ̈`?
* `ModelLe.DecisionProblem`: is the language of the first contained in the language of the second,
  that is, does `e ≤ f` hold in `L Σ̈`?

`TermEqProblem`, `KATermEqProblem` and `LangEqProblem` fix the paper's alphabet `Σ = {0, 1}`, here
`Bool`. Each problem keeps its own namespace, so that its results read as `TermEq.…`,
`LangEq.…` and so on.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.TermEq

open DiagonaLean.KACommUndecidable.KleeneAlgebra

/-- `DecisionProblem i` holds iff the two sides of `i` are provably equal in pre-Kleene algebra
with the commutations `DComm` between left and right letters: equality on `T Σ̈`. -/
def DecisionProblem {α : Type} (i : EqInstance α) : Prop := RExp.Equiv DComm i.1 i.2

/-- Equality on `T Σ̈` over `Σ = {0, 1}`. -/
abbrev TermEqProblem : EqInstance Bool → Prop := DecisionProblem

end DiagonaLean.TermEq

namespace DiagonaLean.KATermEq

open DiagonaLean.KACommUndecidable.KleeneAlgebra

/-- `DecisionProblem i` holds iff the two sides of `i` are provably equal in Kleene algebra with
the commutations `DComm` between left and right letters: equality on `K Σ̈`. -/
def DecisionProblem {α : Type} (i : EqInstance α) : Prop := RExp.KAEquiv DComm i.1 i.2

/-- Equality on `K Σ̈` over `Σ = {0, 1}`. -/
abbrev KATermEqProblem : EqInstance Bool → Prop := DecisionProblem

end DiagonaLean.KATermEq

namespace DiagonaLean.LangEq

open DiagonaLean.KACommUndecidable.KleeneAlgebra

/-- `DecisionProblem i` holds iff the two sides of `i` have the same language in the model
`TD.pl`: equality on `L Σ̈`. -/
def DecisionProblem {α : Type} (i : EqInstance α) : Prop :=
  TD.pl (FreePreKA.mk i.1 : TD α) = TD.pl (FreePreKA.mk i.2)

/-- Equality on `L Σ̈` over `Σ = {0, 1}`. -/
abbrev LangEqProblem : EqInstance Bool → Prop := DecisionProblem

end DiagonaLean.LangEq

namespace DiagonaLean.ModelLe

open DiagonaLean.KACommUndecidable.KleeneAlgebra

/-- `DecisionProblem i` holds iff the language of `i.1` is contained in the language of `i.2` in
the model `TD.pl`: `e ≤ f` in `L Σ̈`. -/
def DecisionProblem {α : Type} (i : EqInstance α) : Prop :=
  TD.pl (FreePreKA.mk i.1 : TD α) ≤ TD.pl (FreePreKA.mk i.2)

end DiagonaLean.ModelLe
