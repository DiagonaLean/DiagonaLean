/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.FreeKA

@[expose] public section

/-! # Equality in Kleene algebra with commutativity, as a decision problem

An instance (`EqInstance α`) is a pair of expressions over the doubled alphabet `α ⊕ α`. There are
three questions about it, one for each structure `X` in Theorem 18 of the paper:

* `TermEq.DecisionProblem`: the two sides are provably equal in pre-Kleene algebra with
  commutativity, that is, equal in `T Σ̈`;
* `KATermEq.DecisionProblem`: they are provably equal in Kleene algebra with commutativity, equal
  in `K Σ̈`;
* `LangEq.DecisionProblem`: they have the same language, equal in `L Σ̈`.

As with `PCP.DecisionProblem` and `PCP.PCProblem`, each problem is defined for any alphabet, and
`TermEqProblem`, `KATermEqProblem` and `LangEqProblem` fix the paper's alphabet `Σ = {0, 1}`,
here `Bool`. `Undec.Inst` and `Reduction.InstB` are the instances over `ℕ` and over `Bool`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm

/-- An instance of equality: two expressions over the doubled alphabet `α ⊕ α`. -/
abbrev EqInstance (α : Type) := RExp (α ⊕ α) × RExp (α ⊕ α)

/-- An instance over the doubled alphabet `ℕ ⊕ ℕ`. -/
abbrev Undec.Inst := EqInstance ℕ

/-- An instance over the doubled alphabet `Bool ⊕ Bool`, the paper's `Σ = {0, 1}`. -/
abbrev Reduction.InstB := EqInstance Bool

namespace TermEq

/-- `DecisionProblem i` holds iff the two sides of `i` are provably equal in pre-Kleene algebra
with the commutations `DComm` between left and right letters: equality on `T Σ̈`. -/
def DecisionProblem {α : Type} (i : EqInstance α) : Prop := RExp.Equiv DComm i.1 i.2

end TermEq

namespace KATermEq

/-- `DecisionProblem i` holds iff the two sides of `i` are provably equal in Kleene algebra with
the commutations `DComm` between left and right letters: equality on `K Σ̈`. -/
def DecisionProblem {α : Type} (i : EqInstance α) : Prop := RExp.KAEquiv DComm i.1 i.2

end KATermEq

namespace LangEq

/-- `DecisionProblem i` holds iff the two sides of `i` have the same language in the model
`TD.pl`: equality on `L Σ̈`. -/
def DecisionProblem {α : Type} (i : EqInstance α) : Prop :=
  TD.pl (FreePreKA.mk i.1 : TD α) = TD.pl (FreePreKA.mk i.2)

end LangEq

/-- Equality on `T Σ̈` over `Σ = {0, 1}`. -/
abbrev TermEqProblem : EqInstance Bool → Prop := TermEq.DecisionProblem

/-- Equality on `K Σ̈` over `Σ = {0, 1}`. -/
abbrev KATermEqProblem : EqInstance Bool → Prop := KATermEq.DecisionProblem

/-- Equality on `L Σ̈` over `Σ = {0, 1}`. -/
abbrev LangEqProblem : EqInstance Bool → Prop := LangEq.DecisionProblem

end DiagonaLean.KAComm
