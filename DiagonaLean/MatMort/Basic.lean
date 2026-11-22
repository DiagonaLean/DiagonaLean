/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Mathlib.Data.Matrix.Basic

/-! # The Matrix Mortality Problem

The matrix mortality predicate `DecisionProblem` on finite sets of `3 × 3` integer matrices. Its
former alias `MatMortProblem` is deprecated.

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

@[expose] public section

namespace DiagonaLean.MatMort
open Matrix

/-- A set of matrices has a mortality solution if there exists a finite sequence
  (list) of matrices drawn from the set such that their product is the zero matrix. -/
def DecisionProblem (Ms : Finset (Matrix (Fin 3) (Fin 3) ℤ)) : Prop :=
  ∃ Ms' : List (Matrix (Fin 3) (Fin 3) ℤ), (∀ M ∈ Ms', M ∈ Ms) ∧ Ms'.prod = 0

/-- The former alias of `DecisionProblem`. -/
@[deprecated DecisionProblem (since := "2026-11-23")]
abbrev MatMortProblem : (Ms : Finset (Matrix (Fin 3) (Fin 3) ℤ)) → Prop := DecisionProblem

end DiagonaLean.MatMort
