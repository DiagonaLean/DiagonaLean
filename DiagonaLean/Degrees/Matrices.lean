/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.Degrees.Complete

@[expose] public section

/-! # Matrix mortality and the matrix game have the same degree

Matrix mortality for `3 × 3` integer matrices and the matrix game (whether Eve has a winning
strategy) are each halting-hard (`MatMort.haltHard`, `MatrixGame.haltHard`) and recursively
enumerable (`MatMort.rePred`, `MatrixGame.rePred`). The halting problem is complete for the
recursively enumerable problems (`manyOneReducible_haltCanon_of_rePred`), so each of the two is
(`MatMort.complete`, `MatrixGame.complete`, in `Complete.lean`), and they are many-one equivalent
(`manyOneEquiv_of_complete`). One direction is the reduction `signGame` (Adam plays `1` and
`-1`); the other, from the game to mortality, comes only through the halting problem.

## Main statements

* `Degrees.matMort_equiv_matrixGame`: the two are many-one equivalent.

## References

* H. Rogers, *Theory of Recursive Functions and Effective Computability* (1967), Section 7.2
* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean

open Foundations.Computability

namespace Degrees

/-- **Matrix mortality and the matrix game are many-one equivalent.** -/
theorem matMort_equiv_matrixGame :
    ManyOneEquiv MatMort.DecisionProblem MatrixGame.DecisionProblem :=
  manyOneEquiv_of_complete _ _

end Degrees

end DiagonaLean
