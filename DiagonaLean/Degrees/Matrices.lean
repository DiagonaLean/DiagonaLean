/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.MatMort.Undecidable
import DiagonaLean.MatMort.RE
import DiagonaLean.MatrixGame.Undecidable
import DiagonaLean.MatrixGame.RE
import DiagonaLean.Foundations.Computability.HaltComplete

@[expose] public section

/-! # Matrix mortality and the matrix game have the same degree

Matrix mortality for `3 × 3` integer matrices and the matrix game (whether Eve has a winning
strategy) are each halting-hard (`MatMort.haltHard`, `MatrixGame.haltHard`) and recursively
enumerable (`MatMort.rePred`, `MatrixGame.rePred`). The halting problem is complete for the
recursively enumerable problems (`manyOneReducible_haltCanon_of_rePred`), so each of the two is,
and they are many-one equivalent. One direction is the reduction `signGame` (Adam plays `1` and
`-1`); the other, from the game to mortality, comes only through the halting problem.

## Main statements

* `MatMort.complete`, `MatrixGame.complete`: every recursively enumerable problem many-one reduces
  to each.
* `Degrees.matMort_equiv_matrixGame`: the two are many-one equivalent.

## References

* H. Rogers, *Theory of Recursive Functions and Effective Computability* (1967), Section 7.2
* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean

open Foundations.Computability

variable {β : Type*} [Primcodable β] {p : β → Prop}

/-- **Matrix mortality is complete for the r.e. problems.** -/
theorem MatMort.complete (hp : REPred p) : ManyOneReducible p MatMort.DecisionProblem :=
  .of_rePred_of_haltHard hp MatMort.haltHard

/-- **The matrix game is complete for the r.e. problems.** -/
theorem MatrixGame.complete (hp : REPred p) : ManyOneReducible p MatrixGame.DecisionProblem :=
  .of_rePred_of_haltHard hp MatrixGame.haltHard

namespace Degrees

/-- **Matrix mortality and the matrix game are many-one equivalent.** -/
theorem matMort_equiv_matrixGame :
    ManyOneEquiv MatMort.DecisionProblem MatrixGame.DecisionProblem :=
  manyOneEquiv_of_haltHard_of_rePred MatMort.haltHard MatMort.rePred MatrixGame.haltHard
    MatrixGame.rePred

end Degrees

end DiagonaLean
