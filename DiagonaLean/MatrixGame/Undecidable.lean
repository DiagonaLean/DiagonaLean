/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.MatrixGame.Reductions.MatMort_to_MatrixGame
import DiagonaLean.MatMort.Undecidable
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Undecidability of the matrix game

The reduction `signGame` is computable (`computable_signGame`), so the halting reduction of matrix
mortality gives one for the matrix game (`MatrixGame.fromHalt`). Hence the matrix game is
halting-hard (`MatrixGame.haltHard`), undecidable (`MatrixGame.not_computablePred`), and no Turing
machine decides it under any computable encoding (`MatrixGame.not_machineDecidable`), all stated by
`halt_results`; even when Adam's moves are fixed to `1` and `-1`
(`MatrixGame.not_machineDecidable_signGame`).

## Main statements

* `MatrixGame.fromHalt`: the halting reduction, proved computable.
* `MatrixGame.haltHard`, `MatrixGame.not_computablePred`, `MatrixGame.not_machineDecidable`
  (`halt_results`).
* `MatrixGame.not_machineDecidable_signGame`: the same when Adam plays only `1` and `-1`.

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatrixGame

open DiagonaLean.MatrixGame.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- **The matrix game is halting-hard**: matrix mortality is (`MatMort.fromHalt`), and
`MatrixGame.synthFromMatMort` computes the computable function `signGame`. -/
def fromHalt : HaltReduction DecisionProblem := by
  reduce_from MatMort.fromHalt via synthFromMatMort

halt_results DecisionProblem from fromHalt

/-- **No Turing machine decides the matrix game when Adam's moves are `1` and `-1`**, under any
computable encoding of Eve's moves. -/
theorem not_machineDecidable_signGame {enc : Finset Position → List Bool} (he : Computable enc) :
    ¬ MachineDecidable enc (fun moves => DecisionProblem (signGame moves)) := by
  have h : (fun moves => DecisionProblem (signGame moves)) = MatMort.DecisionProblem :=
    funext fun moves => propext (matMort_reducesto_matrixGame_spec moves).symm
  rw [h]
  exact MatMort.not_machineDecidable he

end DiagonaLean.MatrixGame
