/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.MatrixGame.Reductions.MatMort_to_MatrixGame
import DiagonaLean.MatMort.Undecidable
import DiagonaLean.Foundations.Computability.UndecTransfer

@[expose] public section

/-! # The matrix game is not a computable predicate

The reduction `signGame` is computable (`computable_signGame`), so the halting reduction of matrix
mortality gives one for the matrix game (`MatrixGame.fromHalt`). Matrix mortality is not a
computable predicate (`MatMort.not_computablePred`), so the matrix game is not a computable
predicate (`not_computablePred_matrixGame`), and no Turing machine decides it under any computable
encoding (`not_machineDecidable_matrixGame`), even when Adam's moves are fixed to `1` and `-1`
(`not_machineDecidable_signGame`).

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatrixGame.MachineLevel

open DiagonaLean.MatrixGame.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

/-- **The matrix game is halting-hard**: matrix mortality is (`MatMort.fromHalt`), and
`MatrixGame.synthFromMatMort` computes the computable function `signGame`. -/
def _root_.DiagonaLean.MatrixGame.fromHalt : HaltReduction DecisionProblem := by
  reduce_from MatMort.fromHalt via MatrixGame.synthFromMatMort

/-- **The matrix game is not a computable predicate.** -/
@[undecHardness] theorem not_computablePred_matrixGame : ¬ ComputablePred DecisionProblem := by
  reduce_from MatMort.not_computablePred via synthFromMatMort

/-- **No Turing machine decides the matrix game**, under any computable encoding of the arenas. -/
theorem not_machineDecidable_matrixGame {enc : Arena → List Bool} (he : Computable enc) :
    ¬ MachineDecidable enc DecisionProblem := by
  reduce_from MatMort.not_computablePred via synthFromMatMort

/-- **No Turing machine decides the matrix game when Adam's moves are `1` and `-1`**, under any
computable encoding of Eve's moves. -/
theorem not_machineDecidable_signGame {enc : Finset Position → List Bool} (he : Computable enc) :
    ¬ MachineDecidable enc (fun moves => DecisionProblem (signGame moves)) := by
  have h : (fun moves => DecisionProblem (signGame moves)) = MatMort.DecisionProblem :=
    funext fun moves => propext (matMort_reducesto_matrixGame_spec moves).symm
  rw [h]
  exact MatMort.not_machineDecidable he

end DiagonaLean.MatrixGame.MachineLevel
