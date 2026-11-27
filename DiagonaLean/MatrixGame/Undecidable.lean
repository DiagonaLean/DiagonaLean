/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.MatMort.SynthHardness
import DiagonaLean.MatrixGame.Reductions.MatMort_to_MatrixGame
import DiagonaLean.MatMort.Undecidable
import DiagonaLean.Synthetic.Tactics.UndecFrom

@[expose] public section

/-! # Undecidability of the matrix game

Matrix mortality is synthetically halting-hard (`MatMort.synthFromHalt`), and
`MatrixGame.synthFromMatMort` reduces it to the matrix game, so the matrix game is synthetically
halting-hard (`MatrixGame.synthFromHalt`). The machine-level statements are in `MachineLevel.lean`.

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatrixGame.Reduction

open DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

/-- **The matrix game is synthetically halting-hard.** -/
@[undecReduction] def _root_.DiagonaLean.MatrixGame.synthFromHalt :
    SynthHaltReduction DecisionProblem := by
  reduce_from MatMort.synthFromHalt via synthFromMatMort

end DiagonaLean.MatrixGame.Reduction
