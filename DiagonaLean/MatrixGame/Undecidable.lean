/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.MatrixGame.Reductions.MatMort_to_MatrixGame
import DiagonaLean.MatMort.Undecidable
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Undecidability of the matrix game

The problem is whether Eve has a winning strategy (`EveWins`, `DecisionProblem`, `Basic.lean`): a
legal strategy that brings the product from the identity to zero against every legal strategy of
Adam. Every statement here is about that property.

The reduction `signGame` is computable (`computable_signGame`), so the halting reduction of matrix
mortality gives one for the matrix game (`MatrixGame.fromHalt`). Hence whether Eve has a winning
strategy is halting-hard (`MatrixGame.haltHard`), undecidable (`MatrixGame.not_computablePred`),
and no Turing machine decides it under any computable encoding of the arenas
(`MatrixGame.not_machineDecidable`), all stated by `halt_results`; even when Adam's moves are fixed
to `1` and `-1` (`MatrixGame.not_machineDecidable_signGame`), where Eve has a winning strategy
exactly with the mortal move sets (`MatrixGame.setOf_signGame_eq_mortal`).

## Main statements

* `MatrixGame.fromHalt`: the halting reduction, proved computable.
* `MatrixGame.haltHard`, `MatrixGame.not_computablePred`, `MatrixGame.not_machineDecidable`
  (`halt_results`).
* `MatrixGame.not_machineDecidable_signGame`: the same when Adam plays only `1` and `-1`.

All are about the existence of a winning strategy for Eve; the proofs reach it through its
inductive form (`decisionProblem_iff_forceZero`, `Attractor.lean`).

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatrixGame

open DiagonaLean.MatrixGame.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- **Whether Eve has a winning strategy is halting-hard**: matrix mortality is
(`MatMort.fromHalt`), and `MatrixGame.synthFromMatMort` computes the computable function
`signGame`. -/
def fromHalt : HaltReduction DecisionProblem := by
  reduce_from MatMort.fromHalt via synthFromMatMort

halt_results DecisionProblem from fromHalt

/-- **No Turing machine decides whether Eve has a winning strategy when Adam's moves are `1` and
`-1`**, under any computable encoding of Eve's moves: Eve wins exactly with the mortal move sets
(`setOf_signGame_eq_mortal`), and no machine decides mortality (`MatMort.not_machineDecidable`). -/
theorem not_machineDecidable_signGame {enc : Finset Position → List Bool} (he : Computable enc) :
    ¬ MachineDecidable enc (fun moves => DecisionProblem (signGame moves)) :=
  (show (fun moves => DecisionProblem (signGame moves)) = MatMort.DecisionProblem from
    setOf_signGame_eq_mortal) ▸ MatMort.not_machineDecidable he

end DiagonaLean.MatrixGame
