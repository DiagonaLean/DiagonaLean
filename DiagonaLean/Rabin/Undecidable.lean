/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Rabin.Reductions.Halt_to_Rabin
import DiagonaLean.Foundations.Computability.UndecTransfer
import DiagonaLean.Foundations.Computability.Undecidable

@[expose] public section

/-! # Undecidability of winner determination in Rabin's game

The payoff program `.bounded (dataC w)` makes Player I win exactly when the machine coded by `w`
halts on its own code (`winner_bounded_iff`, `selfHalt_iff_test`). So winner determination is
undecidable (`Rabin.not_computablePred`), and no Turing machine decides it under any computable
encoding (`Rabin.not_machineDecidable`). The route is self-halting, not a reduction from
`HaltCanon`, so there is no `HaltReduction` and no `halt_results`; the two names are the ones
`halt_results` would give.

## Main statements

* `Rabin.not_computablePred`: winner determination is not a computable predicate.
* `Rabin.not_machineDecidable`: no Turing machine decides it, under any computable encoding.

## References

* [M. O. Rabin, *Effective computability of winning strategies*][Rabin1957]
-/

namespace DiagonaLean.Rabin

open DiagonaLean.Rabin.Reduction DiagonaLean.Foundations.Computability DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

/-- **Winner determination in Rabin's game is not a computable predicate.** -/
@[undecHardness] theorem not_computablePred : Undecidable DecisionProblem := by
  apply not_computablePred_of_selfHalt (code := fun w => PayoffCode.bounded (dataC w))
  · fun_prop
  · intro M
    exact selfHalt_iff_test.trans (winner_bounded_iff (dataC (encodeBoolTM M))).symm

/-- **No Turing machine decides winner determination in Rabin's game**, under any computable
encoding of the payoff programs. -/
theorem not_machineDecidable {enc : PayoffCode → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc DecisionProblem := by
  exact not_machineDecidable_of_not_computablePred henc not_computablePred

end DiagonaLean.Rabin
