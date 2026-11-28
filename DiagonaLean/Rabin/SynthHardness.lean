/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Rabin.Reductions.Halt_to_Rabin

@[expose] public section

/-! # Winner determination in Rabin's game is synthetically halting-hard

`haltToRabin` (`Reductions/Halt_to_Rabin.lean`) many-one reduces the halting problem to winner
determination for finite payoff programs (`halt_reducesto_rabin_spec`), so winner determination
is synthetically halting-hard (`Rabin.synthFromHalt`). The undecidability results are in
`Undecidable.lean`.

## Main statements

* `Rabin.synthFromHalt`: the halting problem reduces to winner determination.

## References

* [M. O. Rabin, *Effective computability of winning strategies*][Rabin1957]
-/

namespace DiagonaLean.Rabin.Reduction

open DiagonaLean.Halt DiagonaLean.Synthetic.Definitions

/-- **Winner determination in Rabin's game is synthetically halting-hard**: the halting problem
many-one reduces to it through `haltToRabin`. -/
@[undecReduction] def _root_.DiagonaLean.Rabin.synthFromHalt : HaltProblem ⪯_s DecisionProblem :=
  ⟨haltToRabin, halt_reducesto_rabin_spec⟩

end DiagonaLean.Rabin.Reduction
