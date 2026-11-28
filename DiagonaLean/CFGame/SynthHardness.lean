/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CFGame.Reductions.ListHalt_to_CFGame
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # Active context-free games are synthetically halting-hard

`listToCFGame` (`Reductions/ListHalt_to_CFGame.lean`) many-one reduces halting of list machines
given by a table to the combined decision problem for context-free games, over letters coded as
numbers (`listHalt_reducesto_cfGame_spec`). Halting of list machines is synthetically
halting-hard (`ListHalt.synthFromHalt`), so the combined problem is synthetically halting-hard
(`CFGame.synthFromHalt`). This
is the combined form of Theorem 4.2 of Muscholl, Schwentick and Segoufin. The undecidability
results are in `Undecidable.lean`.

## Main statements

* `CFGame.synthFromHalt`: the halting problem reduces to context-free games.

## References

* [A. Muscholl, T. Schwentick, L. Segoufin,
  *Active Context-Free Games*][MuschollSchwentickSegoufin2006], Theorem 4.2
-/

namespace DiagonaLean.CFGame.Reduction

open DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions

/-- **Active context-free games are synthetically halting-hard**: halting of list machines is
(`ListHalt.synthFromHalt`), and `listToCFGame` reduces it to context-free games. -/
@[undecReduction] def _root_.DiagonaLean.CFGame.synthFromHalt :
    SynthHaltReduction (@DecisionProblem ℕ) := by
  synth_reduce_from ListHalt.synthFromHalt with (listToCFGame none)
    using (listHalt_reducesto_cfGame_spec none)

end DiagonaLean.CFGame.Reduction
