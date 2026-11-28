/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CFGame.Reductions.ListHalt_to_CFGame
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Undecidability of active context-free games

`listToCFGame` (`Reductions/ListHalt_to_CFGame.lean`) reduces halting of list machines given by a
table to the combined decision problem for context-free games, over letters coded as numbers
(`listHalt_reducesto_cfGame_spec`), and it is primitive recursive (`listToCFGame_prim`). Halting of
list machines is halting-hard (`ListHalt.fromHalt`), so the combined problem is
(`CFGame.fromHalt`). This is the combined form of Theorem 4.2 of Muscholl, Schwentick and
Segoufin. The synthetic result is in `SynthHardness.lean`.

## Main statements

* `CFGame.fromHalt`: the combined decision problem for context-free games is halting-hard.
* By `halt_results`: `CFGame.haltHard`, `CFGame.not_computablePred`,
  `CFGame.not_machineDecidable`. Whether Juliet wins a context-free game from a word is
  halting-hard and undecidable, and no Turing machine decides it under any computable encoding.

## References

* [A. Muscholl, T. Schwentick, L. Segoufin,
  *Active Context-Free Games*][MuschollSchwentickSegoufin2006], Theorem 4.2
-/

namespace DiagonaLean.CFGame

open DiagonaLean.CFGame.Reduction DiagonaLean.Foundations.Computability

/-- **The combined decision problem for active context-free games is halting-hard**: halting of
list machines is (`ListHalt.fromHalt`), and `listToCFGame` reduces it to context-free games and
is primitive recursive. -/
def fromHalt : HaltReduction (@DecisionProblem ℕ) := by
  hard_reduce_from ListHalt.fromHalt with (listToCFGame none)
    using (listHalt_reducesto_cfGame_spec none)

halt_results (@DecisionProblem ℕ) from fromHalt

end DiagonaLean.CFGame
