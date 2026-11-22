/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.GrammarMem.Reductions.Halt_to_GrammarMem

@[expose] public section

/-! # Undecidability of membership for grammar codes

`GrammarMem.synthFromHalt` (`Reductions/Halt_to_GrammarMem.lean`) many-one reduces the halting
problem to membership for grammar codes, so membership is synthetically halting-hard. The
machine-level statements are in `MachineLevel.lean`.

## References

* N. Chomsky, *On certain formal properties of grammars* (1959)
* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace DiagonaLean.GrammarMem.Reduction

open DiagonaLean.Synthetic.Definitions

variable {T : Type}

/-- The former name of `GrammarMem.synthFromHalt`. -/
@[deprecated DiagonaLean.GrammarMem.synthFromHalt (since := "2026-11-23")]
abbrev undecidableGrammarMem := @DiagonaLean.GrammarMem.synthFromHalt

end DiagonaLean.GrammarMem.Reduction
