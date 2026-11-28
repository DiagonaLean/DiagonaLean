/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.GrammarMem.Reductions.Halt_to_GrammarMem

@[expose] public section

/-! # Membership for grammar codes is synthetically halting-hard

`GrammarMem.synthFromHalt` many-one reduces the halting problem to membership for grammar codes,
through `haltToGrammarMem` (`Reductions/Halt_to_GrammarMem.lean`), so membership is synthetically
halting-hard. The undecidability results are in `Undecidable.lean`.

## References

* N. Chomsky, *On certain formal properties of grammars* (1959)
* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace DiagonaLean.GrammarMem.Reduction

open DiagonaLean.Halt DiagonaLean.Synthetic.Definitions

variable {T : Type}

/-- **Membership for grammar codes is synthetically halting-hard.** The halting problem many-one
reduces to membership for grammar codes, through `haltToGrammarMem`. -/
def _root_.DiagonaLean.GrammarMem.synthFromHalt : HaltProblem ⪯_s @DecisionProblem T :=
  ⟨haltToGrammarMem, halt_reducesto_grammarMem_spec⟩

end DiagonaLean.GrammarMem.Reduction
