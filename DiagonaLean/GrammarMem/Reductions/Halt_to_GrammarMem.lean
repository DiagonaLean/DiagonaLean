/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.GrammarMem.Reductions.SemiThue_to_GrammarMem
import DiagonaLean.SemiThue.Reductions.Halt_to_SemiThue

@[expose] public section

/-! # The halting problem reduces to membership for grammar codes

`haltToGrammarMem` sends a machine and an input to the grammar code of the rewriting system of
`SemiThue.Reduction.haltToSemiThue` (`ofSRS`: a fresh start symbol and the symbols
numbered from `1`), and the empty word. Every rule of that system has a non-empty left side
(`SemiThue.Reduction.haltToSemiThue_lhs_ne`), so the empty word is in the language iff the machine
halts (`halt_reducesto_grammarMem_spec`). The synthetic result `GrammarMem.synthFromHalt` is in
`SynthHardness.lean`.

## References

* N. Chomsky, *On certain formal properties of grammars* (1959)
* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace DiagonaLean.GrammarMem.Reduction

open DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.SemiThue.Reduction
  DiagonaLean.GrammarMem.Reduction DiagonaLean.Synthetic.Definitions

variable {T : Type}

/-- **The reduction.** The grammar code of the rewriting system of the normalised machine, and the
empty word. -/
def haltToGrammarMem (p : EncodableTM Bool × List Bool) : GrammarCode T × List T :=
  (ofSRS (haltToSemiThue p).1 (haltToSemiThue p).2.1, [])

/-- `haltToGrammarMem` witnesses the reduction from the halting problem to membership for grammar
codes. -/
theorem halt_reducesto_grammarMem_spec :
    HaltProblem ⪯_s[haltToGrammarMem] @DecisionProblem T := fun p =>
  (halt_reducesto_semiThue_spec p).trans (emptyWord_ofSRS_iff _ _ (haltToSemiThue_lhs_ne p)).symm

end DiagonaLean.GrammarMem.Reduction
