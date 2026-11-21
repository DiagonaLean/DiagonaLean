/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.GrammarMem.MachineLevel
import DiagonaLean.SemiThue.Undecidable

@[expose] public section

/-! # Undecidability of membership for unrestricted grammars

`haltToGrammarMem` sends a machine and an input to the grammar code of the rewriting system of
`SemiThue.Reduction.haltToSemiThue` (`MachineLevel.ofSRS`: a fresh start symbol and the symbols
numbered from `1`), and the empty word. Every rule of that system has a non-empty left side
(`tmRules_lhs_ne`), so the empty word is in the language iff the machine halts
(`halt_reducesto_grammarMem_spec`), and membership is `Undecidable` (`undecidableGrammarMem`). The
machine-level statements are in `MachineLevel.lean`.
-/

namespace DiagonaLean.GrammarMem.Reduction

open DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Foundations.Grammar DiagonaLean.SemiThue.Reduction DiagonaLean.GrammarMem.MachineLevel
  DiagonaLean.Synthetic.Notation

variable {T : Type}

/-- **The reduction.** The grammar code of the rewriting system of the normalised machine, and the
empty word. -/
def haltToGrammarMem (p : EncodableTM Bool × List Bool) : GrammarCode T × List T :=
  (ofSRS (haltToSemiThue p).1 (haltToSemiThue p).2.1, [])

theorem halt_reducesto_grammarMem_spec :
    HaltProblem ⪯ₘ[haltToGrammarMem] @DecisionProblem T := by
  intro p
  refine (halt_reducesto_semiThue_spec p).trans (emptyWord_ofSRS_iff _ _ ?_).symm
  intro lr hlr
  obtain ⟨lr₀, hlr₀, rfl⟩ := List.mem_map.1 hlr
  simpa using tmRules_lhs_ne lr₀ hlr₀

/-- The halting problem many-one reduces to membership for grammar codes, through
`haltToGrammarMem`. -/
def haltReducesGrammarMem : HaltProblem ⪯ₘ @DecisionProblem T :=
  ⟨haltToGrammarMem, halt_reducesto_grammarMem_spec⟩

/-- **Membership for grammar codes is `Undecidable`.** -/
def undecidableGrammarMem : Undecidable (@DecisionProblem T) := haltReducesGrammarMem

end DiagonaLean.GrammarMem.Reduction
