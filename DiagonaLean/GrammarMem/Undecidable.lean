/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.GrammarMem.Reductions.HaltCanon_to_GrammarMem
import DiagonaLean.SemiThue.Undecidable
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Undecidability of membership for unrestricted grammars

`canonGCode` (`Reductions/HaltCanon_to_GrammarMem.lean`) reduces the halting problem on canonical
machines to the empty word problem for type 0 grammar codes, computably. Asking for the empty word
reduces that to membership. The synthetic result is in `SynthHardness.lean`.

## Main statements

* `GrammarMem.emptyWordFromHalt`: whether the empty word belongs to the language of a type 0
  grammar code is halting-hard.
* `GrammarMem.fromHalt`: membership for grammar codes is halting-hard.
* By `halt_results`: `GrammarMem.haltHard`, `GrammarMem.not_computablePred`,
  `GrammarMem.not_machineDecidable` for membership, and the same under `GrammarMem.EmptyWord` for
  the empty word in type 0 grammar codes: both are undecidable, and no Turing machine decides
  either under any computable encoding.

## References

* N. Chomsky, *On certain formal properties of grammars* (1959)
* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace DiagonaLean.GrammarMem

open DiagonaLean.Foundations.Computability DiagonaLean.GrammarMem.Reduction

variable {T : Type} [Primcodable T]

/-- **Whether the empty word belongs to the language of a type 0 grammar code is halting-hard**: a
reduction from the halting problem on canonical machines, proved computable. -/
def emptyWordFromHalt :
    HaltReduction fun g : { g : GrammarCode T // IsType0 g } => EmptyWordProblem g.1 :=
  ⟨fun x => ⟨canonGCode x, isType0_canonGCode x⟩,
    (Primrec.subtype_mk canonGCode_prim).to_comp, haltCanon_iff_emptyWord⟩

/-- **Membership for grammar codes is halting-hard**: `emptyWordFromHalt`, then asking for the
empty word, `g ↦ (g, [])`, computable by `prim_subtype_val`. -/
def fromHalt : HaltReduction (@DecisionProblem T) := by
  hard_reduce_from emptyWordFromHalt
    with (fun g : { g : GrammarCode T // IsType0 g } => (g.1, ([] : List T)))
    using (fun _ => Iff.rfl)

halt_results (@DecisionProblem T) from fromHalt

halt_results EmptyWord for (fun g : { g : GrammarCode T // IsType0 g } => EmptyWordProblem g.1)
  from emptyWordFromHalt

end DiagonaLean.GrammarMem
