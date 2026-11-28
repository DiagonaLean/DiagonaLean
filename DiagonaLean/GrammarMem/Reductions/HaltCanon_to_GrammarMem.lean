/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.GrammarMem.Reductions.SemiThue_to_GrammarMem
import DiagonaLean.SemiThue.Reductions.HaltCanon_to_SemiThue

@[expose] public section

/-! # From the halting problem on canonical machines to the empty word in type 0 grammars

`SemiThue.Reduction.canonToEmpty` sends a canonical machine and an input to a rewriting system
with non-empty left sides and a start string, which rewrites to the empty string iff the machine
halts (`SemiThue.Reduction.haltCanon_iff_toEmpty`). The grammar code `ofSRS` of this instance is
of type 0 (`isType0_ofSRS`), and its language contains the empty word iff the start string rewrites
to the empty string (`emptyWord_ofSRS_iff`). So `canonGCode` reduces `HaltCanon` to the empty word
problem, primitive recursively.

## Main statements

* `canonGCode`, `isType0_canonGCode`, `canonGCode_prim`, `haltCanon_iff_emptyWord`: the reduction.
  The halting reductions built from it (`GrammarMem.emptyWordFromHalt`, `GrammarMem.fromHalt`) are
  in `Undecidable.lean`.

## References

* N. Chomsky, *On certain formal properties of grammars* (1959)
-/

namespace DiagonaLean.GrammarMem.Reduction

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.SemiThue DiagonaLean.SemiThue.Reduction

variable {T : Type}

/-- The grammar code of a canonical machine on an input. -/
def canonGCode (x : CanonTM × List Bool) : GrammarCode T :=
  ofSRS (canonToEmpty x).1 (canonToEmpty x).2

/-- The grammar code of a canonical machine on an input is of type 0. -/
theorem isType0_canonGCode (x : CanonTM × List Bool) : IsType0 (canonGCode (T := T) x) :=
  isType0_ofSRS _ _ (codeRules_lhs_ne _)

theorem canonGCode_prim [Primcodable T] : Primrec (canonGCode (T := T)) := by
  have := canonToEmpty_prim
  unfold canonGCode
  fun_prop

/-- **A canonical machine halts on an input iff the empty word is in the language of its grammar
code.** -/
theorem haltCanon_iff_emptyWord (x : CanonTM × List Bool) :
    HaltCanon x ↔ EmptyWordProblem (canonGCode (T := T) x) :=
  (haltCanon_iff_toEmpty x).trans (emptyWord_ofSRS_iff _ _ (codeRules_lhs_ne _)).symm

end DiagonaLean.GrammarMem.Reduction
