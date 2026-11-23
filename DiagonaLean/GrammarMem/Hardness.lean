/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.GrammarMem.MachineLevel
import DiagonaLean.SemiThue.Hardness

@[expose] public section

/-! # Membership for unrestricted grammars is halting-hard

`SemiThue.MachineLevel.canonToEmpty` sends a canonical machine and an input to a rewriting system
with non-empty left sides and a start string, which rewrites to the empty string iff the machine
halts (`SemiThue.MachineLevel.haltCanon_iff_toEmpty`). The grammar code `ofSRS` of this instance is
of type 0 (`isType0_ofSRS`), and its language contains the empty word iff the start string rewrites
to the empty string (`emptyWord_ofSRS_iff`). So `canonGCode` is a reduction from `HaltCanon`,
proved computable.

## Main statements

* `GrammarMem.emptyWordFromHalt`: whether the empty word belongs to the language of a type 0
  grammar code is halting-hard.
* `GrammarMem.fromHalt`, `GrammarMem.haltHard`: membership for grammar codes is halting-hard.
-/

namespace DiagonaLean.GrammarMem.MachineLevel

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.SemiThue DiagonaLean.SemiThue.MachineLevel

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

end DiagonaLean.GrammarMem.MachineLevel

namespace DiagonaLean.GrammarMem

open DiagonaLean.Foundations.Computability DiagonaLean.GrammarMem.MachineLevel

variable {T : Type} [Primcodable T]

/-- **Whether the empty word belongs to the language of a type 0 grammar code is halting-hard**: a
reduction from the halting problem on canonical machines, proved computable. -/
def emptyWordFromHalt :
    HaltReduction fun g : { g : GrammarCode T // IsType0 g } => EmptyWordProblem g.1 :=
  ⟨fun x => ⟨canonGCode x, isType0_canonGCode x⟩,
    (Primrec.subtype_mk canonGCode_prim).to_comp, haltCanon_iff_emptyWord⟩

/-- **Membership for grammar codes is halting-hard**: `emptyWordFromHalt`, then
`synthFromEmptyWord`, proved computable (`prim_subtype_val`). -/
def fromHalt : HaltReduction (@DecisionProblem T) := by
  reduce_from emptyWordFromHalt via GrammarMem.synthFromEmptyWord

theorem haltHard : HaltHard (@DecisionProblem T) :=
  ⟨fromHalt⟩

end DiagonaLean.GrammarMem
