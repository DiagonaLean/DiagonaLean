/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.GrammarMem.Basic
import DiagonaLean.SemiThue.MachineLevel

@[expose] public section

/-! # No machine decides membership for unrestricted grammars

`SemiThue.MachineLevel.toEmptyCode` sends a machine code to a string rewriting system and a start
string such that the machine halts on its own code iff the start string rewrites to the empty
string. A fresh start symbol `0`, with the rule `[0] → start string`, and the other symbols numbered
from `1` (`gSym`), turn this into a grammar code (`gCode`) whose language contains the empty word
iff the start string rewrites to the empty string (`emptyWord_gCode_iff`, from `SRS.derives_start`
and `Codes.derives_mapRules_iff`). The grammar codes are of type 0 (`isType0_gCode`) and primitive
recursive in the machine code (`gCode_prim`).

## Main statements

* `not_computablePred_emptyWord_type0`, `not_machineDecidable_emptyWord_type0`: whether the empty
  word belongs to the language of a type 0 grammar code is not computable.
* `not_computablePred_grammarMem`, `not_machineDecidable_grammarMem`: membership for grammar codes
  is not computable.
-/

namespace DiagonaLean.GrammarMem.MachineLevel

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Foundations.Computability DiagonaLean.Foundations.Grammar
  DiagonaLean.MPCP.MachineLevel
  DiagonaLean.SemiThue DiagonaLean.SemiThue.Reduction DiagonaLean.SemiThue.MachineLevel
  DiagonaLean.Synthetic.Definitions

variable {T : Type}

/-- The symbols of `Alpha ℕ Sym2` as the nonterminals `1, 2, …`; `0` is the start symbol. -/
def gSym (a : Alpha ℕ Normalize.Sym2) : T ⊕ ℕ := .inr (Encodable.encode a + 1)

/-- `gSym` is injective. -/
theorem gSym_injective : Function.Injective (gSym (T := T)) := fun a b h => by
  simp only [gSym, Sum.inr.injEq, Nat.add_right_cancel_iff] at h
  exact Encodable.encode_injective h

/-- No symbol is sent to the start symbol `0`. -/
theorem gSym_ne_start (a : Alpha ℕ Normalize.Sym2) : gSym (T := T) a ≠ .inr 0 := by
  simp [gSym]

/-- The grammar code of a rewriting system `R` and a start string `u`: the start rule `[0] → u`
and the rules of `R`, over the nonterminals `gSym`. -/
def ofSRS (R : SRS (Alpha ℕ Normalize.Sym2))
    (u : List (Alpha ℕ Normalize.Sym2)) :
    GrammarCode T :=
  (0, ([.inr 0], u.map gSym) :: R.map fun lr => (lr.1.map gSym, lr.2.map gSym))

/-- **The grammar code of a machine code** `w`. -/
def gCode (w : List Bool) : GrammarCode T := ofSRS (toEmptyCode w).1 (toEmptyCode w).2

derive_primrec gSym [Primcodable T]

derive_primrec ofSRS [Primcodable T]

derive_primrec gCode [Primcodable T]

/-- **The empty word is in the language of `ofSRS R u` iff `u` rewrites to the empty string**, when
every rule of `R` has a non-empty left side. -/
theorem emptyWord_ofSRS_iff (R : SRS (Alpha ℕ Normalize.Sym2))
    (u : List (Alpha ℕ Normalize.Sym2)) (hne : ∀ lr ∈ R, lr.1 ≠ []) :
    EmptyWordProblem (ofSRS (T := T) R u) ↔ R.Derives u [] := by
  show SRS.Derives (([(Sum.inr 0 : T ⊕ ℕ)], u.map gSym) ::
      R.map fun lr => (lr.1.map gSym, lr.2.map gSym)) [Sum.inr 0]
      (([] : List T).map Sum.inl) ↔ _
  rw [List.map_nil, SRS.derives_start (v := [])]
  · exact Foundations.Codes.derives_mapRules_iff gSym_injective hne _ []
  · intro lr hlr
    obtain ⟨lr, -, rfl⟩ := List.mem_map.1 hlr
    simp only [List.mem_map, not_exists, not_and]
    exact ⟨fun a _ => gSym_ne_start a, fun a _ => gSym_ne_start a⟩
  · intro lr hlr
    obtain ⟨lr₀, hlr₀, rfl⟩ := List.mem_map.1 hlr
    simpa using hne lr₀ hlr₀
  · simp only [List.mem_map, not_exists, not_and]
    exact fun a _ => gSym_ne_start a
  · simp

/-- **The empty word is in the language of the grammar code of `w` iff the start string of `w`
rewrites to the empty string.** -/
theorem emptyWord_gCode_iff (w : List Bool) :
    EmptyWordProblem (gCode (T := T) w) ↔ ToEmptyProblem (toEmptyCode w) :=
  emptyWord_ofSRS_iff _ _ (codeRules_lhs_ne (rowsC w))

/-- The grammar code of a rewriting system whose left sides are non-empty is of type 0. -/
theorem isType0_ofSRS (R : SRS (Alpha ℕ Normalize.Sym2)) (u : List (Alpha ℕ Normalize.Sym2))
    (hne : ∀ lr ∈ R, lr.1 ≠ []) : IsType0 (ofSRS (T := T) R u) := by
  rw [isType0_iff, ofSRS]
  intro lr hlr
  rcases List.mem_cons.1 hlr with rfl | hlr
  · exact ⟨0, List.mem_singleton.2 rfl⟩
  · obtain ⟨lr₀, hlr₀, rfl⟩ := List.mem_map.1 hlr
    obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (hne lr₀ hlr₀)
    exact ⟨Encodable.encode a + 1, by simp [hl, gSym]⟩

/-- The grammar code of a machine code is of type 0. -/
theorem isType0_gCode (w : List Bool) : IsType0 (gCode (T := T) w) :=
  isType0_ofSRS _ _ (codeRules_lhs_ne (rowsC w))

/-- **A machine halts on its own code iff the empty word is in the language of the grammar code of
its code.** -/
theorem selfHalt_iff_emptyWord (M : EncodableTM Bool) :
    Halts M.toSingleTapeTM (encodeBoolTM M) ↔ EmptyWordProblem (gCode (T := T) (encodeBoolTM M)) :=
  (selfHalt_iff_toEmpty M).trans (emptyWord_gCode_iff _).symm

variable [Primcodable T]

/-- `IsType0` is a primitive recursive predicate. -/
@[fun_prop] theorem isType0_prim : PrimrecPred (IsType0 (T := T)) := by
  unfold IsType0 isType0
  fun_prop

/-- Type 0 grammar codes, with the encoding of a subtype. -/
instance : Primcodable { g : GrammarCode T // IsType0 g } := Primcodable.subtype isType0_prim

/-- **Whether the empty word belongs to the language of a type 0 grammar code is not a computable
predicate.** -/
theorem not_computablePred_emptyWord_type0 :
    ¬ ComputablePred fun g : { g : GrammarCode T // IsType0 g } => EmptyWordProblem g.1 :=
  not_computablePred_of_selfHalt (code := fun w => ⟨gCode w, isType0_gCode w⟩)
    (Primrec.subtype_mk gCode_prim).to_comp selfHalt_iff_emptyWord

/-- **No Turing machine decides whether the empty word belongs to the language of a type 0 grammar
code**, under any computable encoding. -/
theorem not_machineDecidable_emptyWord_type0
    {enc : { g : GrammarCode T // IsType0 g } → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc fun g => EmptyWordProblem g.1 :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_emptyWord_type0

/-- Membership of the empty word in a type 0 grammar is membership in a grammar. -/
def _root_.DiagonaLean.GrammarMem.synthFromEmptyWord :
    (fun g : { g : GrammarCode T // IsType0 g } => EmptyWordProblem g.1) ⪯_s
      @DecisionProblem T :=
  ⟨fun g => (g.1, []), fun _ => Iff.rfl⟩

/-- The former name of `GrammarMem.synthFromEmptyWord`. -/
@[deprecated DiagonaLean.GrammarMem.synthFromEmptyWord (since := "2026-11-23")]
abbrev emptyWordReducesGrammarMem := @DiagonaLean.GrammarMem.synthFromEmptyWord

/-- **Membership for grammar codes is not a computable predicate.** -/
theorem not_computablePred_grammarMem : ¬ ComputablePred (@DecisionProblem T) :=
  not_computablePred_of_reduces GrammarMem.synthFromEmptyWord
    ((Primrec.subtype_val.pair (Primrec.const [])).to_comp) not_computablePred_emptyWord_type0

/-- **No Turing machine decides membership for grammar codes**, under any computable encoding. -/
theorem not_machineDecidable_grammarMem {enc : GrammarCode T × List T → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc DecisionProblem :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_grammarMem

end DiagonaLean.GrammarMem.MachineLevel
