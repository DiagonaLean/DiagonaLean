/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.GrammarMem.Basic
import DiagonaLean.SemiThue.MachineLevel

@[expose] public section

/-! # Membership for unrestricted grammars, at machine level

A fresh start symbol `0`, with the rule `[0] → u`, and the symbols of `Alpha ℕ Sym2` numbered from
`1` (`gSym`), turn a string rewriting system `R` and a start string `u` into a grammar code
(`ofSRS`). When the left sides of `R` are non-empty, its language contains the empty word iff `u`
rewrites to the empty string (`emptyWord_ofSRS_iff`, from `SRS.derives_start` and
`Codes.derives_mapRules_iff`), and it is of type 0 (`isType0_ofSRS`).

## Main statements

* `ofSRS`, `emptyWord_ofSRS_iff`, `isType0_ofSRS`, and the `Primcodable` instance of type 0 grammar
  codes: used in `Hardness.lean` for the halting reductions `GrammarMem.emptyWordFromHalt` and
  `GrammarMem.fromHalt`, from which the negative results there
  (`GrammarMem.not_computablePred`, `GrammarMem.EmptyWord.not_machineDecidable`, …) follow.
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

derive_primrec gSym [Primcodable T]

derive_primrec ofSRS [Primcodable T]

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

variable [Primcodable T]

/-- `IsType0` is a primitive recursive predicate. -/
@[fun_prop] theorem isType0_prim : PrimrecPred (IsType0 (T := T)) := by
  unfold IsType0 isType0
  fun_prop

/-- Type 0 grammar codes, with the encoding of a subtype. -/
instance : Primcodable { g : GrammarCode T // IsType0 g } := Primcodable.subtype isType0_prim

end DiagonaLean.GrammarMem.MachineLevel
