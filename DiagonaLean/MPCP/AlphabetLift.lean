/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.Basic
import DiagonaLean.PCP.AlphabetLift

@[expose] public section

/-! # Transporting MPCP across alphabets

An MPCP instance is a list of pairs of words with a start pair, so
`Foundations.Codes.Correspondence` applies as for PCP: encoding every tile by a code, the start
tile included, preserves and reflects solvability (`decisionProblem_encode_iff`). An injective
renaming of letters is such a code (`mpcp_map_iff`).

MPCP is thus a functor on codes (`mpcpFunctor`), and the lifting of `Foundations.Codes.Functor`
applies: MPCP over an alphabet with decidable equality many-one reduces to MPCP over any alphabet
with two distinct letters (`mpcpAlphabetLift`). `Undecidable.lean` and `MachineLevel.lean` apply
it to the reduction from the halting problem.
-/

namespace DiagonaLean.MPCP

open PCP Foundations.Codes

variable {α β : Type}

/-- MPCP solvability as a correspondence of pairs after the start pair. -/
theorem decisionProblem_iff_isCorr (c : Tile α) (P : Stack α) :
    Solvable c P ↔ ∃ B, IsCorr ((c :: P).map Tile.toPair) c.toPair B := by
  constructor
  · rintro ⟨A, hA, h⟩
    exact ⟨_, isCorr_map_toPair_iff.2 ⟨A, rfl, hA, h⟩⟩
  · rintro ⟨B, h⟩
    obtain ⟨A, rfl, hA, h⟩ := isCorr_map_toPair_iff.1 h
    exact ⟨A, hA, h⟩

/-- **Changing the alphabet of MPCP.** Encoding the tiles, the start tile included, by a code
preserves and reflects solvability. -/
theorem decisionProblem_encode_iff {e : α → List β} (he : IsCode e) (c : Tile α) (P : Stack α) :
    Solvable (c.encode e) (P.encode e) ↔ Solvable c P := by
  have h : (c.encode e :: P.encode e).map Tile.toPair =
      ((c :: P).map Tile.toPair).map (encodePair e) := by
    simp [Stack.encode, Tile.toPair_encode]
  rw [decisionProblem_iff_isCorr, decisionProblem_iff_isCorr, h, Tile.toPair_encode]
  constructor
  · rintro ⟨B, h⟩
    obtain ⟨A, rfl, hA⟩ := IsCorr.of_encode he h
    exact ⟨A, hA⟩
  · rintro ⟨A, h⟩
    exact ⟨_, h.encode⟩

/-- Renaming the letters of the tiles injectively preserves and reflects MPCP solvability. -/
theorem mpcp_map_iff (g : α → β) (hg : Function.Injective g) (c : Tile α) (P : Stack α) :
    Solvable c P ↔ Solvable (Tile.map g c) (P.map (Tile.map g)) := by
  rw [← Tile.encode_unit_comp]
  exact (decisionProblem_encode_iff (isCode_unit.comp hg) c P).symm

namespace Reduction

open DiagonaLean.Synthetic.Definitions

/-- **MPCP as a functor on codes**: an instance is a start tile and a stack, a code encodes every
tile, and codes preserve and reflect solvability. -/
abbrev mpcpFunctor : CodeFunctor IsCode where
  Inst α := Tile α × Stack α
  map c x := (x.1.encode c, x.2.encode c)
  Prob x := DecisionProblem x
  map_unit _ := Prod.ext (Tile.encode_unit _) (Stack.encode_unit _)
  map_kcomp c₁ c₂ _ := Prod.ext (Tile.encode_kcomp c₁ c₂ _) (Stack.encode_kcomp c₁ c₂ _)
  natural hc x := decisionProblem_encode_iff hc x.1 x.2
  supp x := (x.1.top ++ x.1.bot) ++ x.2.letters
  map_congr _ h := Prod.ext (Tile.encode_congr fun a ha => h a (List.mem_append_left _ ha))
    (Stack.encode_congr fun a ha => h a (List.mem_append_right _ ha))

/-- MPCP over an alphabet `γ` with decidable equality many-one reduces to MPCP over any alphabet
with two distinct letters, by encoding every tile with the code of the letters of the instance
(`Foundations.Codes.CodeFunctor.lift`). -/
def mpcpAlphabetLift {γ : Type} [DecidableEq γ] (b0 b1 : α) (hne : b0 ≠ b1) :
    (@MPCP.DecisionProblem γ) ⪯_s
      (@MPCP.DecisionProblem α) :=
  mpcpFunctor.lift b0 b1 hne

end Reduction

end DiagonaLean.MPCP
