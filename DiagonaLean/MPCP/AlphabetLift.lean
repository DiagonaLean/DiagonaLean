/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.Undecidable
import DiagonaLean.PCP.AlphabetLift
import DiagonaLean.Foundations.Codes.Functor
import DiagonaLean.Foundations.Computability.DerivePrimcodable

@[expose] public section

/-! # Transporting MPCP across alphabets

An MPCP instance is a list of pairs of words with a start pair, so
`Foundations.Codes.Correspondence` applies as for PCP: encoding every tile, the start tile
included, preserves and reflects solvability when `encode c` is injective on the words over the
letters of the instance (`decisionProblem_encode_iff`), in particular for a code.

MPCP is thus a functor on codes (`mpcpFunctor`), and the lifting of `Foundations.Codes.Functor`
applies: `Alpha ℕ Sym2` has decidable equality, so `undecidableMPCP` transfers to every alphabet
with two distinct letters (`undecidableMPCPOf`), for instance to `Bool` (`undecidableMPCPBool`). The
machine-level lifting is in `MachineLevel.lean`.
-/

derive_primcodable DiagonaLean.MPCP.Reduction.Alpha

namespace DiagonaLean.MPCP

open PCP Foundations.Codes

variable {α β : Type}

/-- MPCP solvability as a correspondence of pairs after the start pair. -/
theorem decisionProblem_iff_isCorr (c : Tile α) (P : Stack α) :
    DecisionProblem c P ↔ ∃ B, IsCorr ((c :: P).map Tile.toPair) c.toPair B := by
  constructor
  · rintro ⟨A, hA, h⟩
    exact ⟨_, isCorr_map_toPair_iff.2 ⟨A, rfl, hA, h⟩⟩
  · rintro ⟨B, h⟩
    obtain ⟨A, rfl, hA, h⟩ := isCorr_map_toPair_iff.1 h
    exact ⟨A, hA, h⟩

/-- **Changing the alphabet of MPCP.** Encoding the tiles preserves and reflects solvability when
`encode e` is injective on the words over the letters of the instance. -/
theorem decisionProblem_encode_iff {e : α → List β} {c : Tile α} {P : Stack α}
    (he : InjOnLetters e (c.toPair :: (c :: P).map Tile.toPair)) :
    DecisionProblem (c.encode e) (P.encode e) ↔ DecisionProblem c P := by
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

/-- MPCP solvability is preserved and reflected by a code. -/
theorem decisionProblem_encode_iff_of_isCode {e : α → List β} (he : IsCode e) (c : Tile α)
    (P : Stack α) : DecisionProblem (c.encode e) (P.encode e) ↔ DecisionProblem c P :=
  decisionProblem_encode_iff (he.injOnLetters _)

namespace Reduction

open DiagonaLean.Synthetic.Notation

/-- **MPCP as a functor on codes**: an instance is a start tile and a stack, a code encodes every
tile, and codes preserve and reflect solvability. -/
abbrev mpcpFunctor : CodeFunctor IsCode where
  Inst α := Tile α × Stack α
  map c x := (x.1.encode c, x.2.encode c)
  Prob x := DecisionProblem x.1 x.2
  map_unit x := Prod.ext (Tile.encode_unit _) (Stack.encode_unit _)
  map_kcomp c₁ c₂ x := Prod.ext (Tile.encode_kcomp c₁ c₂ _) (Stack.encode_kcomp c₁ c₂ _)
  natural hc x := decisionProblem_encode_iff_of_isCode hc x.1 x.2
  supp x := (x.1.top ++ x.1.bot) ++ x.2.letters
  map_congr x h := Prod.ext (Tile.encode_congr fun a ha => h a (List.mem_append_left _ ha))
    (Stack.encode_congr fun a ha => h a (List.mem_append_right _ ha))

/-- MPCP over `Alpha ℕ Sym2` many-one reduces to MPCP over any alphabet with two distinct
letters, by encoding every tile with the code of the letters of the instance
(`Foundations.Codes.CodeFunctor.lift`). -/
def mpcpAlphabetLift (b0 b1 : α) (hne : b0 ≠ b1) :
    (fun x : Tile (Alpha ℕ Foundations.Normalize.Sym2) ×
      Stack (Alpha ℕ Foundations.Normalize.Sym2) => DecisionProblem x.1 x.2) ⪯ₘ
      fun x : Tile α × Stack α => DecisionProblem x.1 x.2 :=
  mpcpFunctor.lift b0 b1 hne

/-- **MPCP is `Undecidable` over any alphabet `α` with two distinct letters `b0`, `b1`.** -/
def undecidableMPCPOf (b0 b1 : α) (hne : b0 ≠ b1) :
    Undecidable fun x : Tile α × Stack α => DecisionProblem x.1 x.2 :=
  mpcpFunctor.undecidableOf undecidableMPCP b0 b1 hne

/-- **MPCP over `Bool` is `Undecidable`.** -/
def undecidableMPCPBool : Undecidable MPCProblem :=
  undecidableMPCPOf false true Bool.false_ne_true

end Reduction

end DiagonaLean.MPCP
