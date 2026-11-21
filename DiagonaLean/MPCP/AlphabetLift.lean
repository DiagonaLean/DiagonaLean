/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.Undecidable
import DiagonaLean.PCP.AlphabetLift
import DiagonaLean.Foundations.Codes.Unary
import DiagonaLean.Foundations.Computability.DerivePrimcodable

@[expose] public section

/-! # Transporting MPCP across alphabets

An MPCP instance is a list of pairs of words with a start pair, so
`Foundations.Codes.Correspondence` applies as for PCP: encoding every tile, the start tile
included, preserves and reflects solvability when `encode c` is injective on the words over the
letters of the instance (`decisionProblem_encode_iff`), in particular for a code.

`Alpha ℕ Sym2` is countable, so `Codes.bitCode` is a code into any alphabet with two distinct
letters, and `undecidableMPCP` transfers to every such alphabet
(`undecidableMPCPOf`), for instance to `Bool` (`undecidableMPCPBool`).
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

/-- MPCP over `Alpha ℕ Sym2` many-one reduces to MPCP over any alphabet with two distinct
letters, by encoding every tile with `bitCode`. -/
def mpcpAlphabetLift (b0 b1 : α) (hne : b0 ≠ b1) :
    (fun x : Tile (Alpha ℕ Foundations.Normalize.Sym2) ×
      Stack (Alpha ℕ Foundations.Normalize.Sym2) => DecisionProblem x.1 x.2) ⪯ₘ
      fun x : Tile α × Stack α => DecisionProblem x.1 x.2 :=
  ⟨fun x => (x.1.encode (bitCode b0 b1), x.2.encode (bitCode b0 b1)),
    fun x => (decisionProblem_encode_iff_of_isCode (isSync_bitCode hne).isCode x.1 x.2).symm⟩

/-- **MPCP is `Undecidable` over any alphabet `α` with two distinct letters `b0`, `b1`.** -/
def undecidableMPCPOf (b0 b1 : α) (hne : b0 ≠ b1) :
    Undecidable fun x : Tile α × Stack α => DecisionProblem x.1 x.2 :=
  undecidabilityFromReducibility undecidableMPCP (mpcpAlphabetLift b0 b1 hne)

/-- **MPCP over `Bool` is `Undecidable`.** -/
def undecidableMPCPBool : Undecidable MPCProblem :=
  undecidableMPCPOf false true Bool.false_ne_true

end Reduction

end DiagonaLean.MPCP
