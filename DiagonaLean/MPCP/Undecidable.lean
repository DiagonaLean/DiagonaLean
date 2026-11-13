/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.PCP.Reductions.Halt_to_PCP

/-! # Undecidability of MPCP

MPCP is undecidable over the fixed alphabet `Alpha ℕ Sym2` (`mpcp_undecidable`). `halt_iff_mpcp`
assumes `NoBlankWrites` and `NoLeftBoundary`, so `haltToMpcpNorm` first normalizes the machine and
its input with `Foundations.Normalize`, then renames states to their codes. The composition lives
here because `Foundations.Normalize` imports `Halt_to_MPCP`.
-/

namespace DiagonaLean.MPCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.PCP
  DiagonaLean.PCP.Reduction DiagonaLean.Synthetic.Notation

/-- Renaming symbols injectively preserves and reflects MPCP solvability. -/
theorem decisionProblem_map_iff {α β : Type} (g : α → β) (hg : Function.Injective g)
    (c : Tile α) (P : Stack α) :
    MPCP.DecisionProblem c P ↔ MPCP.DecisionProblem (Tile.map g c) (P.map (Tile.map g)) := by
  constructor
  · rintro ⟨A, hA, heq⟩
    refine ⟨A.map (Tile.map g), fun t ht => ?_, ?_⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ht
      exact List.mem_map_of_mem (f := Tile.map g) (l := c :: P) (hA a ha)
    · simp only [Tile.map, τ1_map, τ2_map, ← List.map_append, heq]
  · rintro ⟨A, hA, heq⟩
    obtain ⟨ls, rfl, hls⟩ := exists_stack_of_mem_mapped A g (c :: P)
      (fun t ht => (List.mem_map (f := Tile.map g) (l := c :: P)).1 (hA t ht))
    refine ⟨ls, hls, ?_⟩
    simp only [Tile.map, τ1_map, τ2_map, ← List.map_append] at heq
    exact List.map_injective_iff.2 hg heq

/-- The reduction function witnessing `HaltProblem ⪯ₘ MPCP`: normalizes the machine and input to
satisfy `NoBlankWrites` and `NoLeftBoundary`, builds the MPCP instance of `halt_iff_mpcp`, and
renames states by `tm.stateEncodable` composed with the `Encodable` instance for the normalizer's
control states. -/
def haltToMpcpNorm (p : EncodableTM Bool × List Bool) :
    Tile (Alpha ℕ Foundations.Normalize.Sym2) × Stack (Alpha ℕ Foundations.Normalize.Sym2) :=
  letI := p.1.stateEncodable
  letI hEnc : Encodable (Foundations.Normalize.normTM p.1.toSingleTapeTM).State :=
    (inferInstance : Encodable (p.1.State × Foundations.Normalize.Ctrl))
  let tm : EncodableTM _ := ⟨Foundations.Normalize.normTM p.1.toSingleTapeTM, hEnc⟩
  (Tile.map (Alpha.map Encodable.encode)
      (startTile tm.toSingleTapeTM (Foundations.Normalize.encInput p.2)),
    (haltTiles tm).map (Tile.map (Alpha.map Encodable.encode)))

/-- `haltToMpcpNorm` witnesses that the halting problem many-one reduces to MPCP over the fixed
alphabet `Alpha ℕ Sym2`. -/
theorem halt_reducesto_mpcp_spec :
    HaltProblem ⪯ₘ[haltToMpcpNorm]
      fun x : Tile (Alpha ℕ Foundations.Normalize.Sym2) ×
        Stack (Alpha ℕ Foundations.Normalize.Sym2) => MPCP.DecisionProblem x.1 x.2 := by
  rintro ⟨tm, w⟩
  show Halts tm.toSingleTapeTM w ↔ _
  let _ := tm.stateEncodable
  let hEnc : Encodable (Foundations.Normalize.normTM tm.toSingleTapeTM).State :=
    (inferInstance : Encodable (tm.State × Foundations.Normalize.Ctrl))
  let normTMEnc : EncodableTM _ := ⟨Foundations.Normalize.normTM tm.toSingleTapeTM, hEnc⟩
  rw [Foundations.Normalize.halts_normTM_iff tm.toSingleTapeTM w,
    halt_iff_mpcp normTMEnc (Foundations.Normalize.normTM_noBlankWrites tm.toSingleTapeTM)
      (Foundations.Normalize.encInput w)
      (Foundations.Normalize.normTM_noLeftBoundary tm.toSingleTapeTM w)]
  exact decisionProblem_map_iff _ (Alpha.map_injective Encodable.encode_injective) _ _

/-- MPCP is undecidable over the fixed alphabet `Alpha ℕ Sym2`. -/
theorem mpcp_undecidable :
    Undecidable fun x : Tile (Alpha ℕ Foundations.Normalize.Sym2) ×
      Stack (Alpha ℕ Foundations.Normalize.Sym2) => MPCP.DecisionProblem x.1 x.2 :=
  ⟨⟨haltToMpcpNorm, halt_reducesto_mpcp_spec⟩⟩

end DiagonaLean.MPCP.Reduction
