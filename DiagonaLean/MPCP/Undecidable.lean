/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.PCP.Reductions.Halt_to_PCP

@[expose] public section

/-! # Undecidability of MPCP

MPCP is undecidable over the fixed alphabet `Alpha ℕ Sym2` (`undecidableMPCP`). `halt_iff_mpcp`
assumes `NoBlankWrites` and `NoLeftBoundary`, so `haltToMpcpNorm` first normalizes the machine and
its input with `MPCP.Normalize`, then renames states to their codes. The composition lives
here because `MPCP.Normalize` imports `Halt_to_MPCP`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.MPCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.PCP
  DiagonaLean.PCP.Reduction DiagonaLean.Synthetic.Notation

/-- Renaming symbols injectively preserves and reflects MPCP solvability. -/
theorem mpcp_map_iff {α β : Type} (g : α → β) (hg : Function.Injective g)
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

/-- **The reduction.** The function witnessing `HaltProblem ⪯ₘ MPCP`: it normalizes the machine
and input to satisfy `NoBlankWrites` and `NoLeftBoundary`, builds the MPCP instance of
`halt_iff_mpcp`, and renames states by `tm.stateEncodable` composed with the `Encodable` instance
for the normalizer's control states. -/
def haltToMpcpNorm (p : EncodableTM Bool × List Bool) :
    Tile (Alpha ℕ MPCP.Normalize.Sym2) × Stack (Alpha ℕ MPCP.Normalize.Sym2) :=
  let tm := MPCP.Normalize.normEnc p.1
  letI := tm.stateEncodable
  (Tile.map (Alpha.map Encodable.encode)
      (startTile tm.toSingleTapeTM (MPCP.Normalize.encInput p.2)),
    (haltTiles tm).map (Tile.map (Alpha.map Encodable.encode)))

/-- `haltToMpcpNorm` witnesses that the halting problem many-one reduces to MPCP over the fixed
alphabet `Alpha ℕ Sym2`. -/
theorem halt_reducesto_mpcp_spec :
    HaltProblem ⪯ₘ[haltToMpcpNorm]
      fun x : Tile (Alpha ℕ MPCP.Normalize.Sym2) ×
        Stack (Alpha ℕ MPCP.Normalize.Sym2) => MPCP.DecisionProblem x.1 x.2 := by
  rintro ⟨tm, w⟩
  show Halts tm.toSingleTapeTM w ↔ _
  let normTMEnc := MPCP.Normalize.normEnc tm
  let _ := normTMEnc.stateEncodable
  rw [MPCP.Normalize.halts_normTM_iff tm.toSingleTapeTM w,
    halt_iff_mpcp normTMEnc (MPCP.Normalize.normTM_noBlankWrites tm.toSingleTapeTM)
      (MPCP.Normalize.encInput w)
      (MPCP.Normalize.normTM_noLeftBoundary tm.toSingleTapeTM w)]
  exact mpcp_map_iff _ (Alpha.map_injective Encodable.encode_injective) _ _

/-- The halting problem many-one reduces to MPCP over the fixed alphabet `Alpha ℕ Sym2`, through
`haltToMpcpNorm`. -/
def haltReducesMPCP :
    HaltProblem ⪯ₘ fun x : Tile (Alpha ℕ MPCP.Normalize.Sym2) ×
      Stack (Alpha ℕ MPCP.Normalize.Sym2) => MPCP.DecisionProblem x.1 x.2 :=
  ⟨haltToMpcpNorm, halt_reducesto_mpcp_spec⟩

/-- **MPCP is `Undecidable` over the fixed alphabet `Alpha ℕ Sym2`.** -/
def undecidableMPCP :
    Undecidable fun x : Tile (Alpha ℕ MPCP.Normalize.Sym2) ×
      Stack (Alpha ℕ MPCP.Normalize.Sym2) => MPCP.DecisionProblem x.1 x.2 :=
  haltReducesMPCP

end DiagonaLean.MPCP.Reduction
