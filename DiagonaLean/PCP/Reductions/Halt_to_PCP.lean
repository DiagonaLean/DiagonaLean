/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga
-/

import DiagonaLean.PCP.Reductions.MPCP_to_PCP
import DiagonaLean.MPCP.Reductions.Halt_to_MPCP
import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.Foundations.Computability.Normalize.Normalize
import DiagonaLean.PCP.AlphabetLift

@[expose] public section

/-! # Halt ⪯ₘ PCP

The composition `Halt ⪯ₘ MPCP ⪯ₘ PCP`, giving a direct equivalence between halting of a TM
`tm` on input `w` and solvability of the PCP instance `mpcpToPcp (startTile tm w) (haltTiles tm)`.

`MPCP_to_PCP` supplies the intermediate step; `Foundations.Computability.Normalize` removes the
`NoBlankWrites` and `NoLeftBoundary` side conditions by simulating an arbitrary TM by a
normalised one. This shifts the tape alphabet to `Bool × Bool`, landing the reduction in
`Stack (Ext (Alpha ℕ (Bool × Bool)))`. Finally, `AlphabetLift` transports the resulting
instance back to the target alphabet via distinct elements `Ext.hash ≠ Ext.rupee`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.PCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.MPCP.Reduction DiagonaLean.Halt
  DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Computability.Normalize
open DiagonaLean.PCP.AlphabetLift DiagonaLean.Synthetic.Notation

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Under `NoBlankWrites` and `NoLeftBoundary`, `tm` halts on `w` iff the PCP instance
`mpcpToPcp (startTile tm w) (haltTiles tm)` is solvable. -/
theorem halt_iff_pcp (tm : EncodableTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm.toSingleTapeTM) (h_nlb : NoLeftBoundary tm.toSingleTapeTM w)
    [Encodable Symbol] :
    Halts tm.toSingleTapeTM w ↔
    PCP.DecisionProblem (mpcpToPcp (startTile tm.toSingleTapeTM w) (haltTiles tm)) :=
  (halt_iff_mpcp tm h_nbw w h_nlb).trans (mpcp_iff_pcp _ _)

/-- Map symbol types in the PCP boundary extension type `Ext`. -/
def Ext.map {α β : Type} (g : α → β) : Ext α → Ext β
  | .sym a  => .sym (g a)
  | .hash   => .hash
  | .rupee  => .rupee

/-- `Ext.map` preserves injectivity of the underlying map. -/
theorem Ext.map_injective {α β : Type} {g : α → β} (hg : Function.Injective g) :
    Function.Injective (Ext.map g) := by
  intro x y hxy
  cases x <;> cases y <;> simp only [Ext.map, reduceCtorEq, Ext.sym.injEq] at hxy ⊢
  exact hg hxy

/-- Map TM halting instance to a PCP stack via integer state encoding. -/
def pcpRed (tm : EncodableTM Symbol) (w : List Symbol)
    [Encodable Symbol] : Stack (Ext (Alpha ℕ Symbol)) :=
  letI := tm.stateEncodable
  (mpcpToPcp (startTile tm.toSingleTapeTM w) (haltTiles tm)).map
    (Tile.map (Ext.map (Alpha.map Encodable.encode)))

/-- State encoding preserves and reflects PCP solvability. -/
theorem pcpRed_iff (tm : EncodableTM Symbol) (w : List Symbol)
    [Encodable Symbol] :
    PCP.DecisionProblem (mpcpToPcp (startTile tm.toSingleTapeTM w) (haltTiles tm)) ↔
    PCP.DecisionProblem (pcpRed tm w) := by
  let _ := tm.stateEncodable
  exact pcp_map_iff (Ext.map (Alpha.map Encodable.encode))
    (Ext.map_injective (Alpha.map_injective Encodable.encode_injective))
    (mpcpToPcp (startTile tm.toSingleTapeTM w) (haltTiles tm))

variable (α : Type*) [Fintype α]

/-- **The reduction.** The function witnessing `HaltProblem ⪯ₘ PCP.DecisionProblem`: it
normalizes the machine and input to satisfy `NoBlankWrites`/`NoLeftBoundary`, encodes states via
`pcpRed` (using `tm.stateEncodable`, composed with the hand-written `Encodable` instance for the
normalizer's `Ctrl` control states, to stay computable), and lifts the result to the fixed
alphabet `Ext (Alpha ℕ Bool)`. -/
def haltToPcp (p : EncodableTM Bool × List Bool) : Stack (Ext (Alpha ℕ Bool)) :=
  AlphabetLift.liftInstance Ext.hash Ext.rupee (pcpRed (normEnc p.1) (encInput p.2))

/-- `haltToPcp` witnesses that the halting problem many-one reduces to PCP over the fixed
alphabet `Ext (Alpha ℕ Bool)`. Combines TM normalization, MPCP reduction, and alphabet
lifting. -/
theorem halt_reducesto_pcp_spec :
    HaltProblem ⪯ₘ[haltToPcp] (@DecisionProblem (Ext (Alpha ℕ Bool))) := by
  rintro ⟨tm, w⟩
  show Halts tm.toSingleTapeTM w ↔ _
  let normTMEnc := normEnc tm
  rw [halts_normTM_iff tm.toSingleTapeTM w,
    halt_iff_pcp normTMEnc (encInput w)
      (normTM_noBlankWrites tm.toSingleTapeTM)
      (normTM_noLeftBoundary tm.toSingleTapeTM w),
    pcpRed_iff normTMEnc (encInput w)]
  exact AlphabetLift.decisionProblem_lifts Ext.hash Ext.rupee
    (pcpRed normTMEnc (encInput w))
    (by decide)

/-- The halting problem many-one reduces to PCP over the fixed alphabet `Ext (Alpha ℕ Bool)`. -/
def haltReducesPCP :
    HaltProblem ⪯ₘ (@DecisionProblem (Ext (Alpha ℕ Bool))) :=
  ⟨haltToPcp, halt_reducesto_pcp_spec⟩

end DiagonaLean.PCP.Reduction
