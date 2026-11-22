/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.SemiThue.Basic
import DiagonaLean.SemiThue.Reductions.Halt_to_SemiThue

@[expose] public section

/-! # Undecidability of the word problem for string rewriting systems

`haltToSemiThue` normalises the machine and its input (`Foundations.Normalize`), takes the
rewriting system of `Reductions/Halt_to_SemiThue.lean`, and renames its states to their codes,
over the fixed alphabet `Alpha ℕ Sym2`. `halt_iff_derives` and `SRS.derives_map_iff` make it a
reduction from `HaltProblem` (`haltReducesSemiThue`), so the word problem is `Undecidable`
(`undecidableSemiThue`).
The machine-level statements are in `MachineLevel.lean`.
-/

namespace DiagonaLean.SemiThue.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Grammar
  DiagonaLean.Synthetic.Notation

/-- **The reduction.** The rewriting system of the normalised machine and its start string, with
states renamed to their codes, and the empty string as target. -/
def haltToSemiThue (p : EncodableTM Bool × List Bool) :
    SRS (Alpha ℕ Foundations.Normalize.Sym2) × List (Alpha ℕ Foundations.Normalize.Sym2) ×
      List (Alpha ℕ Foundations.Normalize.Sym2) :=
  letI := (Foundations.Normalize.normEnc p.1).stateEncodable
  ((tmRules (Foundations.Normalize.normEnc p.1)).mapRules (Alpha.map Encodable.encode),
    (block (Foundations.Normalize.normEnc p.1).toSingleTapeTM
      (initCfg (Foundations.Normalize.normEnc p.1).toSingleTapeTM
        (Foundations.Normalize.encInput p.2))).map
        (Alpha.map Encodable.encode), [])

theorem halt_reducesto_semiThue_spec : HaltProblem ⪯ₘ[haltToSemiThue] DecisionProblem := by
  rintro ⟨M, w⟩
  show Halts M.toSingleTapeTM w ↔ _
  let := (Foundations.Normalize.normEnc M).stateEncodable
  rw [Foundations.Normalize.halts_normTM_iff,
    halt_iff_derives (tm := Foundations.Normalize.normEnc M)
      (Foundations.Normalize.normTM_noBlankWrites _) _
      (Foundations.Normalize.normTM_noLeftBoundary _ _),
    ← SRS.derives_map_iff (f := Alpha.map Encodable.encode)
      (Alpha.map_injective Encodable.encode_injective)]
  rfl

/-- The halting problem many-one reduces to the word problem for string rewriting systems over
`Alpha ℕ Sym2`, through `haltToSemiThue`. -/
def haltReducesSemiThue : HaltProblem ⪯ₘ @DecisionProblem (Alpha ℕ Foundations.Normalize.Sym2) :=
  ⟨haltToSemiThue, halt_reducesto_semiThue_spec⟩

/-- **The word problem for string rewriting systems is `Undecidable`**, over `Alpha ℕ Sym2`. -/
def undecidableSemiThue : Undecidable (@DecisionProblem (Alpha ℕ Foundations.Normalize.Sym2)) :=
  haltReducesSemiThue

end DiagonaLean.SemiThue.Reduction
