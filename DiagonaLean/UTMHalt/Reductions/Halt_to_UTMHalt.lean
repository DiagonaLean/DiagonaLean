/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Akhilesh Balaji
-/

import DiagonaLean.UTMHalt.Basic

@[expose] public section

/-! # Halting of universal machines

A weakly universal machine `U` halts on `instanceEncoding M w` exactly when `M` halts on `w`
(`halt_iff_weakutmhalt`), and the same holds for a universal machine (`halt_iff_utmhalt`). A
machine deciding the halting problem of a weakly universal machine decides the general halting
problem (`isHaltDecider_of_isHaltDeciderFor`). These are equivalences of propositions; no
many-one reduction is built, since no universal machine is constructed.
-/

namespace DiagonaLean.UTMHalt.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Halt.Helpers
  DiagonaLean.UTMHalt.UniversalTuringMachine DiagonaLean.Halt.Undecidable

/-- A weakly universal machine halts on at least one input. -/
theorem IsWeaklyUniversalWrt.exists_halts (hU : IsWeaklyUniversalWrt pair U) :
    ∃ x : List Bool, Halts U x :=
  ⟨pair (encodeBoolTM ⟨haltTM, inferInstance⟩) [],
    (hU ⟨haltTM, inferInstance⟩ []).mpr (halts_haltTM [])⟩

/-- A weakly universal machine diverges on at least one input: it is not a total machine. -/
theorem IsWeaklyUniversalWrt.exists_not_halts (hU : IsWeaklyUniversalWrt pair U) :
    ∃ x : List Bool, ¬ Halts U x :=
  ⟨pair (encodeBoolTM ⟨loopTM, inferInstance⟩) [],
    fun h => not_halts_loopTM [] ((hU ⟨loopTM, inferInstance⟩ []).mp h)⟩

/-- A machine deciding the halting problem of a weakly universal machine decides the
general halting problem. -/
theorem isHaltDecider_of_isHaltDeciderFor {D : SingleTapeTM Bool}
    (hU : IsWeaklyUniversal U) (hD : IsHaltDeciderFor U D) : IsHaltDecider D := by
  intro tm w
  refine ⟨fun h => (hD _).1 ((hU tm w).mpr h), fun h => (hD _).2 ?_⟩
  exact fun h' => h ((hU tm w).mp h')

/-- If `U` is weakly universal, then `M` halts on `w` iff `U` halts on `instanceEncoding M w`. -/
theorem halt_iff_weakutmhalt (hU : IsWeaklyUniversal U) (M : EncodableTM Bool)
    (w : List Bool) :
    Halts M.toSingleTapeTM w ↔ WeakUTMHalts U hU M w :=
  (hU M w).symm

/-- If `U` is universal, then `M` halts on `w` iff `U` halts on `instanceEncoding M w`. -/
theorem halt_iff_utmhalt (hU : IsUniversal U) (M : EncodableTM Bool)
    (w : List Bool) :
    Halts M.toSingleTapeTM w ↔ UTMHalts U hU M w :=
  (hU M w).left.symm

end DiagonaLean.UTMHalt.Reduction
