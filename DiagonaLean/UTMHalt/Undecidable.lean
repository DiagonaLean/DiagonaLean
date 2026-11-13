/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Akhilesh Balaji
-/

import DiagonaLean.UTMHalt.Reductions.Halt_to_UTMHalt

@[expose] public section

/-! # Undecidability of the UTM halting problem

No Turing machine decides the halting problem of a weakly universal machine
(`not_exists_haltDeciderFor_of_isWeaklyUniversal`). The statement is about machines: no universal
machine is constructed, so there is no many-one reduction to `UTMHaltProblem`.
-/

namespace DiagonaLean.UTMHalt.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Foundations.UniversalTuringMachine DiagonaLean.Halt.Undecidable

/-- The halting problem of a single weakly universal machine is undecidable. -/
theorem not_exists_haltDeciderFor_of_isWeaklyUniversal (hU : IsWeaklyUniversal U) :
    ¬ ∃ D : SingleTapeTM Bool, IsHaltDeciderFor U D := by
  rintro ⟨D, hD⟩
  exact halt_undecidable
    ⟨D, isHaltDecider_of_isHaltDeciderFor hU hD⟩

end DiagonaLean.UTMHalt.Reduction
