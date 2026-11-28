/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Reductions.Halt_to_CM2

@[expose] public section

/-! # Halting of two-counter machines is synthetically halting-hard

`haltToCM2` (`Reductions/Halt_to_CM2.lean`) many-one reduces the halting problem to halting of
two-counter machines from address 0 with both counters zero (`halt_reducesto_cm2_spec`), so
halting of two-counter machines is synthetically halting-hard (`CM2.synthFromHalt`). The theorem
is due to Minsky. The undecidability results are in `Undecidable.lean`.

## Main statements

* `CM2.synthFromHalt`: the halting problem reduces to halting of two-counter machines.

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967], Section 14.1
-/

namespace DiagonaLean.CM2.Reduction

open DiagonaLean.Halt DiagonaLean.Synthetic.Definitions

/-- **Halting of two-counter machines is synthetically halting-hard**: the halting problem
many-one reduces to it through `haltToCM2`. -/
@[undecReduction] def _root_.DiagonaLean.CM2.synthFromHalt : HaltProblem ⪯_s DecisionProblem :=
  ⟨haltToCM2, halt_reducesto_cm2_spec⟩

end DiagonaLean.CM2.Reduction
