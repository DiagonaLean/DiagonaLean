/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Reductions.ListHalt_to_CM2
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # Halting of two-counter machines is synthetically halting-hard

`listToCM2` (`Reductions/ListHalt_to_CM2.lean`) many-one reduces halting of list machines given
by a table to halting of two-counter machines from address 0 with both counters zero
(`listHalt_reducesto_cm2_spec`). Halting of list machines is synthetically halting-hard
(`ListHalt.synthFromHalt`), so halting of two-counter machines is (`CM2.synthFromHalt`). The
theorem is due to Minsky. The undecidability results are in `Undecidable.lean`.

## Main statements

* `CM2.synthFromHalt`: the halting problem reduces to halting of two-counter machines.

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967], Section 14.1
-/

namespace DiagonaLean.CM2.Reduction

open DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions

/-- **Halting of two-counter machines is synthetically halting-hard**: halting of list machines
is (`ListHalt.synthFromHalt`), and `listToCM2` reduces it to halting of two-counter machines. -/
@[undecReduction] def _root_.DiagonaLean.CM2.synthFromHalt :
    SynthHaltReduction DecisionProblem := by
  synth_reduce_from ListHalt.synthFromHalt with (listToCM2 none)
    using (listHalt_reducesto_cm2_spec none)

end DiagonaLean.CM2.Reduction
