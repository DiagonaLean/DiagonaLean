/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Reductions.ListHalt_to_CM2
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Undecidability of halting for two-counter machines

`listToCM2` (`Reductions/ListHalt_to_CM2.lean`) reduces halting of list machines given by a table
to halting of two-counter machines from address 0 with both counters zero
(`listHalt_reducesto_cm2_spec`), and it is primitive recursive (`listToCM2_prim`). Halting of list
machines is halting-hard (`ListHalt.fromHalt`), so halting of two-counter machines is
(`CM2.fromHalt`). The theorem is due to Minsky. The synthetic result is in `SynthHardness.lean`.

## Main statements

* `CM2.fromHalt`: halting of two-counter machines is halting-hard.
* By `halt_results`: `CM2.haltHard`, `CM2.not_computablePred`, `CM2.not_machineDecidable`. Halting
  of two-counter machines is halting-hard and undecidable, and no Turing machine decides it under
  any computable encoding of programs.

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967], Section 14.1
-/

namespace DiagonaLean.CM2

open DiagonaLean.CM2.Reduction DiagonaLean.Foundations.Computability

/-- **Halting of two-counter machines from zero counters is halting-hard**: halting of list
machines is (`ListHalt.fromHalt`), and `listToCM2` reduces it to halting of two-counter machines
and is primitive recursive. -/
def fromHalt : HaltReduction DecisionProblem := by
  hard_reduce_from ListHalt.fromHalt with (listToCM2 none) using (listHalt_reducesto_cm2_spec none)

halt_results DecisionProblem from fromHalt

end DiagonaLean.CM2
