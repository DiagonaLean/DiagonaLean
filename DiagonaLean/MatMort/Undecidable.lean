/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Aristotle (Harmonic), Prathamesh Turaga
-/

import DiagonaLean.Foundations.Computability.UndecTransfer
import DiagonaLean.MatMort.Primrec
import DiagonaLean.PCP.Undecidable
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Undecidability of matrix mortality

The reduction `matImage` from PCP over `S23` is primitive recursive (`matImage_primrec`), so with
`PCP.fromHaltOver` it gives the halting reduction `MatMort.fromHalt`, proved computable. So
mortality of finite sets of `3 × 3` integer matrices is halting-hard (`MatMort.haltHard`), is
undecidable (`MatMort.not_computablePred`), and no Turing machine decides it under any computable
encoding (`MatMort.not_machineDecidable`).

## Main statements

* `MatMort.fromHalt`: a reduction from the halting problem, proved computable.
* `MatMort.haltHard`, `MatMort.not_computablePred`, `MatMort.not_machineDecidable`: its
  consequences, stated by `halt_results`.

The synthetic result is in `SynthHardness.lean`.

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatMort

open DiagonaLean.MatMort.Reduction DiagonaLean.Foundations.Computability

/-- **Matrix mortality of `3 × 3` integer matrices is halting-hard** (Paterson 1970): PCP over `S23`
is (`PCP.fromHaltOver`), and `matImage` reduces it to mortality (`pcp_reducesto_matMort_spec`),
computably (`matImage_primrec`). -/
def fromHalt : HaltReduction DecisionProblem := by
  hard_reduce_from (PCP.fromHaltOver (0 : S23) 1 (by decide)) with matImage
    using pcp_reducesto_matMort_spec

/-- Matrix mortality is registered as halting-hard. -/
instance : HaltSource DecisionProblem := ⟨fromHalt⟩

halt_results DecisionProblem from fromHalt

attribute [undecHardness] not_computablePred

end DiagonaLean.MatMort
