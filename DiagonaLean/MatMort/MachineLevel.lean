/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Aristotle (Harmonic), Prathamesh Turaga
-/

import DiagonaLean.MatMort.Primrec
import DiagonaLean.PCP.MachineLevel

@[expose] public section

/-! # Matrix mortality is not a computable predicate

The reduction `matImage` from PCP over `S23` is primitive recursive (`matImage_primrec`), so it
is proved computable (`MatMort.fromPCP`) and gives the halting reduction `MatMort.fromHalt` (from
`PCP.fromHaltOver`). So mortality of finite sets of `3 × 3` integer matrices is not a computable
predicate (`not_computablePred_matMort`), and no Turing machine decides it under any computable
encoding (`not_machineDecidable_matMort`).


## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatMort

open DiagonaLean.MatMort.Reduction DiagonaLean.Foundations.Computability

/-- **The reduction from PCP to matrix mortality, proved computable** (`matImage_primrec`). -/
def fromPCP : @PCP.DecisionProblem S23 ⪯ MatMort.DecisionProblem :=
  .ofSynth MatMort.synthFromPCP matImage_primrec.to_comp

/-- **Matrix mortality of `3 × 3` integer matrices is halting-hard**: PCP over `S23` is
(`PCP.fromHaltOver`), and `fromPCP`. -/
def fromHalt : HaltReduction MatMort.DecisionProblem := by
  reduce_from (PCP.fromHaltOver (0 : S23) 1 (by decide)) via MatMort.synthFromPCP

end DiagonaLean.MatMort

namespace DiagonaLean.MatMort.MachineLevel

open DiagonaLean.MatMort.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- **Matrix mortality of `3 × 3` integer matrices is not a computable predicate**: it is
halting-hard (`MatMort.fromHalt`). -/
theorem not_computablePred_matMort : ¬ ComputablePred DecisionProblem :=
  MatMort.fromHalt.not_computablePred

/-- **No Turing machine decides matrix mortality** of `3 × 3` integer matrices, under any
computable encoding of finite sets of matrices as bit strings. -/
theorem not_machineDecidable_matMort {enc : Finset (Matrix (Fin 3) (Fin 3) ℤ) → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc DecisionProblem :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_matMort

end DiagonaLean.MatMort.MachineLevel
