/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Aristotle (Harmonic), Prathamesh Turaga
-/

import DiagonaLean.MatMort.Reductions.PCP_to_MatMort
import DiagonaLean.MatMort.Primrec
import DiagonaLean.PCP.Undecidable

@[expose] public section

/-! # Undecidability of matrix mortality

Mortality of finite sets of `3 × 3` integer matrices is `Undecidable` (`undecidableMatMort`). It
is not a computable predicate (`not_computablePred_matMort`), so no Turing machine decides it under
any computable encoding (`not_machineDecidable_matMort`): PCP over `S23` is not a computable
predicate (`PCP.Reduction.not_computablePred_pcp`), and the reduction `matImage` is primitive
recursive (`matImage_primrec`).

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatMort.Reduction

open DiagonaLean.PCP DiagonaLean.MatMort DiagonaLean.Synthetic.Notation

/-- **Matrix mortality of `3 × 3` integer matrices is `Undecidable`.** It is reduced from PCP
over the alphabet `S23 = {2, 3}` through `pcpReducesMatMort`. -/
def undecidableMatMort : Undecidable (fun Ws => DecisionProblem Ws) := by
  reduce_from_pcp over_letters (0 : S23) (1 : S23) via pcpReducesMatMort

open DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions in
/-- **Matrix mortality of `3 × 3` integer matrices is not a computable predicate.** -/
theorem not_computablePred_matMort : ¬ ComputablePred MatMortProblem :=
  not_computablePred_of_reduces pcpReducesMatMort matImage_primrec.to_comp
    PCP.Reduction.not_computablePred_pcp

open DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions in
/-- **No Turing machine decides matrix mortality** of `3 × 3` integer matrices, under any
computable encoding of finite sets of matrices as bit strings. -/
theorem not_machineDecidable_matMort {enc : Finset (Matrix (Fin 3) (Fin 3) ℤ) → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc MatMortProblem :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_matMort

end DiagonaLean.MatMort.Reduction
