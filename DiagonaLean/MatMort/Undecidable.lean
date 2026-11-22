/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Aristotle (Harmonic), Prathamesh Turaga
-/

import DiagonaLean.MatMort.Reductions.PCP_to_MatMort
import DiagonaLean.PCP.Undecidable

@[expose] public section

/-! # Undecidability of matrix mortality

Mortality of finite sets of `3 × 3` integer matrices is `Undecidable` (`undecidableMatMort`), by
the reduction from PCP over `S23` of `Reductions/PCP_to_MatMort.lean`. The machine-level
statements are in `MachineLevel.lean`.

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatMort.Reduction

open DiagonaLean.PCP DiagonaLean.MatMort DiagonaLean.Synthetic.Notation

/-- **Matrix mortality of `3 × 3` integer matrices is `Undecidable`.** It is reduced from PCP
over the alphabet `S23 = {2, 3}` through `pcpReducesMatMort`. -/
def undecidableMatMort : Undecidable (fun Ws => DecisionProblem Ws) := by
  reduce_from_pcp over_letters (0 : S23) (1 : S23) via pcpReducesMatMort

end DiagonaLean.MatMort.Reduction
