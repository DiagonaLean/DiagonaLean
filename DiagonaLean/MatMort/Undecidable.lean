/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Aristotle (Harmonic), Prathamesh Turaga
-/

import DiagonaLean.MatMort.Reductions.PCP_to_MatMort

/-! # Undecidability of matrix mortality

Mortality of finite sets of `3 × 3` integer matrices is undecidable (`matmort_undecidable`).
-/

namespace DiagonaLean.MatMort.Reduction

open DiagonaLean.PCP DiagonaLean.MatMort DiagonaLean.Synthetic.Notation

/-- Matrix mortality of `3 × 3` integer matrices is undecidable: reduced from PCP over the
alphabet `S23 = {2, 3}` through `pcpReducesMatMort`. -/
theorem matmort_undecidable : Undecidable (fun Ws => DecisionProblem Ws) := by
  reduceFromPCP over_type S23 via pcpReducesMatMort

end DiagonaLean.MatMort.Reduction
