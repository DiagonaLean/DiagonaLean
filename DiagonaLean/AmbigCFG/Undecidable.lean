/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.AmbigCFG.Reductions.PCP_to_AmbigCFG

@[expose] public section

/-! # Undecidability of CFG ambiguity

CFG ambiguity is undecidable over any alphabet with two distinct letters (`ambigcfgUndecidable`).
An instance bundles the grammar with the number of tiles of the PCP instance it came from
(`AmbigCFGInstance`), so that all instances share one type.
-/

variable {α : Type} [DecidableEq α]

namespace DiagonaLean.AmbigCFG.Reduction

open DiagonaLean.PCP DiagonaLean.AmbigCFG DiagonaLean.Synthetic.Notation

/-- CFG ambiguity is undecidable over any alphabet with two distinct letters `b0`, `b1`, through
`pcpReducesAmbigCFG`. -/
def ambigcfgUndecidable (b0 b1 : α) (hne : b0 ≠ b1) :
    Undecidable (fun G : AmbigCFGInstance α => G.2.DecisionProblem) := by
  reduce_from_pcp over_letters b0 b1 via pcpReducesAmbigCFG

end DiagonaLean.AmbigCFG.Reduction
