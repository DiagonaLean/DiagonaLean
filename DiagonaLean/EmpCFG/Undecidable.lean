/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.EmpCFG.Reductions.PCP_to_EmpCFG

@[expose] public section

/-! # Undecidability of the non-emptiness of CFG intersection

Non-emptiness of the intersection of two context-free grammars is undecidable over the terminals
`Term α`, for any alphabet `α` with two distinct letters (`empcfg_undecidable`).
-/

open DiagonaLean.Synthetic.Notation

namespace EmpCFG.Reduction

open DiagonaLean.EmpCFG DiagonaLean.PCP ContextFreeGrammar

/-- Non-emptiness of the intersection of two context-free grammars over the terminals `Term α` is
undecidable, for any alphabet `α` with two distinct letters, through `pcpReducesEmpCFG`. -/
theorem empcfg_undecidable {α : Type} [DecidableEq α] [Nontrivial α] :
    Undecidable (@DiagonaLean.EmpCFG.DecisionProblem (Term α)) := by
  reduceFromPCP over_type α via pcpReducesEmpCFG

end EmpCFG.Reduction
