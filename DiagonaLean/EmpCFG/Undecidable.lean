/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.EmpCFG.Reductions.PCP_to_EmpCFG

@[expose] public section

/-! # Undecidability of the non-emptiness of CFG intersection

Non-emptiness of the intersection of two context-free grammars is undecidable over the terminals
`Term α`, for any alphabet `α` with two distinct letters (`empcfgUndecidable`).
-/

open DiagonaLean.Synthetic.Notation

namespace EmpCFG.Reduction

open DiagonaLean.EmpCFG DiagonaLean.PCP ContextFreeGrammar

/-- Non-emptiness of the intersection of two context-free grammars over the terminals `Term α` is
undecidable, for any alphabet `α` with two distinct letters `b0`, `b1`, through
`pcpReducesEmpCFG`. -/
def empcfgUndecidable {α : Type} [DecidableEq α] (b0 b1 : α) (hne : b0 ≠ b1) :
    Undecidable (@DiagonaLean.EmpCFG.DecisionProblem (Term α)) := by
  reduceFromPCP over_letters b0 b1 via pcpReducesEmpCFG

end EmpCFG.Reduction
