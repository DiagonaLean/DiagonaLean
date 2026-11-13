/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.EmpCFG.Reductions.PCP_to_EmpCFG

@[expose] public section

/-! # Undecidability of the emptiness of CFG intersection

Emptiness of the intersection of two context-free grammars is undecidable over any alphabet with
two distinct letters (`empcfg_undecidable`).
-/

open DiagonaLean.Synthetic.Notation

namespace EmpCFG.Reduction

open DiagonaLean.EmpCFG DiagonaLean.PCP ContextFreeGrammar

/-- Emptiness of the intersection of two context-free grammars is undecidable: reduced from
PCP by pairing the two derived grammars `topCFG P`, `botCFG P` for each stack `P`. The
correctness equivalence is `pcp_iff_nempcfg`. -/
theorem empcfg_undecidable {α : Type} [DecidableEq α] [Nontrivial α] :
    Undecidable (fun (P : Stack α) => DecisionProblem (topCFG P, botCFG P)) := by
  reduceFromPCP over_type α with_red_function (fun P => P)
  · exact (pcp_iff_nempcfg K).mp hPCP
  · exact (pcp_iff_nempcfg K).mpr hC

end EmpCFG.Reduction
