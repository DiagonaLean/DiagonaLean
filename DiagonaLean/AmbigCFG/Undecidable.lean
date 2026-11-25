/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.AmbigCFG.Reductions.PCP_to_AmbigCFG

@[expose] public section

/-! # Undecidability of CFG ambiguity

CFG ambiguity is undecidable over any alphabet with two distinct letters
(`AmbigCFG.synthFromHaltOver`). An instance bundles the grammar with the number of tiles of the PCP
instance it came from (`AmbigCFGInstance`), so that all instances share one type.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
  Theorem 9.20.
-/

variable {α : Type} [DecidableEq α]

namespace DiagonaLean.AmbigCFG.Reduction

open DiagonaLean.PCP DiagonaLean.AmbigCFG DiagonaLean.Synthetic.Definitions

/-- **CFG ambiguity is synthetically halting-hard.** This holds over any alphabet with two distinct
letters `b0`, `b1`, through `pcpToAmbigCFG`. -/
def _root_.DiagonaLean.AmbigCFG.synthFromHaltOver (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (fun G : AmbigCFGInstance α => AmbigCFG.DecisionProblem G.2) := by
  reduce_from_pcp over_letters b0 b1 with pcpToAmbigCFG using pcp_reducesto_ambigCFG_spec

/-- The former name of `AmbigCFG.synthFromHaltOver`. -/
@[deprecated DiagonaLean.AmbigCFG.synthFromHaltOver (since := "2026-11-23")]
abbrev undecidableAmbigCFG := @DiagonaLean.AmbigCFG.synthFromHaltOver

end DiagonaLean.AmbigCFG.Reduction
