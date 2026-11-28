/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.AmbigCFG.Reductions.PCP_to_AmbigCFG
import DiagonaLean.AmbigCFG.AlphabetLift
import DiagonaLean.PCP.SynthHardness
import DiagonaLean.Foundations.Codes.Tactic

@[expose] public section

/-! # CFG ambiguity is synthetically halting-hard

CFG ambiguity is synthetically halting-hard over any alphabet with two distinct letters
(`AmbigCFG.synthFromHaltOver`). An instance bundles the grammar with the number of tiles of the PCP
instance it came from (`AmbigCFGInstance`), so that all instances share one type. On grammar codes
over any alphabet with two distinct letters it is too (`AmbigCFG.synthCodeFromHaltOver`), through
`ambCode` and the lifting along `ambCodeFunctor`. The undecidability results are in
`Undecidable.lean`.

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

end DiagonaLean.AmbigCFG.Reduction

namespace DiagonaLean.AmbigCFG.AlphabetLift

open DiagonaLean.AmbigCFG.Reduction DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Codes
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions

variable {α : Type}

/-- **Ambiguity of grammar codes is synthetically halting-hard over any alphabet `α` with two
distinct letters
`b0`, `b1`**: from PCP over `Bool` to codes over `Bool ⊕ ℕ`, then the lifting. -/
def _root_.DiagonaLean.AmbigCFG.synthCodeFromHaltOver [DecidableEq α] (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction fun c : CFGCode α => AmbigCFG.DecisionProblem c.toCFG :=
  have u₀ : SynthHaltReduction fun c : CFGCode (Bool ⊕ ℕ) => AmbigCFG.DecisionProblem c.toCFG := by
    synth_reduce_from (PCP.synthFromHaltOver false true Bool.false_ne_true) with ambCode
      using pcp_reducesto_ambigCFGCode_spec
  have u : SynthHaltReduction (@CodeProblem (Bool ⊕ ℕ)) :=
    SynthHaltReduction.comp u₀ codeProblemReduces
  have u' : SynthHaltReduction (@CodeProblem α) := by code_lift ambCodeFunctor from u
  SynthHaltReduction.comp u' codeProblemReduces'

end DiagonaLean.AmbigCFG.AlphabetLift
