/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.Synthetic.Tactics.UndecFrom
import DiagonaLean.EmpCFG.Reductions.PCP_to_EmpCFG
import DiagonaLean.EmpCFG.AlphabetLift

@[expose] public section

/-! # Non-emptiness of CFG intersection is synthetically halting-hard

Non-emptiness of the intersection of two context-free grammars is synthetically halting-hard over
the terminals `Term α`, for any alphabet `α` with two distinct letters (`EmpCFG.synthFromHaltTerm`).
Encoding the terminals of both grammars (`EmpCFG.synthAlphabetLift`, `AlphabetLift.lean`) moves it
to any alphabet with two distinct letters (`EmpCFG.synthFromHaltOver`), for instance to `Bool`
(`EmpCFG.synthFromHaltBool`). The undecidability results, on grammar codes, are in
`Undecidable.lean`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

open DiagonaLean.Synthetic.Definitions

namespace DiagonaLean.EmpCFG.Reduction

open DiagonaLean.EmpCFG DiagonaLean.PCP ContextFreeGrammar

/-- **Non-emptiness of the intersection of two context-free grammars is synthetically
halting-hard.** This holds over the terminals `Term α`, for any alphabet `α` with two distinct
letters `b0`, `b1`, through `pcpToEmpCFG`. -/
def _root_.DiagonaLean.EmpCFG.synthFromHaltTerm {α : Type} [DecidableEq α] (b0 b1 : α)
    (hne : b0 ≠ b1) :
    SynthHaltReduction (@DiagonaLean.EmpCFG.DecisionProblem (Term α)) := by
  reduce_from_pcp over_letters b0 b1 with pcpToEmpCFG using pcp_reducesto_empCFG_spec

/-- **Non-emptiness of the intersection of two context-free grammars is synthetically halting-hard
over any alphabet `α` with two distinct letters `b0`, `b1`.** -/
def _root_.DiagonaLean.EmpCFG.synthFromHaltOver {α : Type} (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DiagonaLean.EmpCFG.DecisionProblem α) :=
  SynthHaltReduction.comp (EmpCFG.synthFromHaltTerm false true Bool.false_ne_true)
    (EmpCFG.synthAlphabetLift b0 b1 hne)

/-- **Non-emptiness of the intersection of two context-free grammars over `Bool` is
synthetically halting-hard.** -/
@[undecReduction] def _root_.DiagonaLean.EmpCFG.synthFromHaltBool :
    SynthHaltReduction (@DiagonaLean.EmpCFG.DecisionProblem Bool) :=
  EmpCFG.synthFromHaltOver false true Bool.false_ne_true

end DiagonaLean.EmpCFG.Reduction
