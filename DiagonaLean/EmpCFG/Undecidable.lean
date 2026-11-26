/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.EmpCFG.Reductions.PCP_to_EmpCFG
import DiagonaLean.EmpCFG.AlphabetLift

@[expose] public section

/-! # Undecidability of the non-emptiness of CFG intersection

Non-emptiness of the intersection of two context-free grammars is undecidable over the terminals
`Term α`, for any alphabet `α` with two distinct letters (`EmpCFG.synthFromHaltTerm`). Encoding the
terminals of both grammars (`EmpCFG.synthAlphabetLift`, `AlphabetLift.lean`) moves it to any
alphabet with two distinct letters (`EmpCFG.synthFromHaltOver`), for instance to `Bool`
(`EmpCFG.synthFromHaltBool`).

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

open DiagonaLean.Synthetic.Definitions

namespace DiagonaLean.EmpCFG.Reduction

open DiagonaLean.EmpCFG DiagonaLean.PCP ContextFreeGrammar

/-- **Non-emptiness of the intersection of two context-free grammars is synthetically
halting-hard.** This holds over the terminals `Term α`, for any alphabet `α` with two distinct
letters `b0`, `b1`, through `EmpCFG.synthFromPCP`. -/
def _root_.DiagonaLean.EmpCFG.synthFromHaltTerm {α : Type} [DecidableEq α] (b0 b1 : α)
    (hne : b0 ≠ b1) :
    SynthHaltReduction (@DiagonaLean.EmpCFG.DecisionProblem (Term α)) := by
  reduce_from_pcp over_letters b0 b1 via EmpCFG.synthFromPCP

/-- The former name of `EmpCFG.synthFromHaltTerm`. -/
@[deprecated DiagonaLean.EmpCFG.synthFromHaltTerm (since := "2026-11-23")]
abbrev undecidableEmpCFG := @DiagonaLean.EmpCFG.synthFromHaltTerm

/-- **Non-emptiness of the intersection of two context-free grammars is synthetically halting-hard
over any alphabet `α` with two distinct letters `b0`, `b1`.** -/
def _root_.DiagonaLean.EmpCFG.synthFromHaltOver {α : Type} (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DiagonaLean.EmpCFG.DecisionProblem α) :=
  SynthHaltReduction.comp (EmpCFG.synthFromHaltTerm false true Bool.false_ne_true)
    (EmpCFG.synthAlphabetLift b0 b1 hne)

/-- The former name of `EmpCFG.synthFromHaltOver`. -/
@[deprecated DiagonaLean.EmpCFG.synthFromHaltOver (since := "2026-11-23")]
abbrev undecidableEmpCFGOf := @DiagonaLean.EmpCFG.synthFromHaltOver

/-- **Non-emptiness of the intersection of two context-free grammars over `Bool` is
synthetically halting-hard.** -/
def _root_.DiagonaLean.EmpCFG.synthFromHaltBool :
    SynthHaltReduction (@DiagonaLean.EmpCFG.DecisionProblem Bool) :=
  EmpCFG.synthFromHaltOver false true Bool.false_ne_true

/-- The former name of `EmpCFG.synthFromHaltBool`. -/
@[deprecated DiagonaLean.EmpCFG.synthFromHaltBool (since := "2026-11-23")]
abbrev undecidableEmpCFGBool := @DiagonaLean.EmpCFG.synthFromHaltBool

end DiagonaLean.EmpCFG.Reduction
