/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.EmpCFG.Reductions.PCP_to_EmpCFG
import DiagonaLean.EmpCFG.AlphabetLift

@[expose] public section

/-! # Undecidability of the non-emptiness of CFG intersection

Non-emptiness of the intersection of two context-free grammars is undecidable over the terminals
`Term α`, for any alphabet `α` with two distinct letters (`undecidableEmpCFG`). Encoding the
terminals of both grammars (`empCFGAlphabetLift`, `AlphabetLift.lean`) moves it to any alphabet
with two distinct letters (`undecidableEmpCFGOf`), for instance to `Bool`
(`undecidableEmpCFGBool`).

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

open DiagonaLean.Synthetic.Definitions

namespace DiagonaLean.EmpCFG.Reduction

open DiagonaLean.EmpCFG DiagonaLean.PCP ContextFreeGrammar

/-- **Non-emptiness of the intersection of two context-free grammars is synthetically
halting-hard.** This holds over the terminals `Term α`, for any alphabet `α` with two distinct
letters `b0`, `b1`,
through `pcpReducesEmpCFG`. -/
def undecidableEmpCFG {α : Type} [DecidableEq α] (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DiagonaLean.EmpCFG.DecisionProblem (Term α)) := by
  reduce_from_pcp over_letters b0 b1 via pcpReducesEmpCFG

/-- **Non-emptiness of the intersection of two context-free grammars is synthetically halting-hard
over any
alphabet `α` with two distinct letters `b0`, `b1`.** -/
def undecidableEmpCFGOf {α : Type} (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DiagonaLean.EmpCFG.DecisionProblem α) :=
  SynthHaltReduction.comp (undecidableEmpCFG false true Bool.false_ne_true)
    (empCFGAlphabetLift b0 b1 hne)

/-- **Non-emptiness of the intersection of two context-free grammars over `Bool` is
synthetically halting-hard.** -/
def undecidableEmpCFGBool : SynthHaltReduction (@DiagonaLean.EmpCFG.DecisionProblem Bool) :=
  undecidableEmpCFGOf false true Bool.false_ne_true

end DiagonaLean.EmpCFG.Reduction
