/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga
-/

import DiagonaLean.Synthetic.Tactics.UndecFrom
import DiagonaLean.PCP.Reductions.Halt_to_PCP

@[expose] public section

/-! # PCP is synthetically halting-hard

PCP is synthetically halting-hard over the fixed alphabet `Ext (Alpha ℕ Bool)`
(`PCP.synthFromHalt`), and over any alphabet with two distinct letters (`PCP.synthFromHaltOver`), by
transporting the first result along `PCP.synthAlphabetLift`; over `Bool` this is
`PCP.synthFromHaltBool`. The undecidability results are in `Undecidable.lean`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.PCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.MPCP.Reduction DiagonaLean.Halt
  DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Computability.Normalize
open DiagonaLean.PCP.AlphabetLift DiagonaLean.Synthetic.Definitions

/-- **PCP is synthetically halting-hard over the fixed alphabet `Ext (Alpha ℕ Bool)`.** The halting
problem many-one reduces to PCP over the fixed alphabet `Ext (Alpha ℕ Bool)`. -/
def _root_.DiagonaLean.PCP.synthFromHalt :
    HaltProblem ⪯_s (@DecisionProblem (Ext (Alpha ℕ Bool))) :=
  ⟨haltToPcp, halt_reducesto_pcp_spec⟩

end DiagonaLean.PCP.Reduction

namespace DiagonaLean.PCP.Reduction

open DiagonaLean.MPCP.Reduction DiagonaLean.Synthetic.Definitions

/-- **PCP is synthetically halting-hard over any alphabet `α` with two distinct letters `b0`,
`b1`.** Obtained by transporting `PCP.synthFromHalt` along `PCP.synthAlphabetLift`. The letters
are arguments rather than taken from `Nontrivial α`, since a definition cannot extract data from a
proof. -/
def _root_.DiagonaLean.PCP.synthFromHaltOver {α : Type} (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DecisionProblem α) :=
  SynthHaltReduction.comp PCP.synthFromHalt (PCP.synthAlphabetLift b0 b1 hne)

/-- PCP over `Bool` is displayed as binary PCP. -/
instance : Synthetic.ReductionChain.ProblemName PCProblem :=
  ⟨"Binary PCP"⟩

/-- **PCP over `Bool` is synthetically halting-hard.** -/
@[undecReduction] def _root_.DiagonaLean.PCP.synthFromHaltBool : SynthHaltReduction PCProblem :=
  PCP.synthFromHaltOver false true Bool.false_ne_true

end DiagonaLean.PCP.Reduction
