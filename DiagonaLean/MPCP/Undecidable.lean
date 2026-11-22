/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.Reductions.Halt_to_MPCP
import DiagonaLean.MPCP.AlphabetLift
import DiagonaLean.Foundations.Codes.Tactic

@[expose] public section

/-! # Undecidability of MPCP

`haltReducesMPCP` (`Reductions/Halt_to_MPCP.lean`) many-one reduces the halting problem to MPCP over
the fixed alphabet `Alpha ℕ Sym2`, so MPCP is synthetically halting-hard there (`undecidableMPCP`).
MPCP is a functor on codes (`AlphabetLift.lean`), so it is synthetically halting-hard over every
alphabet with two distinct letters (`undecidableMPCPOf`), for instance over `Bool`
(`undecidableMPCPBool`). The machine-level statements are in `MachineLevel.lean`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.MPCP.Reduction

open DiagonaLean.PCP DiagonaLean.Synthetic.Definitions

variable {α : Type}

/-- **MPCP is synthetically halting-hard over the fixed alphabet `Alpha ℕ Sym2`.** -/
def undecidableMPCP :
    SynthHaltReduction (@MPCP.DecisionProblem (Alpha ℕ Foundations.Computability.Normalize.Sym2)) :=
  haltReducesMPCP

/-- **MPCP is synthetically halting-hard over any alphabet `α` with two distinct letters `b0`,
`b1`.** -/
def undecidableMPCPOf (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@MPCP.DecisionProblem α) := by
  code_lift mpcpFunctor from undecidableMPCP

/-- **MPCP over `Bool` is synthetically halting-hard.** -/
def undecidableMPCPBool : SynthHaltReduction MPCProblem :=
  undecidableMPCPOf false true Bool.false_ne_true

end DiagonaLean.MPCP.Reduction
