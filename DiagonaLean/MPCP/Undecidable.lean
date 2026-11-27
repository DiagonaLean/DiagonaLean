/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Synthetic.Tactics.UndecFrom
import DiagonaLean.MPCP.Reductions.Halt_to_MPCP
import DiagonaLean.MPCP.AlphabetLift
import DiagonaLean.Foundations.Codes.Tactic

@[expose] public section

/-! # Undecidability of MPCP

`MPCP.synthFromHalt` (`Reductions/Halt_to_MPCP.lean`) many-one reduces the halting problem to MPCP
over the fixed alphabet `Alpha ℕ Sym2`, so MPCP is synthetically halting-hard there. MPCP is a
functor on codes (`AlphabetLift.lean`), so it is synthetically halting-hard over every alphabet with
two distinct letters (`MPCP.synthFromHaltOver`), for instance over `Bool`
(`MPCP.synthFromHaltBool`). The machine-level statements are in `MachineLevel.lean`. The former
names (`undecidableMPCP`, `haltReducesMPCP`, …) remain as deprecated aliases.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.MPCP.Reduction

open DiagonaLean.PCP DiagonaLean.Synthetic.Definitions

variable {α : Type}

/-- The former name of `MPCP.synthFromHalt`. -/
@[deprecated DiagonaLean.MPCP.synthFromHalt (since := "2026-11-23")]
abbrev undecidableMPCP := @DiagonaLean.MPCP.synthFromHalt

/-- **MPCP is synthetically halting-hard over any alphabet `α` with two distinct letters `b0`,
`b1`.** -/
def _root_.DiagonaLean.MPCP.synthFromHaltOver (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@MPCP.DecisionProblem α) := by
  code_lift mpcpFunctor from MPCP.synthFromHalt

/-- The former name of `MPCP.synthFromHaltOver`. -/
@[deprecated DiagonaLean.MPCP.synthFromHaltOver (since := "2026-11-23")]
abbrev undecidableMPCPOf := @DiagonaLean.MPCP.synthFromHaltOver

/-- **MPCP over `Bool` is synthetically halting-hard.** -/
@[undecReduction] def _root_.DiagonaLean.MPCP.synthFromHaltBool : SynthHaltReduction MPCProblem :=
  MPCP.synthFromHaltOver false true Bool.false_ne_true

/-- The former name of `MPCP.synthFromHaltBool`. -/
@[deprecated DiagonaLean.MPCP.synthFromHaltBool (since := "2026-11-23")]
abbrev undecidableMPCPBool := @DiagonaLean.MPCP.synthFromHaltBool

end DiagonaLean.MPCP.Reduction
