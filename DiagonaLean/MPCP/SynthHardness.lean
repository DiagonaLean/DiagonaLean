/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Synthetic.Tactics.UndecFrom
import DiagonaLean.MPCP.Undecidable
import DiagonaLean.MPCP.AlphabetLift
import DiagonaLean.Foundations.Codes.Tactic

@[expose] public section

/-! # MPCP is synthetically halting-hard

`MPCP.synthFromHalt` many-one reduces the halting problem to MPCP over the fixed alphabet
`Alpha ℕ Sym2`: it is the proved reduction `MPCP.fromHalt` (`Undecidable.lean`), read as a synthetic
one through the bridge from `HaltProblem` to `HaltCanon` (`HaltReduction.toSynthHalt`). MPCP is a
functor on codes (`AlphabetLift.lean`), so it is synthetically halting-hard over every alphabet with
two distinct letters (`MPCP.synthFromHaltOver`), for instance over `Bool`
(`MPCP.synthFromHaltBool`). The undecidability results, from a halting reduction proved computable,
are in `Undecidable.lean`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.MPCP.Reduction

open DiagonaLean.Halt DiagonaLean.Foundations.Computability.Normalize

/-- **MPCP is synthetically halting-hard over the fixed alphabet `Alpha ℕ Sym2`**: the proved
reduction `MPCP.fromHalt`, through the bridge. -/
def _root_.DiagonaLean.MPCP.synthFromHalt :
    HaltProblem ⪯_s (@MPCP.DecisionProblem (Alpha ℕ Sym2)) :=
  MPCP.fromHalt.toSynthHalt

end DiagonaLean.MPCP.Reduction

namespace DiagonaLean.MPCP.Reduction

open DiagonaLean.PCP DiagonaLean.Synthetic.Definitions

variable {α : Type}

/-- **MPCP is synthetically halting-hard over any alphabet `α` with two distinct letters `b0`,
`b1`.** -/
def _root_.DiagonaLean.MPCP.synthFromHaltOver (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@MPCP.DecisionProblem α) := by
  code_lift mpcpFunctor from MPCP.synthFromHalt

/-- **MPCP over `Bool` is synthetically halting-hard.** -/
@[undecReduction] def _root_.DiagonaLean.MPCP.synthFromHaltBool : SynthHaltReduction MPCProblem :=
  MPCP.synthFromHaltOver false true Bool.false_ne_true

end DiagonaLean.MPCP.Reduction
