/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga
-/

import DiagonaLean.PCP.Reductions.Halt_to_PCP

@[expose] public section

/-! # Undecidability of PCP

PCP is undecidable over the fixed alphabet `Ext (Alpha ℕ Bool)` (`PCP.synthFromHalt`), and over any
alphabet with two distinct letters (`PCP.synthFromHaltOver`), by transporting the first result along
`PCP.synthAlphabetLift`. The machine-level statements are in `MachineLevel.lean`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.PCP.Reduction

open DiagonaLean.MPCP.Reduction DiagonaLean.Synthetic.Definitions

/-- The former name of `PCP.synthFromHalt`. -/
@[deprecated DiagonaLean.PCP.synthFromHalt (since := "2026-11-23")]
abbrev undecidablePCP' := @DiagonaLean.PCP.synthFromHalt

/-- **PCP is synthetically halting-hard over any alphabet `α` with two distinct letters `b0`,
`b1`.** Obtained by transporting `PCP.synthFromHalt` along `PCP.synthAlphabetLift`. The letters
are arguments rather than taken from `Nontrivial α`, since a definition cannot extract data from a
proof. -/
def _root_.DiagonaLean.PCP.synthFromHaltOver {α : Type} (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DecisionProblem α) :=
  SynthHaltReduction.comp PCP.synthFromHalt (PCP.synthAlphabetLift b0 b1 hne)

/-- The former name of `PCP.synthFromHaltOver`. -/
@[deprecated DiagonaLean.PCP.synthFromHaltOver (since := "2026-11-23")]
abbrev undecidablePCP := @DiagonaLean.PCP.synthFromHaltOver

end DiagonaLean.PCP.Reduction
