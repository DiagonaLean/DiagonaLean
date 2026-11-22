/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga
-/

import DiagonaLean.PCP.Reductions.Halt_to_PCP

@[expose] public section

/-! # Undecidability of PCP

PCP is undecidable over the fixed alphabet `Ext (Alpha ℕ Bool)` (`undecidablePCP'`), and over
any alphabet with two distinct letters (`undecidablePCP`), by transporting the first result along
`AlphabetLift.pcpAlphabetLift`. The machine-level statements are in `MachineLevel.lean`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.PCP.Reduction

open DiagonaLean.MPCP.Reduction DiagonaLean.Synthetic.Definitions

/-- **PCP is synthetically halting-hard over the fixed alphabet `Ext (Alpha ℕ Bool)`.** -/
def undecidablePCP' :
    SynthHaltReduction (@DecisionProblem (Ext (Alpha ℕ Bool))) :=
  haltReducesPCP

/-- **PCP is synthetically halting-hard over any alphabet `α` with two distinct letters `b0`,
`b1`.** Obtained by transporting `undecidablePCP'` along `AlphabetLift.pcpAlphabetLift`. The letters
are arguments rather than taken from `Nontrivial α`, since a definition cannot extract data from a
proof. -/
def undecidablePCP {α : Type} (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DecisionProblem α) :=
  SynthHaltReduction.comp undecidablePCP' (AlphabetLift.pcpAlphabetLift b0 b1 hne)

end DiagonaLean.PCP.Reduction
