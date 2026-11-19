/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga
-/

import DiagonaLean.PCP.Reductions.Halt_to_PCP

/-! # Undecidability of PCP

PCP is undecidable over the fixed alphabet `Ext (Alpha ℕ Bool)` (`pcpUndecidable'`), and over
any alphabet with two distinct letters (`pcpUndecidable`), by transporting the first result along
`AlphabetLift.PCPAlphabetLift`.
-/

namespace DiagonaLean.PCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.MPCP.Reduction DiagonaLean.Halt
  DiagonaLean.Halt.Encoding DiagonaLean.PCP.AlphabetLift DiagonaLean.Synthetic.Notation

/-- PCP is undecidable over the fixed alphabet `Ext (Alpha ℕ Bool)`. -/
def pcpUndecidable' :
    Undecidable (@DecisionProblem (Ext (Alpha ℕ Bool))) :=
  haltReducesToPCP

/-- PCP is undecidable over any alphabet `α` with two distinct letters `b0`, `b1`. Obtained by
transporting `pcpUndecidable'` along `AlphabetLift.PCPAlphabetLift`. The letters are arguments
rather than taken from `Nontrivial α`, since a definition cannot extract data from a proof. -/
def pcpUndecidable {α : Type} (b0 b1 : α) (hne : b0 ≠ b1) :
    Undecidable (@DecisionProblem α) :=
  undecidabilityFromReducibility pcpUndecidable' (AlphabetLift.PCPAlphabetLift b0 b1 hne)

end DiagonaLean.PCP.Reduction
