/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga
-/

import DiagonaLean.PCP.Reductions.Halt_to_PCP

/-! # Undecidability of PCP

PCP is undecidable over the fixed alphabet `Ext (Alpha ℕ Bool)` (`pcp_undecidable'`), and over
any alphabet with two distinct letters (`pcp_undecidable`), by transporting the first result along
`AlphabetLift.PCPAlphabetLift`.
-/

namespace DiagonaLean.PCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.MPCP.Reduction DiagonaLean.Halt
  DiagonaLean.Halt.Encoding DiagonaLean.PCP.AlphabetLift DiagonaLean.Synthetic.Notation

/-- PCP is undecidable over the fixed alphabet `Ext (Alpha ℕ Bool)`. -/
theorem pcp_undecidable' :
    Undecidable (@DecisionProblem (Ext (Alpha ℕ Bool))) :=
  ⟨haltReducesToPCP⟩

/-- PCP is undecidable over any `DecidableEq`, `Nontrivial` alphabet. Obtained by transporting
  `pcp_undecidable` along `AlphabetLift.PCP_alphabet_lift`. -/
@[nolint unusedArguments]
theorem pcp_undecidable {α : Type} [DecidableEq α] [Nontrivial α] :
    Undecidable (@DecisionProblem α) := by
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne α
  exact undecidability_from_reducibility
    pcp_undecidable'
    (AlphabetLift.PCPAlphabetLift b0 b1 hne)

end DiagonaLean.PCP.Reduction
