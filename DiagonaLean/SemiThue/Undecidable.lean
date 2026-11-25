/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.SemiThue.AlphabetLift
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # Undecidability of the word problem for string rewriting systems

`SemiThue.synthFromHalt` (`Reductions/Halt_to_SemiThue.lean`) many-one reduces the halting problem
to the word problem over the fixed alphabet `Alpha ℕ Sym2`, so the word problem is synthetically
halting-hard there. Its systems have non-empty left sides (`SemiThue.synthPosFromHalt`), and on such
systems the word problem is a functor on synchronizing codes (`AlphabetLift.lean`), so it is
synthetically halting-hard over every alphabet with two distinct letters
(`SemiThue.synthPosFromHaltOver`). `posToWord` returns to the plain word problem
(`SemiThue.synthFromHaltOver`, `SemiThue.synthFromHaltBool`). The machine-level statements are in
`MachineLevel.lean` and `AlphabetLift.lean`.

## References

* E. L. Post, *Recursive unsolvability of a problem of Thue* (1947)
* A. A. Markov, *On the impossibility of certain algorithms in the theory of associative systems*
  (1947)
-/

namespace DiagonaLean.SemiThue.Reduction

open DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Codes DiagonaLean.Synthetic.Definitions

variable {α : Type}

/-- The former name of `SemiThue.synthFromHalt`. -/
@[deprecated DiagonaLean.SemiThue.synthFromHalt (since := "2026-11-23")]
abbrev undecidableSemiThue := @DiagonaLean.SemiThue.synthFromHalt

/-- **The word problem for systems with non-empty left sides over every alphabet `α` with two
distinct letters is synthetically halting-hard**: the lifting of
`Foundations.Codes.CodeFunctor.undecidableOf`.
-/
def _root_.DiagonaLean.SemiThue.synthPosFromHaltOver (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DecisionProblemPos α) := by
  code_lift semiThueFunctor from SemiThue.synthPosFromHalt

/-- The former name of `SemiThue.synthPosFromHaltOver`. -/
@[deprecated DiagonaLean.SemiThue.synthPosFromHaltOver (since := "2026-11-23")]
abbrev undecidableSemiThuePosOf := @DiagonaLean.SemiThue.synthPosFromHaltOver

/-- **The word problem for string rewriting systems is synthetically halting-hard over any alphabet
`α` with two
distinct letters `b0`, `b1`.** -/
def _root_.DiagonaLean.SemiThue.synthFromHaltOver (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DecisionProblem α) := by
  synth_reduce_from (SemiThue.synthPosFromHaltOver b0 b1 hne) with (posToWord b0)
    using (posToWord_spec b0)

/-- The former name of `SemiThue.synthFromHaltOver`. -/
@[deprecated DiagonaLean.SemiThue.synthFromHaltOver (since := "2026-11-23")]
abbrev undecidableSemiThueOf := @DiagonaLean.SemiThue.synthFromHaltOver

/-- **The word problem for string rewriting systems over `Bool` is synthetically halting-hard.** -/
def _root_.DiagonaLean.SemiThue.synthFromHaltBool : SynthHaltReduction (@DecisionProblem Bool) :=
  SemiThue.synthFromHaltOver false true Bool.false_ne_true

/-- The former name of `SemiThue.synthFromHaltBool`. -/
@[deprecated DiagonaLean.SemiThue.synthFromHaltBool (since := "2026-11-23")]
abbrev undecidableSemiThueBool := @DiagonaLean.SemiThue.synthFromHaltBool

end DiagonaLean.SemiThue.Reduction
