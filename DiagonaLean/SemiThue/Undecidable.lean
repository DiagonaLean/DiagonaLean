/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.SemiThue.AlphabetLift

@[expose] public section

/-! # Undecidability of the word problem for string rewriting systems

`haltReducesSemiThue` (`Reductions/Halt_to_SemiThue.lean`) many-one reduces the halting problem to
the word problem over the fixed alphabet `Alpha ℕ Sym2`, so the word problem is synthetically
halting-hard there (`undecidableSemiThue`). Its systems have non-empty left sides
(`haltReducesSemiThuePos`), and on such systems the word problem is a functor on synchronizing codes
(`AlphabetLift.lean`), so it is synthetically halting-hard over every alphabet with two distinct
letters (`undecidableSemiThuePosOf`). `posReduces` returns to the plain word problem
(`undecidableSemiThueOf`, `undecidableSemiThueBool`). The machine-level statements are in
`MachineLevel.lean` and `AlphabetLift.lean`.

## References

* E. L. Post, *Recursive unsolvability of a problem of Thue* (1947)
* A. A. Markov, *On the impossibility of certain algorithms in the theory of associative systems*
  (1947)
-/

namespace DiagonaLean.SemiThue.Reduction

open DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Codes DiagonaLean.Synthetic.Definitions

variable {α : Type}

/-- **The word problem for string rewriting systems is synthetically halting-hard**, over
`Alpha ℕ Sym2`. -/ def undecidableSemiThue : SynthHaltReduction (@DecisionProblem (Alpha ℕ
Foundations.Computability.Normalize.Sym2)) := haltReducesSemiThue

/-- **The word problem for systems with non-empty left sides over every alphabet `α` with two
distinct letters is synthetically halting-hard**: the lifting of
`Foundations.Codes.CodeFunctor.undecidableOf`.
-/
def undecidableSemiThuePosOf (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DecisionProblemPos α) := by
  code_lift semiThueFunctor from haltReducesSemiThuePos

/-- **The word problem for string rewriting systems is synthetically halting-hard over any alphabet
`α` with two
distinct letters `b0`, `b1`.** -/
def undecidableSemiThueOf (b0 b1 : α) (hne : b0 ≠ b1) : SynthHaltReduction (@DecisionProblem α) :=
  SynthHaltReduction.comp (undecidableSemiThuePosOf b0 b1 hne) (posReduces b0)

/-- **The word problem for string rewriting systems over `Bool` is synthetically halting-hard.** -/
def undecidableSemiThueBool : SynthHaltReduction (@DecisionProblem Bool) :=
  undecidableSemiThueOf false true Bool.false_ne_true

end DiagonaLean.SemiThue.Reduction
