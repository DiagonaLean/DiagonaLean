/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.SemiThue.Reductions.Halt_to_SemiThue
import DiagonaLean.SemiThue.AlphabetLift
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # The word problem for string rewriting systems is synthetically halting-hard

`haltToSemiThue` (`Reductions/Halt_to_SemiThue.lean`) sends a machine and an input to a system and
a start word over `Alpha ℕ Sym2` such that the machine halts iff the start word rewrites to the
empty word, `u ↠[R] []` (`halt_reducesto_semiThue_spec`). So the word problem `WordProblem R u v` is
synthetically halting-hard over `Alpha ℕ Sym2` (`SemiThue.synthFromHalt`), and so is its
restriction `PosWordProblem` to systems with non-empty left sides (`SemiThue.synthPosFromHalt`).
On such systems the word problem is a functor on synchronizing codes (`semiThueFunctor`,
`AlphabetLift.lean`), which moves it to every alphabet with two distinct letters
(`SemiThue.synthPosFromHaltOver`); `posToWord` returns to the plain word problem
(`SemiThue.synthFromHaltOver`, `SemiThue.synthFromHaltBool`). The undecidability results are in
`Undecidable.lean`.

## Main definitions

* `SemiThue.synthFromHalt`, `SemiThue.synthPosFromHalt`: over `Alpha ℕ Sym2`.
* `SemiThue.synthPosFromHaltOver`, `SemiThue.synthFromHaltOver`, `SemiThue.synthFromHaltBool`:
  over every alphabet with two distinct letters.

## References

* E. L. Post, *Recursive unsolvability of a problem of Thue* (1947)
* A. A. Markov, *On the impossibility of certain algorithms in the theory of associative systems*
  (1947)
-/

namespace DiagonaLean.SemiThue.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Halt
  DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Rewriting
  DiagonaLean.Foundations.Computability.Normalize
  DiagonaLean.Synthetic.Definitions Relation

/-- **The word problem for string rewriting systems is synthetically halting-hard**, over
`Alpha ℕ Sym2`. The halting problem many-one reduces to the word problem for string rewriting
systems over `Alpha ℕ Sym2`, through `haltToSemiThue`. -/
def _root_.DiagonaLean.SemiThue.synthFromHalt : HaltProblem ⪯_s @DecisionProblem (Alpha ℕ Sym2) :=
  ⟨haltToSemiThue, halt_reducesto_semiThue_spec⟩

/-- **The word problem for systems with non-empty left sides is synthetically halting-hard**, over
`Alpha ℕ Sym2`, through `haltToSemiThue`, whose systems have non-empty left sides
(`haltToSemiThue_lhs_ne`). -/
def _root_.DiagonaLean.SemiThue.synthPosFromHalt :
    HaltProblem ⪯_s @DecisionProblemPos (Alpha ℕ Sym2) :=
  ⟨haltToSemiThue, halt_reducesto_semiThuePos_spec⟩

end DiagonaLean.SemiThue.Reduction

namespace DiagonaLean.SemiThue.Reduction

open DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Codes DiagonaLean.Synthetic.Definitions

variable {α : Type}

/-- **The word problem for systems with non-empty left sides is synthetically halting-hard over
every alphabet `α` with two distinct letters `b0`, `b1`**: `SemiThue.synthPosFromHalt`, lifted along
`semiThueFunctor` (`Foundations.Codes.CodeFunctor.undecidableOf`). -/
def _root_.DiagonaLean.SemiThue.synthPosFromHaltOver (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DecisionProblemPos α) := by
  code_lift semiThueFunctor from SemiThue.synthPosFromHalt

/-- **The word problem for string rewriting systems is synthetically halting-hard over any alphabet
`α` with two distinct letters `b0`, `b1`**: `SemiThue.synthPosFromHaltOver`, then `posToWord b0`. -/
def _root_.DiagonaLean.SemiThue.synthFromHaltOver (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DecisionProblem α) := by
  synth_reduce_from (SemiThue.synthPosFromHaltOver b0 b1 hne) with (posToWord b0)
    using (posToWord_spec b0)

/-- **The word problem for string rewriting systems over `Bool` is synthetically halting-hard.** -/
def _root_.DiagonaLean.SemiThue.synthFromHaltBool : SynthHaltReduction (@DecisionProblem Bool) :=
  SemiThue.synthFromHaltOver false true Bool.false_ne_true

end DiagonaLean.SemiThue.Reduction
