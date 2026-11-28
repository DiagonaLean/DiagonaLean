/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kshitij Salunke, Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Rice.Reductions.Halt_to_Rice

@[expose] public section

/-! # Rice's problem is synthetically halting-hard

The synthetic results split on whether `C` contains the nowhere-defined function, which is itself
computed by a program. If it does not and `cT` computes a function in `C`, then `RiceProblem C` is
synthetically halting-hard (`Rice.synthFromHalt`, through `reduction` of
`Reductions/Halt_to_Rice.lean`). If it does and `cF` computes a function not in `C`, then the
complement of `RiceProblem C` is synthetically halting-hard (`Rice.synthComplFromHalt`). So every
non-trivial `C` is covered by one of the two. A single `SynthHaltReduction` result is not possible:
which case holds cannot be computed, and when `C` contains the nowhere-defined function,
`RiceProblem C` may be co-r.e. (for `C = {fun _ => Part.none}`), so that `HaltProblem` does not
reduce to it.

Each result takes a waiter program `w` (`exists_isWaiter`) and the witness code as arguments,
since they are only known to exist. The undecidability results are in `Undecidable.lean`.

## References

* H. G. Rice, *Classes of recursively enumerable sets and their decision problems* (1953)
-/

namespace DiagonaLean.Rice.Reduction

open Nat.Partrec DiagonaLean.Foundations.Computability DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions

/-- **Rice's problem is synthetically halting-hard.** If `cT` computes a function in `C` and the
nowhere-defined function is not in `C`, then `RiceProblem C` is synthetically halting-hard, given a
waiter program `w` (`exists_isWaiter`). `HaltProblem` many-one reduces to `RiceProblem C`. -/
def _root_.DiagonaLean.Rice.synthFromHalt {C : Set (ℕ →. ℕ)} (w cT : Code) (hw : IsWaiter w)
    (hT : cT.eval ∈ C) (hbot : (fun _ => Part.none : ℕ →. ℕ) ∉ C) :
    HaltProblem ⪯_s RiceProblem C :=
  ⟨reduction w cT, halt_reducesto_rice_spec hw hT hbot⟩

/-- **The complement of Rice's problem is synthetically halting-hard.** If `cF` computes a function
not in `C` and the nowhere-defined function is in `C`, then the complement of `RiceProblem C` is
synthetically halting-hard, given a waiter program `w` (`exists_isWaiter`). -/
def _root_.DiagonaLean.Rice.synthComplFromHalt {C : Set (ℕ →. ℕ)} (w cF : Code) (hw : IsWaiter w)
    (hF : cF.eval ∉ C) (hbot : (fun _ => Part.none : ℕ →. ℕ) ∈ C) :
    SynthHaltReduction fun c => ¬ RiceProblem C c :=
  Rice.synthFromHalt (C := Cᶜ) w cF hw hF (fun h => h hbot)

end DiagonaLean.Rice.Reduction
