/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kshitij Salunke, Aalok Thakkar, Claude Opus
-/

import Mathlib.Computability.Halting
import DiagonaLean.Rice.Reductions.Halt_to_Rice

@[expose] public section

/-! # Rice's theorem

If `C` is non-trivial (`IsNontrivial`), then `RiceProblem C` is not a computable predicate
(`not_computablePred_rice`, from Mathlib's `ComputablePred.rice`).

The undecidability results split on whether `C` contains the nowhere-defined function, which is
itself computed by a program. If it does not and `cT` computes a function in `C`, then
`RiceProblem C` is `Undecidable` (`undecidableRice`). If it does and `cF` computes a function not
in `C`, then the complement of `RiceProblem C` is `Undecidable` (`undecidableRiceCompl`). So every
non-trivial `C` is covered by one of the two. A single `Undecidable` result is not possible: which
case holds cannot be computed, and when `C` contains the nowhere-defined function, `RiceProblem C`
may be co-r.e. (for `C = {fun _ => Part.none}`), so that `HaltProblem` does not reduce to it.

Each result takes a waiter program `w` (`exists_isWaiter`) and the witness code as arguments,
since they are only known to exist.

## References

* H. G. Rice, *Classes of recursively enumerable sets and their decision problems* (1953)
-/

namespace DiagonaLean.Rice.Reduction

open Nat.Partrec DiagonaLean.Synthetic.Notation

/-- **Rice's theorem.** If `C` is non-trivial, then `RiceProblem C` is not a computable
predicate. -/
theorem not_computablePred_rice {C : Set (ℕ →. ℕ)} (h : IsNontrivial C) :
    ¬ ComputablePred (RiceProblem C) := fun hc => by
  obtain ⟨⟨c, hc₁⟩, d, hd⟩ := h
  exact hd (ComputablePred.rice C hc (Code.exists_code.2 ⟨c, rfl⟩) (Code.exists_code.2 ⟨d, rfl⟩)
    hc₁)

/-- **Rice's problem is `Undecidable`.** If `cT` computes a function in `C` and the
nowhere-defined function is not in `C`, then `RiceProblem C` is `Undecidable`, given a waiter
program `w` (`exists_isWaiter`). -/
def undecidableRice {C : Set (ℕ →. ℕ)} (w cT : Code) (hw : IsWaiter w) (hT : cT.eval ∈ C)
    (hbot : (fun _ => Part.none : ℕ →. ℕ) ∉ C) : Undecidable (RiceProblem C) :=
  haltReducesRice w cT hw hT hbot

/-- **The complement of Rice's problem is `Undecidable`.** If `cF` computes a function not in `C`
and the nowhere-defined function is in `C`, then the complement of `RiceProblem C` is
`Undecidable`, given a waiter program `w` (`exists_isWaiter`). -/
def undecidableRiceCompl {C : Set (ℕ →. ℕ)} (w cF : Code) (hw : IsWaiter w) (hF : cF.eval ∉ C)
    (hbot : (fun _ => Part.none : ℕ →. ℕ) ∈ C) : Undecidable fun c => ¬ RiceProblem C c :=
  haltReducesRice (C := Cᶜ) w cF hw hF (fun h => h hbot)

end DiagonaLean.Rice.Reduction
