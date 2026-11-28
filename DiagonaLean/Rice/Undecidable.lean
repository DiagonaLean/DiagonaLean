/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kshitij Salunke, Aalok Thakkar, Claude Opus
-/

import Mathlib.Computability.Halting
import DiagonaLean.Rice.Reductions.Halt_to_Rice
import DiagonaLean.Foundations.Computability.Undecidable

@[expose] public section

/-! # Rice's theorem

If `C` is non-trivial (`IsNontrivial`), then `RiceProblem C` is undecidable
(`Rice.not_computablePred`, from Mathlib's `ComputablePred.rice`). So no machine decides it, under
any computable encoding of programs (`Rice.not_machineDecidable`, through
`not_machineDecidable_of_not_computablePred`). The synthetic results are in `SynthHardness.lean`.

## References

* H. G. Rice, *Classes of recursively enumerable sets and their decision problems* (1953)
-/

namespace DiagonaLean.Rice.Reduction

open Nat.Partrec DiagonaLean.Synthetic.Definitions
  DiagonaLean.Foundations.Computability

/-- **Rice's theorem.** If `C` is non-trivial, then `RiceProblem C` is undecidable: it is not a
computable predicate. -/
theorem _root_.DiagonaLean.Rice.not_computablePred {C : Set (ℕ →. ℕ)} (h : IsNontrivial C) :
    Undecidable (RiceProblem C) := fun hc => by
  obtain ⟨⟨c, hc₁⟩, d, hd⟩ := h
  exact hd (ComputablePred.rice C hc (Code.exists_code.2 ⟨c, rfl⟩) (Code.exists_code.2 ⟨d, rfl⟩)
    hc₁)

/-- **No machine decides Rice's problem.** If `C` is non-trivial, no `SingleTapeTM Bool` decides
`RiceProblem C` under a computable encoding `enc` of programs, such as `encUnary`. -/
theorem _root_.DiagonaLean.Rice.not_machineDecidable {C : Set (ℕ →. ℕ)} (h : IsNontrivial C)
    {enc : Code → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc (RiceProblem C) :=
  not_machineDecidable_of_not_computablePred henc (DiagonaLean.Rice.not_computablePred h)

end DiagonaLean.Rice.Reduction
