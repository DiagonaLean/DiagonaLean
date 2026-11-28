/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.BetaConv.Reductions.Halt_to_BetaConv

@[expose] public section

/-! # β-conversion is synthetically halting-hard

`reduction U C` (`Reductions/Halt_to_BetaConv.lean`) many-one reduces the halting problem to
β-conversion of λ-terms (`BetaConv.synthFromHaltWith`), given a universal term `U` and a race
program `C`. With the universal code `u` and the race program `C` for its SKI term `u.toSKI`, from
the recursion theorem, it is `BetaConv.synthFromHalt`. They are only known to exist, so `C` and the
proofs `hu : IsUniversal u` and `hC : RaceProg u.toSKI C` are arguments, and `u` is implicit. The
undecidability results are in `Undecidable.lean`.

## References

* [A. Church, *An Unsolvable Problem of Elementary Number Theory*][Church1936]
(for the λI-calculus)
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.BetaConv.Reduction

open Cslib SKI LambdaCalculus.LocallyNameless.Untyped Nat.Partrec
  DiagonaLean.Foundations.LambdaCalculus DiagonaLean.Foundations.Computability DiagonaLean.Halt
  DiagonaLean.Halt.Encoding DiagonaLean.Halt.Inseparable DiagonaLean.Synthetic.Definitions

/-- `HaltProblem` many-one reduces to β-conversion. -/
def _root_.DiagonaLean.BetaConv.synthFromHaltWith {u : Code} (U : SKI) (C : Code)
    (hu : Foundations.CombinatoryLogic.IsUniversal u) (hU : Computes U u.eval)
    (hC : RaceProg U C) : HaltProblem ⪯_s BetaConvProblem :=
  ⟨reduction U C, halt_reducesto_betaConv_spec hu hU hC⟩

end DiagonaLean.BetaConv.Reduction

namespace DiagonaLean.BetaConv.Reduction

open Cslib SKI LambdaCalculus.LocallyNameless.Untyped Nat.Partrec
  DiagonaLean.Foundations.LambdaCalculus DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Inseparable

/-- **β-conversion of λ-terms is synthetically halting-hard**, given a universal code `u`
(`Foundations.CombinatoryLogic.exists_isUniversal`) and the race program `C` for `u.toSKI`
(`exists_raceProg`). These finite constants are only known to exist, so they are arguments rather
than computed here. The statement without them is `not_machineDecidable_betaConv`. -/
def _root_.DiagonaLean.BetaConv.synthFromHalt {u : Code} (C : Code)
    (hu : Foundations.CombinatoryLogic.IsUniversal u) (hC : RaceProg u.toSKI C) :
    SynthHaltReduction BetaConvProblem :=
  BetaConv.synthFromHaltWith u.toSKI C hu (Code.toSKI_correct u) hC

end DiagonaLean.BetaConv.Reduction
