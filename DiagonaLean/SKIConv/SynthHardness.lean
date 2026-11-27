/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.SKIConv.Reductions.Halt_to_SKIConv

@[expose] public section

/-! # SKI convertibility is synthetically halting-hard

`reduction U C` (`Reductions/Halt_to_SKIConv.lean`) many-one reduces the halting problem to
convertibility of SKI terms (`SKIConv.synthFromHaltWith`), given a universal term `U` and a race
program `C`. With the universal code `u` and the race program `C` for its SKI term `u.toSKI`, from
the recursion theorem, it is `SKIConv.synthFromHalt`. They are only known to exist, so `C` and the
proofs `hu : IsUniversal u` and `hC : RaceProg u.toSKI C` are arguments, and `u` is implicit. The
undecidability results are in `Undecidable.lean`.

## References

* [J. R. Hindley, J. P. Seldin,
*Lambda-Calculus and Combinators: An Introduction*][HindleySeldin2008]
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.SKIConv.Reduction

open Cslib SKI Nat.Partrec DiagonaLean.Foundations.CombinatoryLogic
  DiagonaLean.Foundations.Computability DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Inseparable DiagonaLean.Synthetic.Definitions

/-- `HaltProblem` many-one reduces to SKI convertibility. -/
def _root_.DiagonaLean.SKIConv.synthFromHaltWith {u : Code} (U : SKI) (C : Code)
    (hu : IsUniversal u) (hU : Computes U u.eval) (hC : RaceProg U C) :
    HaltProblem ⪯_s SKIConvProblem :=
  ⟨reduction U C, halt_reducesto_skiConv_spec hu hU hC⟩

end DiagonaLean.SKIConv.Reduction

namespace DiagonaLean.SKIConv.Reduction

open Cslib SKI Nat.Partrec DiagonaLean.Foundations.CombinatoryLogic
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Inseparable

/-- **Convertibility of SKI terms is synthetically halting-hard**, given a universal code `u`
(`exists_isUniversal`) and the race program `C` for `u.toSKI` (`exists_raceProg`). These finite
constants are only known to exist, so they are arguments rather than computed here. The statement
without them is `not_machineDecidable_skiConv`. -/
def _root_.DiagonaLean.SKIConv.synthFromHalt {u : Code} (C : Code) (hu : IsUniversal u)
    (hC : RaceProg u.toSKI C) : SynthHaltReduction SKIConvProblem :=
  SKIConv.synthFromHaltWith u.toSKI C hu (Code.toSKI_correct u) hC

end DiagonaLean.SKIConv.Reduction
