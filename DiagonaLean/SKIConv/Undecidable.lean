/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.SKIConv.Reductions.Halt_to_SKIConv
import DiagonaLean.Foundations.CombinatoryLogic.Primcodable
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Undecidability of SKI convertibility

Convertibility of SKI terms is synthetically halting-hard (`SKIConv.synthFromHalt`), given the
reduction's constants: a universal code `u` and the race program `C` for its SKI term `u.toSKI`,
from the recursion theorem. They are only known to exist, so `C` and the proofs `hu : IsUniversal u`
and `hC : RaceProg u.toSKI C` are arguments, and `u` is implicit. No Turing machine decides it under
the encoding of a pair of terms as the binary digits of the pair of their codes
(`not_machineDecidable_skiConv`), so it is not a computable predicate (`not_computablePred_skiConv`)
and no machine decides it under any computable encoding
(`not_machineDecidable_skiConv_of_computable`); the encoding is injective (`encSKI_injective`) and
follows `encNat` in `KAComm/KleeneAlgebra/Race.lean`. It separates the computably inseparable pair
`SelfOut true`, `SelfOut false`, so no machine decides it on the instances `sepRed U c M` given the
code of `M` (`not_machineDecidable_skiConv_sepRed`).

## References

* [J. R. Hindley, J. P. Seldin,
  *Lambda-Calculus and Combinators: An Introduction*][HindleySeldin2008]
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.SKIConv.Reduction

open Cslib SKI Nat.Partrec DiagonaLean.Foundations.CombinatoryLogic
  DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Inseparable

/-- **Convertibility of SKI terms is synthetically halting-hard**, given a universal code `u`
(`exists_isUniversal`) and the race program `C` for `u.toSKI` (`exists_raceProg`). These finite
constants are only known to exist, so they are arguments rather than computed here. The statement
without them is `not_machineDecidable_skiConv`. -/
def _root_.DiagonaLean.SKIConv.synthFromHalt {u : Code} (C : Code) (hu : IsUniversal u)
    (hC : RaceProg u.toSKI C) : SynthHaltReduction SKIConvProblem :=
  SKIConv.synthFromHaltWith u.toSKI C hu (Code.toSKI_correct u) hC

/-- A pair of SKI terms, as the binary digits of the pair of their codes. -/
def encSKI (i : SKI × SKI) : List Bool := bitsPair (skc i.1) (skc i.2)

/-- `encSKI` is injective. -/
theorem encSKI_injective : Function.Injective encSKI := fun i j h => by
  obtain ⟨h₁, h₂⟩ := bitsPair_injective h
  exact Prod.ext (skc_injective h₁) (skc_injective h₂)

/-- **No Turing machine decides convertibility of SKI terms.** -/
theorem not_machineDecidable_skiConv : ¬ MachineDecidable encSKI SKIConvProblem := by
  obtain ⟨u, hu⟩ := exists_isUniversal
  exact ProofRace.not_machineDecidable_of_race chk_prim (instCode_prim u.toSKI)
    (fun c n => (inst u.toSKI c n, FF))
    (fun _ _ => by simp only [encSKI, instCode, bitsPair])
    (fun _ _ => conv_inst_iff_chk _ _ _)
    (fun _ _ h => conv_inst_of_one hu (Code.toSKI_correct u) h)
    (fun _ _ h => not_conv_inst_of_zero hu (Code.toSKI_correct u) h)

/-- **SKI convertibility is not a computable predicate.** `encSKI` writes the pair of codes `skc`
in binary, and `skc` has a primitive recursive decoder (`skcDec`), so a computable decision
procedure would give a machine deciding it under `encSKI` (`not_computablePred_of_bitsPair`). -/
theorem not_computablePred_skiConv : ¬ ComputablePred SKIConvProblem :=
  not_computablePred_of_bitsPair skc_primrec skcDec_primrec skcDec_skc not_machineDecidable_skiConv

/-- **No Turing machine decides SKI convertibility under any computable encoding.** -/
theorem not_machineDecidable_skiConv_of_computable {enc : SKI × SKI → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc SKIConvProblem :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_skiConv

/-- **On the instances `sepRed`, no machine decides SKI convertibility** given the code of the
machine: they separate the computably inseparable pair `SelfOut true`, `SelfOut false`. -/
theorem not_machineDecidable_skiConv_sepRed :
    ∃ (U : SKI) (c : Code),
      ¬ MachineDecidable encodeBoolTM fun M => SKIConvProblem (sepRed U c M) := by
  obtain ⟨u, hu⟩ := exists_isUniversal
  obtain ⟨c, hc⟩ := exists_isReader
  exact ⟨u.toSKI, c,
    selfOut_inseparable (sepRed_separates u.toSKI c hu (Code.toSKI_correct u) hc)⟩

end DiagonaLean.SKIConv.Reduction
