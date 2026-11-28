/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.SKIConv.Reductions.Halt_to_SKIConv
import DiagonaLean.Foundations.CombinatoryLogic.Primcodable
import DiagonaLean.Foundations.Computability.MachineBridge
import DiagonaLean.SKIConv.Reductions.HaltCanon_to_SKIConv
import DiagonaLean.Foundations.Computability.HaltResults
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # Undecidability of SKI convertibility

On a canonical instance, `canonRed U C` (`Reductions/HaltCanon_to_SKIConv.lean`) builds the
instance of the race program `C`, primitive recursively, so `SKIConv.fromHaltWith U C …` is a
proved halting reduction, given the universal term `U` and the race program `C`. Those constants
are only known to exist (a universal code, and the recursion theorem), so the reduction takes them
as arguments, and halting-hardness, which is a proposition, obtains them in its proof
(`SKIConv.haltHard`). From it, SKI convertibility is undecidable (`SKIConv.not_computablePred`),
and no machine decides it under any computable encoding (`SKIConv.not_machineDecidable`).

The same two statements are reached independently through a machine-level race: no Turing machine
decides it under the encoding of a pair of terms as the binary digits of the pair of their codes
(`not_machineDecidable_skiConv`); the encoding is injective (`encSKI_injective`) and follows
`encNat` in `KAComm/KleeneAlgebra/Race.lean`. It separates the computably inseparable pair
`SelfOut true`, `SelfOut false`, so no machine decides it on the instances `sepRed U c M` given the
code of `M` (`not_machineDecidable_skiConv_sepRed`). The synthetic results are in
`SynthHardness.lean`.

## References

* [J. R. Hindley, J. P. Seldin,
*Lambda-Calculus and Combinators: An Introduction*][HindleySeldin2008]
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.SKIConv.Reduction

open Cslib SKI Nat.Partrec DiagonaLean.Foundations.CombinatoryLogic
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Inseparable

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

namespace DiagonaLean.SKIConv

open Cslib SKI Nat.Partrec DiagonaLean.Foundations.CombinatoryLogic
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions

/-- **A proved halting reduction to SKI convertibility**, given the universal term `U` and the race
program `C`. -/
def fromHaltWith {u : Code} (U : SKI) (C : Code) (hu : IsUniversal u) (hU : Computes U u.eval)
    (hC : RaceProg U C) : HaltReduction SKIConvProblem :=
  ⟨canonRed U C, (canonRed_primrec U C).to_comp, haltCanon_reducesto_skiConv_spec hu hU hC⟩

-- Halting-hardness and its consequences: the universal code and the race program exist
-- (`exists_isUniversal`, `exists_raceProg`), so the proof obtains them, and only the existence
-- of a reduction is stated.
halt_results SKIConvProblem from
  exists_isUniversal.elim fun u hu => (exists_raceProg u.toSKI).elim fun C hC =>
    ⟨fromHaltWith u.toSKI C hu (Code.toSKI_correct u) hC⟩

end DiagonaLean.SKIConv
