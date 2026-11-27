/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.BetaConv.Reductions.Halt_to_BetaConv
import DiagonaLean.Foundations.LambdaCalculus.Primcodable
import DiagonaLean.Foundations.Computability.MachineBridge
import DiagonaLean.BetaConv.Reductions.HaltCanon_to_BetaConv
import DiagonaLean.Foundations.Computability.HaltResults
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # Undecidability of β-conversion

On a canonical instance, `canonRed U C` (`Reductions/HaltCanon_to_BetaConv.lean`) builds the
λ-instance of the race program `C`, primitive recursively, so `BetaConv.fromHaltWith U C …` is a
proved halting reduction, given the universal term `U` and the race program `C`. The constants are
only known to exist, so halting-hardness, a proposition, obtains them in its proof
(`BetaConv.haltHard`). From it, β-conversion is undecidable (`BetaConv.not_computablePred`), and no
machine decides it under any computable encoding (`BetaConv.not_machineDecidable`).

The same two statements are reached independently through a machine-level race: no Turing machine
decides it under the encoding of a pair of terms as the binary digits of the pair of their codes
(`not_machineDecidable_betaConv`); the encoding is injective (`encBeta_injective`) and follows
`encNat` in `KAComm/KleeneAlgebra/Race.lean`. It separates the computably inseparable pair
`SelfOut true`, `SelfOut false`, so no machine decides it on the instances `sepRed U c M` given the
code of `M` (`not_machineDecidable_betaConv_sepRed`). The synthetic results are in
`SynthHardness.lean`.

## References

* [A. Church, *An Unsolvable Problem of Elementary Number Theory*][Church1936]
(for the λI-calculus)
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.BetaConv.Reduction

open Cslib SKI LambdaCalculus.LocallyNameless.Untyped Nat.Partrec
  DiagonaLean.Foundations.LambdaCalculus DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Inseparable

/-- A pair of λ-terms, as the binary digits of the pair of their codes. -/
def encBeta (i : Term ℕ × Term ℕ) : List Bool :=
  bitsPair (tc i.1) (tc i.2)

/-- `encBeta` is injective. -/
theorem encBeta_injective : Function.Injective encBeta := fun i j h => by
  obtain ⟨h₁, h₂⟩ := bitsPair_injective h
  exact Prod.ext (tc_injective h₁) (tc_injective h₂)

/-- **No Turing machine decides β-conversion of λ-terms.** -/
theorem not_machineDecidable_betaConv : ¬ MachineDecidable encBeta BetaConvProblem := by
  obtain ⟨u, hu⟩ := Foundations.CombinatoryLogic.exists_isUniversal
  have henc : ∀ c n, encBeta (linst u.toSKI c n, tr FF) =
      bitsOf (Nat.pair (instCode u.toSKI c n).1 (instCode u.toSKI c n).2) := fun _ _ => by
    simp only [encBeta, instCode, bitsPair]
  have hQ : ∀ c n, BetaConvProblem (linst u.toSKI c n, tr FF) ↔
      ∃ k, chk k (instCode u.toSKI c n) = true := fun _ _ => betaConv_iff_chk _ _ _
  have pos : ∀ (c : Code) n, 1 ∈ c.eval n → BetaConvProblem (linst u.toSKI c n, tr FF) :=
    fun _ _ h => betaConv_linst_of_one hu (Code.toSKI_correct u) h
  have neg : ∀ (c : Code) n, 0 ∈ c.eval n → ¬ BetaConvProblem (linst u.toSKI c n, tr FF) :=
    fun _ _ h => not_betaConv_linst_of_zero hu (Code.toSKI_correct u) h
  exact ProofRace.not_machineDecidable_of_race chk_prim (instCode_prim u.toSKI)
    (fun c n => (linst u.toSKI c n, tr FF)) henc hQ pos neg

/-- **On the instances `sepRed`, no machine decides β-conversion** given the code of the machine:
they separate the computably inseparable pair `SelfOut true`, `SelfOut false`. -/
theorem not_machineDecidable_betaConv_sepRed :
    ∃ (U : SKI) (c : Code),
      ¬ MachineDecidable encodeBoolTM fun M => BetaConvProblem (sepRed U c M) := by
  obtain ⟨u, hu⟩ := Foundations.CombinatoryLogic.exists_isUniversal
  obtain ⟨c, hc⟩ := exists_isReader
  exact ⟨u.toSKI, c,
    selfOut_inseparable (sepRed_separates u.toSKI c hu (Code.toSKI_correct u) hc)⟩

end DiagonaLean.BetaConv.Reduction

namespace DiagonaLean.BetaConv

open Cslib SKI LambdaCalculus.LocallyNameless.Untyped Nat.Partrec
  DiagonaLean.Foundations.LambdaCalculus DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- **A proved halting reduction to β-conversion**, given the universal term `U` and the race
program `C`. -/
def fromHaltWith {u : Code} (U : SKI) (C : Code) (hu : Foundations.CombinatoryLogic.IsUniversal u)
    (hU : Computes U u.eval) (hC : RaceProg U C) : HaltReduction BetaConvProblem :=
  ⟨canonRed U C, (canonRed_primrec U C).to_comp, haltCanon_reducesto_betaConv_spec hu hU hC⟩

-- Halting-hardness and its consequences: the universal code and the race program exist
-- (`exists_isUniversal`, `exists_raceProg`), so the proof obtains them, and only the existence
-- of a reduction is stated.
halt_results BetaConvProblem from
  Foundations.CombinatoryLogic.exists_isUniversal.elim fun u hu =>
    (exists_raceProg u.toSKI).elim fun C hC =>
      ⟨fromHaltWith u.toSKI C hu (Code.toSKI_correct u) hC⟩

/-- β-conversion is a halting-hard source for `hard_reduce_from`. -/
instance : HaltHardFact BetaConvProblem := ⟨haltHard⟩

end DiagonaLean.BetaConv
