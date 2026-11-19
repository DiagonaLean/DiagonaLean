/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.BetaConv.Reductions.Halt_to_BetaConv

@[expose] public section

/-! # Undecidability of β-conversion

β-conversion of λ-terms is `Undecidable` (`undecidableBetaConv`), given the reduction's constants:
a universal code `u` and the race program `C` for its SKI term `u.toSKI`, from the recursion
theorem. They are only known to exist, so `C` and the proofs `hu : IsUniversal u` and
`hC : RaceProg u.toSKI C` are arguments, and `u` is implicit. No Turing machine decides it under the
encoding of a pair of terms as the binary digits of the pair of their codes
(`not_machineDecidable_betaConv`); the encoding is injective (`encBeta_injective`) and follows
`encNat` in `KAComm/KleeneAlgebra/Race.lean`. It separates the computably inseparable
pair `SelfOut true`, `SelfOut false`, so no machine decides it on the instances `sepRed U c M` given
the code of `M` (`not_machineDecidable_betaConv_sepRed`).

## References

* [A. Church, *An Unsolvable Problem of Elementary Number Theory*][Church1936]
  (for the λI-calculus)
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.BetaConv.Reduction

open Cslib SKI LambdaCalculus.LocallyNameless.Untyped Nat.Partrec
  DiagonaLean.Foundations.LambdaCalculus DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Inseparable

/-- **β-conversion of λ-terms is `Undecidable`**, given a universal code `u`
(`Foundations.CombinatoryLogic.exists_isUniversal`) and the race program `C` for `u.toSKI`
(`exists_raceProg`). These finite constants are only known to exist, so they are arguments rather
than computed here. The statement without them is `not_machineDecidable_betaConv`. -/
def undecidableBetaConv {u : Code} (C : Code) (hu : Foundations.CombinatoryLogic.IsUniversal u)
    (hC : RaceProg u.toSKI C) : Undecidable BetaConvProblem :=
  haltReducesBetaConv u.toSKI C hu (Code.toSKI_correct u) hC

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
