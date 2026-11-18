/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.BetaConv.Reductions.Halt_to_BetaConv

@[expose] public section

/-! # Undecidability of β-conversion

β-conversion of λ-terms is `Undecidable` (`undecidable_betaConv`). The reduction's constants are
the SKI translation of a universal code (`Nat.Partrec.Code.toSKI`) and the race program from the
recursion theorem. No Turing machine decides it under the encoding of a pair of terms as the
binary digits of the pair of their codes (`not_machineDecidable_betaConv`); the encoding is
injective (`encBeta_injective`) and follows `encNat` in `Foundations/KleeneAlgebra/Race.lean`. It
separates the computably inseparable pair `SelfOut true`, `SelfOut false` (`betaConv_separated`).

## References

* [A. Church, *An Unsolvable Problem of Elementary Number Theory*][Church1936]
  (for the λI-calculus)
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.BetaConv.Reduction

open Cslib SKI LambdaCalculus.LocallyNameless.Untyped Nat.Partrec
  DiagonaLean.Foundations.LambdaCalculus DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

/-- **β-conversion of λ-terms is `Undecidable`.** -/
theorem undecidable_betaConv : Undecidable BetaConvProblem := by
  obtain ⟨u, hu⟩ := Foundations.CombinatoryLogic.exists_isUniversal
  obtain ⟨C, hC⟩ := exists_raceProg u.toSKI
  exact ⟨haltReducesBetaConv u.toSKI C hu (Code.toSKI_correct u) hC⟩

/-- A pair of λ-terms, as the binary digits of the pair of their codes. -/
def encBeta (i : Term ℕ × Term ℕ) : List Bool := bitsPair (tc i.1) (tc i.2)

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

/-- `sepRed` separates the inseparable pair by β-conversion. -/
theorem betaConv_separated : InsepUndecidable BetaConvProblem := by
  obtain ⟨u, hu⟩ := Foundations.CombinatoryLogic.exists_isUniversal
  obtain ⟨c, hc⟩ := exists_isReader
  exact ⟨sepReducesBetaConv u.toSKI c hu (Code.toSKI_correct u) hc⟩

end DiagonaLean.BetaConv.Reduction
