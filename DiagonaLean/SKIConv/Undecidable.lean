/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.SKIConv.Reductions.Halt_to_SKIConv

@[expose] public section

/-! # Undecidability of SKI convertibility

Convertibility of SKI terms is `Undecidable` (`undecidable_skiConv`). The reduction's constants
are the SKI translation of a universal code (`Nat.Partrec.Code.toSKI`) and the race program from
the recursion theorem. No Turing machine decides it under the encoding of a pair of terms as the
binary digits of the pair of their codes (`not_machineDecidable_skiConv`); the encoding is
injective (`encSKI_injective`) and follows `encNat` in `Foundations/KleeneAlgebra/Race.lean`. It
separates the computably inseparable pair `SelfOut true`, `SelfOut false` (`skiConv_separated`).

## References

* [J. R. Hindley, J. P. Seldin,
  *Lambda-Calculus and Combinators: An Introduction*][HindleySeldin2008]
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.SKIConv.Reduction

open Cslib SKI Nat.Partrec DiagonaLean.Foundations.CombinatoryLogic
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation

/-- **Convertibility of SKI terms is `Undecidable`.** -/
theorem undecidable_skiConv : Undecidable SKIConvProblem := by
  obtain ⟨u, hu⟩ := exists_isUniversal
  obtain ⟨C, hC⟩ := exists_raceProg u.toSKI
  exact ⟨haltReducesSKIConv u.toSKI C hu (Code.toSKI_correct u) hC⟩

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

/-- `sepRed` separates the inseparable pair by SKI convertibility. -/
theorem skiConv_separated : InsepUndecidable SKIConvProblem := by
  obtain ⟨u, hu⟩ := exists_isUniversal
  obtain ⟨c, hc⟩ := exists_isReader
  exact ⟨sepReducesSKIConv u.toSKI c hu (Code.toSKI_correct u) hc⟩

end DiagonaLean.SKIConv.Reduction
