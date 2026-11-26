/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.BetaConv.Undecidable
import DiagonaLean.Foundations.Computability.CanonRace
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # β-conversion is halting-hard

The argument of `SKIConv/Hardness.lean`, for the λ-instances `linst U C n` of
`Foundations/LambdaCalculus/Race.lean` (the translations of the SKI instances). On a canonical
instance `x`, `canonRed U C x` is the λ-instance of the race program `C` on the code of
`dataCanon x`, against `tr FF`. It is primitive recursive through the code `tc`
(`primrec_iff_tc`, `tc_linst_prim`), and Smullyan's argument on canonical instances
(`ProofRace.haltCanon_iff`) makes it a reduction, so `BetaConv.fromHaltWith U C …` is a proved
halting reduction given the universal term `U` and the race program `C`.

The constants are only known to exist, so halting-hardness, a proposition, obtains them in its proof
(`BetaConv.haltHard`). From it, β-conversion is not a computable predicate
(`BetaConv.not_computablePred`), and no machine decides it under any computable encoding
(`BetaConv.not_machineDecidable`). `Undecidable.lean` reaches the two negative statements through a
machine-level race and the binary encoding `encBeta`.

## References

* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.BetaConv

open Cslib SKI LambdaCalculus.LocallyNameless.Untyped Nat.Partrec
  DiagonaLean.Foundations.LambdaCalculus DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- The λ-instance of a program on an input is primitive recursive in the input. -/
theorem linst_primrec (U : SKI) (C : Code) : Primrec (linst U C) := by
  have h : Primrec fun n : ℕ => tc (linst U (C, n).1 (C, n).2) :=
    (tc_linst_prim U).comp ((Primrec.const C).pair Primrec.id)
  -- reduce the projections first: unification would otherwise unfold the closed codes
  dsimp only at h
  exact primrec_iff_tc.2 h

/-- **The reduction from canonical instances.** The λ-instance of the race program `C` on the
code of the data of `x`, against `tr FF`. -/
def canonRed (U : SKI) (C : Code) (x : CanonTM × List Bool) : Term ℕ × Term ℕ :=
  (linst U C (Encodable.encode (dataCanon x)), tr FF)

/-- `canonRed U C` is primitive recursive. -/
theorem canonRed_primrec (U : SKI) (C : Code) : Primrec (canonRed U C) :=
  ((linst_primrec U C).comp (Primrec.encode.comp dataCanon_prim)).pair (Primrec.const _)

/-- `canonRed U C` reduces `HaltCanon` to β-conversion. -/
theorem haltCanon_reducesto_betaConv_spec {u : Code} {U : SKI} {C : Code}
    (hu : Foundations.CombinatoryLogic.IsUniversal u) (hU : Computes U u.eval)
    (hC : RaceProg U C) : HaltCanon ⪯_s[canonRed U C] BetaConvProblem :=
  ProofRace.haltCanon_iff (Q := fun n => Foundations.LambdaCalculus.BetaConv (linst U C n) (tr FF))
    hC (fun _ => betaConv_iff_chk U C _) (fun _ h => betaConv_linst_of_one hu hU h)
    (fun _ h => not_betaConv_linst_of_zero hu hU h)

/-- **A proved halting reduction to β-conversion**, given the universal term `U` and the race
program `C`. -/
def fromHaltWith {u : Code} (U : SKI) (C : Code) (hu : Foundations.CombinatoryLogic.IsUniversal u)
    (hU : Computes U u.eval) (hC : RaceProg U C) : HaltReduction BetaConvProblem :=
  ⟨canonRed U C, (canonRed_primrec U C).to_comp, haltCanon_reducesto_betaConv_spec hu hU hC⟩

/-- **β-conversion is halting-hard.** The universal code and the race program exist
(`exists_isUniversal`, `exists_raceProg`). -/
theorem haltHard : HaltHard BetaConvProblem := by
  obtain ⟨u, hu⟩ := Foundations.CombinatoryLogic.exists_isUniversal
  obtain ⟨C, hC⟩ := exists_raceProg u.toSKI
  exact ⟨fromHaltWith u.toSKI C hu (Code.toSKI_correct u) hC⟩

/-- **β-conversion is not a computable predicate.** -/
theorem not_computablePred : ¬ ComputablePred BetaConvProblem :=
  haltHard.not_computablePred

/-- **No Turing machine decides β-conversion under any computable encoding.** -/
theorem not_machineDecidable {enc : Term ℕ × Term ℕ → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc BetaConvProblem :=
  haltHard.not_machineDecidable henc

/-- β-conversion is a halting-hard source for `hard_reduce_from`. -/
instance : HaltHardFact BetaConvProblem := ⟨haltHard⟩

end DiagonaLean.BetaConv
