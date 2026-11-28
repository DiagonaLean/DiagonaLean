/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.BetaConv.Reductions.Halt_to_BetaConv
import DiagonaLean.Foundations.LambdaCalculus.Primcodable
import DiagonaLean.Foundations.Computability.CanonRace
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # From the halting problem on canonical machines to β-conversion

The argument of `SKIConv/Reductions/HaltCanon_to_SKIConv.lean`, for the λ-instances `linst U C n`
of `Foundations/LambdaCalculus/Race.lean` (the translations of the SKI instances). On a canonical
instance `x`, `canonRed U C x` is the λ-instance of the race program `C` on the code of
`dataCanon x`, against `tr FF`. It is primitive recursive through the code `tc`
(`primrec_iff_tc`, `tc_linst_prim`), and Smullyan's argument on canonical instances
(`ProofRace.haltCanon_iff`) makes it a reduction (`haltCanon_reducesto_betaConv_spec`). The
halting reduction `BetaConv.fromHaltWith` built from it is in `Undecidable.lean`.

## Main statements

* `canonRed`, `canonRed_primrec`, `haltCanon_reducesto_betaConv_spec`.

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
  ProofRace.haltCanon_iff (Q := fun n => Foundations.LambdaCalculus.Conv (linst U C n) (tr FF))
    hC (fun _ => betaConv_iff_chk U C _) (fun _ h => betaConv_linst_of_one hu hU h)
    (fun _ h => not_betaConv_linst_of_zero hu hU h)

end DiagonaLean.BetaConv
