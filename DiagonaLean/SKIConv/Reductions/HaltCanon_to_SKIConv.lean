/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.SKIConv.Reductions.Halt_to_SKIConv
import DiagonaLean.Foundations.CombinatoryLogic.Primcodable
import DiagonaLean.Foundations.Computability.CanonRace
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # From the halting problem on canonical machines to SKI convertibility

On a canonical instance `x`, the reduction `canonRed U C` builds the instance of the race program
`C` on the code of `dataCanon x`, against `FF`. It is primitive recursive (`canonRed_primrec`):
`dataCanon` is, and so is the instance `inst U C`, through the code `skc` (`primrec_iff_skc`).
Smullyan's argument on canonical instances (`ProofRace.haltCanon_iff`) makes it a reduction
(`haltCanon_reducesto_skiConv_spec`). The halting reduction `SKIConv.fromHaltWith` built from it is
in `Undecidable.lean`.

## Main statements

* `canonRed`, `canonRed_primrec`, `haltCanon_reducesto_skiConv_spec`.

## References

* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.SKIConv

open Cslib SKI Nat.Partrec DiagonaLean.Foundations.CombinatoryLogic
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions

/-- The instance of a program on an input is primitive recursive in the input. -/
theorem inst_primrec (U : SKI) (C : Code) : Primrec (inst U C) := by
  have h : Primrec fun n : ℕ => skc (inst U (C, n).1 (C, n).2) :=
    (skc_inst_prim U).comp ((Primrec.const C).pair Primrec.id)
  -- reduce the projections first: unification would otherwise unfold the closed codes
  dsimp only at h
  exact primrec_iff_skc.2 h

/-- **The reduction from canonical instances.** The instance of the race program `C` on the code
of the data of `x`, against `FF`. -/
def canonRed (U : SKI) (C : Code) (x : CanonTM × List Bool) : SKI × SKI :=
  (inst U C (Encodable.encode (dataCanon x)), FF)

/-- `canonRed U C` is primitive recursive. -/
theorem canonRed_primrec (U : SKI) (C : Code) : Primrec (canonRed U C) :=
  ((inst_primrec U C).comp (Primrec.encode.comp dataCanon_prim)).pair (Primrec.const _)

/-- `canonRed U C` reduces `HaltCanon` to SKI convertibility. -/
theorem haltCanon_reducesto_skiConv_spec {u : Code} {U : SKI} {C : Code} (hu : IsUniversal u)
    (hU : Computes U u.eval) (hC : RaceProg U C) : HaltCanon ⪯_s[canonRed U C] SKIConvProblem :=
  ProofRace.haltCanon_iff (Q := fun n => Conv (inst U C n) FF) hC
    (fun _ => conv_inst_iff_chk U C _) (fun _ h => conv_inst_of_one hu hU h)
    (fun _ h => not_conv_inst_of_zero hu hU h)

end DiagonaLean.SKIConv
