/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.SKIConv.Undecidable
import DiagonaLean.Foundations.Computability.CanonRace
import DiagonaLean.Foundations.Computability.HaltResults
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # SKI convertibility is halting-hard

On a canonical instance `x`, the reduction `canonRed U C` builds the instance of the race program
`C` on the code of `dataCanon x`, against `FF`. It is primitive recursive (`canonRed_primrec`):
`dataCanon` is, and so is the instance `inst U C`, through the code `skc` (`primrec_iff_skc`).
Smullyan's argument on canonical instances (`ProofRace.haltCanon_iff`) makes it a reduction, so
`SKIConv.fromHaltWith U C …` is a proved halting reduction, given the universal term `U` and the
race program `C`.

Those constants are only known to exist (a universal code, and the recursion theorem), so the
reduction takes them as arguments, and halting-hardness, which is a proposition, obtains them in its
proof (`SKIConv.haltHard`). From it, SKI convertibility is not a computable predicate
(`SKIConv.not_computablePred`), and no machine decides it under any computable encoding
(`SKIConv.not_machineDecidable`). These follow the proved layer; `Undecidable.lean` reaches the
same two statements through a machine-level race and the binary encoding `encSKI`.

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

/-- SKI convertibility is a halting-hard source for `hard_reduce_from`. -/
instance : HaltHardFact SKIConvProblem := ⟨haltHard⟩

end DiagonaLean.SKIConv
