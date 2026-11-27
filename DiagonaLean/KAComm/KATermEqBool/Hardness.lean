/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.KAComm.KATermEqBool.Undecidable
import DiagonaLean.KAComm.KleeneAlgebra.CanonRace
import DiagonaLean.Foundations.Computability.HaltResults
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # Halting-hardness of provable equality in Kleene algebra with commutativity over `{0, 1}`

The reduction from canonical machines, `canonReductionB B C`
(`KAComm/KleeneAlgebra/CanonRace.lean`), is proved computable, so `KAComm.KATermEqBool.fromHaltWith
B C …` is a proved halting reduction for each choice of the interpreter constants `B` and the race
program `C`. These exist only classically, so halting-hardness, a proposition, obtains them in its
proof (`KAComm.KATermEqBool.haltHard`); the problem is not a computable predicate
(`KAComm.KATermEqBool.not_computablePred`) and no machine decides it under any computable encoding
(`KAComm.KATermEqBool.not_machineDecidable`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 19
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.KAComm.KATermEqBool

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- `canonReductionB B C` reduces `HaltCanon` to provable equality in Kleene algebra with
commutativity over `{0, 1}`. -/
theorem haltCanon_reducesto_spec {B : Base} {C : Code} (hB : B.Good) (hC : RaceProgB true B C) :
    HaltCanon ⪯_s[canonReductionB B C] KATermEqBoolProblem := fun x =>
  (haltCanon_iff_qb hB hC x).trans (by
    simpa [QB, KAComm.KleeneAlgebra.Rel, canonReductionB, DecisionProblem] using kaEquiv_iff_map)

/-- **A proved halting reduction**, given the interpreter constants `B` and the race program `C`. -/
def fromHaltWith (B : Base) (C : Code) (hB : B.Good) (hC : RaceProgB true B C) :
    HaltReduction KATermEqBoolProblem :=
  ⟨canonReductionB B C, (canonReductionB_prim B C).to_comp, haltCanon_reducesto_spec hB hC⟩

-- Halting-hardness and its consequences: the interpreter constants and the race program exist
-- (`exists_base`, `exists_raceProgB`), so the proof obtains them, and only the existence of a
-- reduction is stated.
halt_results KATermEqBoolProblem from
  exists_base.elim fun B hB => (exists_raceProgB true B).elim fun C hC =>
    ⟨fromHaltWith B C hB hC⟩

/-- A halting-hard source for `hard_reduce_from`. -/
instance : HaltHardFact KATermEqBoolProblem := ⟨haltHard⟩

end DiagonaLean.KAComm.KATermEqBool
