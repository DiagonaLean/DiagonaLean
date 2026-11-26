/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.KAComm.KATermEq.Undecidable
import DiagonaLean.KAComm.KleeneAlgebra.CanonRace
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # Halting-hardness of provable equality in Kleene algebra with commutativity over `ℕ`

The reduction from canonical machines, `canonReduction B C` (`KAComm/KleeneAlgebra/CanonRace.lean`),
is proved computable, so `KAComm.KATermEq.fromHaltWith B C …` is a proved halting reduction for each
choice of the interpreter constants `B` and the race program `C`. These exist only classically, so
halting-hardness, a proposition, obtains them in its proof (`KAComm.KATermEq.haltHard`); the problem
is not a computable predicate (`KAComm.KATermEq.not_computablePred`) and no machine decides it under
any computable encoding (`KAComm.KATermEq.not_machineDecidable`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 19
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.KAComm.KATermEq

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- `canonReduction B C` reduces `HaltCanon` to provable equality in Kleene algebra with
commutativity over `ℕ`. -/
theorem haltCanon_reducesto_spec {B : Base} {C : Code} (hB : B.Good) (hC : RaceProg true B C) :
    HaltCanon ⪯_s[canonReduction B C] KATermEqProblem := fun x => by
  simpa [KAComm.KleeneAlgebra.Rel, DecisionProblem] using haltCanon_iff_rel hB hC x

/-- **A proved halting reduction**, given the interpreter constants `B` and the race program `C`. -/
def fromHaltWith (B : Base) (C : Code) (hB : B.Good) (hC : RaceProg true B C) :
    HaltReduction KATermEqProblem :=
  ⟨canonReduction B C, (canonReduction_prim B C).to_comp, haltCanon_reducesto_spec hB hC⟩

/-- **Halting-hardness.** The interpreter constants and the race program exist (`exists_base`,
`exists_raceProg`). -/
theorem haltHard : HaltHard KATermEqProblem := by
  obtain ⟨B, hB⟩ := exists_base
  obtain ⟨C, hC⟩ := exists_raceProg true B
  exact ⟨fromHaltWith B C hB hC⟩

/-- **Not a computable predicate.** -/
theorem not_computablePred : ¬ ComputablePred KATermEqProblem :=
  haltHard.not_computablePred

/-- **No Turing machine decides it under any computable encoding.** -/
theorem not_machineDecidable {enc : Inst → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc KATermEqProblem :=
  haltHard.not_machineDecidable henc

/-- A halting-hard source for `hard_reduce_from`. -/
instance : HaltHardFact KATermEqProblem := ⟨haltHard⟩

end DiagonaLean.KAComm.KATermEq
