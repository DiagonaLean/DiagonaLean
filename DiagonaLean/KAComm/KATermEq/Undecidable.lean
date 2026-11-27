/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KATermEq.Reductions.Halt_to_KATermEq
import DiagonaLean.KAComm.KleeneAlgebra.Separation
import DiagonaLean.KAComm.KleeneAlgebra.RExpPrimcodable
import DiagonaLean.Foundations.Computability.MachineBridge
import DiagonaLean.KAComm.KATermEq.Reductions.HaltCanon_to_KATermEq
import DiagonaLean.Foundations.Computability.HaltResults
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # Undecidability of equality on `K Σ̈`

The reduction from canonical machines, `canonReduction B C` (`KAComm/KleeneAlgebra/CanonRace.lean`,
correct by `haltCanon_reducesto_spec` in `Reductions/HaltCanon_to_KATermEq.lean`), is proved
computable, so `KAComm.KATermEq.fromHaltWith B C …` is a proved halting reduction to provable
equality in Kleene algebra with commutativity over `ℕ`, for each choice of the interpreter constants
`B` and the race program `C`. These exist only classically, so halting-hardness, a proposition,
obtains them in its proof (`KAComm.KATermEq.haltHard`); the problem is undecidable
(`KAComm.KATermEq.not_computablePred`) and no machine decides it under any computable encoding
(`KAComm.KATermEq.not_machineDecidable`).

Independently, no Turing machine decides it under the encoding `encNat` of a pair of expressions as
the binary digits of its code (`not_machineDecidable_kaTermEq`), or under any encoding that a
machine computes from `encNat` (`not_machineDecidable_kaTermEq_of_conv`). Nor does any machine
decide it on the instances `eqRed M` given the code of `M` (`not_machineDecidable_kaTermEq_eqRed`),
by computable inseparability. The synthetic result is in `SynthHardness.lean`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.KAComm.KATermEq.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Halt.Undecidable

/-- **No Turing machine decides provable equality in Kleene algebra over `ℕ`.** -/
theorem not_machineDecidable_kaTermEq : ¬ MachineDecidable encNat KATermEqProblem :=
  not_machineDecidable_of_family (ka := true) instCode instCode_prim rInst enc_nat iff_nat_ka
    (fun _ _ h => rInst_pos_ka h) (fun _ _ h => rInst_neg_ka h)

/-- **No Turing machine decides provable equality in Kleene algebra over `ℕ`, under any encoding**
that a machine computes from `encNat`. -/
theorem not_machineDecidable_kaTermEq_of_conv {enc : Inst → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc KATermEqProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_kaTermEq hR

/-- **No Turing machine decides provable equality in Kleene algebra on the instances `eqRed M`**,
given the code of `M`. This is the case `X = K Σ̈` of Theorem 18 on a model. -/
theorem not_machineDecidable_kaTermEq_eqRed :
    ¬ MachineDecidable encodeBoolTM fun M => KATermEqProblem (eqRed M) := fun ⟨D, hD⟩ =>
  not_machineDecidable_selfEq factorK ⟨D, fun M =>
    ⟨fun h => (hD M).1 ((eqVia_factorK _).1 h), fun h => (hD M).2 (h ∘ (eqVia_factorK _).2)⟩⟩

end DiagonaLean.KAComm.KATermEq.Reduction

namespace DiagonaLean.KAComm.KATermEq

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- **A proved halting reduction**, given the interpreter constants `B` and the race program `C`. -/
def fromHaltWith (B : Base) (C : Code) (hB : B.Good) (hC : RaceProg true B C) :
    HaltReduction KATermEqProblem :=
  ⟨canonReduction B C, (canonReduction_prim B C).to_comp, haltCanon_reducesto_spec hB hC⟩

-- Halting-hardness and its consequences: the interpreter constants and the race program exist
-- (`exists_base`, `exists_raceProg`), so the proof obtains them, and only the existence of a
-- reduction is stated.
halt_results KATermEqProblem from
  exists_base.elim fun B hB => (exists_raceProg true B).elim fun C hC =>
    ⟨fromHaltWith B C hB hC⟩

/-- A halting-hard source for `hard_reduce_from`. -/
instance : HaltHardFact KATermEqProblem := ⟨haltHard⟩

end DiagonaLean.KAComm.KATermEq
