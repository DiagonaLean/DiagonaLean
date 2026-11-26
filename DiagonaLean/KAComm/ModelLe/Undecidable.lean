/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.ModelLe.Reductions.Halt_to_ModelLe
import DiagonaLean.KAComm.KleeneAlgebra.Between
import DiagonaLean.KAComm.KleeneAlgebra.RExpPrimcodable
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Undecidability of inclusion in `L Σ̈`

The failure of inclusion of languages over `ℕ` is synthetically halting-hard
(`KAComm.ModelLe.synthComplFromHalt`). No Turing machine decides inclusion of languages under the
encoding `encNat` of a pair of expressions as the binary digits of its code
(`not_machineDecidable_modelLe`), or under any encoding that a machine computes from `encNat`
(`not_machineDecidable_modelLe_of_conv`). Since `rc` has a primitive recursive decoder, it is not a
computable predicate either (`not_computablePred_modelLe`). The machine-level statement is the case
of Theorem 18 where the predicate is inclusion of languages itself (`not_machineDecidable_between`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.ModelLe.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing DiagonaLean.Synthetic.Definitions
  DiagonaLean.Halt.Undecidable

/-- The former name of `KAComm.ModelLe.synthComplFromHalt`. -/
@[deprecated DiagonaLean.KAComm.ModelLe.synthComplFromHalt (since := "2026-11-23")]
abbrev undecidableNotModelLe := @DiagonaLean.KAComm.ModelLe.synthComplFromHalt

/-- **No Turing machine decides inclusion of languages over `ℕ`.** -/
theorem not_machineDecidable_modelLe : ¬ MachineDecidable encNat ModelLeProblem :=
  not_machineDecidable_between _ (fun _ h => h.modelLe) fun _ h => h

/-- **Inclusion of languages over `ℕ` is not a computable predicate**: `encNat` writes the pair of
codes `rc` in binary, and `rc` has a primitive recursive decoder (`rcDec`), so this follows from
`not_machineDecidable_modelLe` (`not_computablePred_of_bitsPair`). -/
theorem not_computablePred_modelLe : ¬ ComputablePred ModelLeProblem :=
  Foundations.Computability.not_computablePred_of_bitsPair RExp.rc_primrec RExp.rcDec_primrec
    RExp.rcDec_rc not_machineDecidable_modelLe

/-- **No Turing machine decides inclusion of languages over `ℕ`, under any encoding** that a machine
computes from `encNat`. -/
theorem not_machineDecidable_modelLe_of_conv {enc : Inst → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc ModelLeProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_modelLe hR

end DiagonaLean.KAComm.ModelLe.Reduction
