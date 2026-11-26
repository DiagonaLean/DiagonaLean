/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.ModelLeBool.Reductions.Halt_to_ModelLeBool
import DiagonaLean.KAComm.KleeneAlgebra.Between
import DiagonaLean.KAComm.KleeneAlgebra.BoolCode

@[expose] public section

/-! # Undecidability of inclusion in `L Σ̈` over `{0, 1}`

The failure of inclusion of languages over `{0, 1}` is synthetically halting-hard
(`KAComm.ModelLeBool.synthComplFromHalt`). No Turing machine decides inclusion of languages under
the encoding `encBool` of a pair of expressions as the binary digits of its code
(`not_machineDecidable_modelLeBool`), or under any encoding that a machine computes from `encBool`
(`not_machineDecidable_modelLeBool_of_conv`). The machine-level statement is the case of Theorem 18
where the predicate is inclusion of languages itself (`not_machineDecidable_between_bool`).
Since the code of `encBool` has a primitive recursive decoder (`rcbDec`), it is not a computable
predicate either (`not_computablePred_modelLeBool`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.ModelLeBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing TD DiagonaLean.Synthetic.Definitions
  DiagonaLean.Halt.Undecidable

/-- **No Turing machine decides inclusion of languages over `{0, 1}`.** -/
theorem not_machineDecidable_modelLeBool : ¬ MachineDecidable encBool ModelLeBoolProblem :=
  not_machineDecidable_between_bool _ (fun _ h => pl_mono h) fun _ h => h

/-- **Inclusion of languages over `{0, 1}` is not a computable predicate**: `encBool` writes the
pair of codes `rc (toNat e)` in binary, which has a primitive recursive decoder (`rcbDec`), so this
follows from `not_machineDecidable_modelLeBool` (`not_computablePred_of_bitsPair`). -/
theorem not_computablePred_modelLeBool : ¬ ComputablePred ModelLeBoolProblem :=
  Foundations.Computability.not_computablePred_of_bitsPair rcb_prim rcbDec_prim rcbDec_rc
    not_machineDecidable_modelLeBool

/-- **No Turing machine decides inclusion of languages over `{0, 1}`, under any encoding** that a
machine computes from `encBool`. -/
theorem not_machineDecidable_modelLeBool_of_conv {enc : InstB → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encBool enc id) :
    ¬ MachineDecidable enc ModelLeBoolProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_modelLeBool hR

end DiagonaLean.KAComm.ModelLeBool.Reduction
