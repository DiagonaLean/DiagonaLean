/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.LangEqBool.Reductions.Halt_to_LangEqBool
import DiagonaLean.KAComm.KleeneAlgebra.Between
import DiagonaLean.KAComm.KleeneAlgebra.BoolCode

@[expose] public section

/-! # Undecidability of equality on `L Σ̈` over `{0, 1}`

The failure of equality of languages over `{0, 1}` is synthetically halting-hard
(`KAComm.LangEqBool.synthComplFromHalt`). No Turing machine decides equality of languages under the
encoding `encBool` of a pair of expressions as the binary digits of its code
(`not_machineDecidable_langEqBool`), or under any encoding that a machine computes from `encBool`
(`not_machineDecidable_langEqBool_of_conv`). The machine-level statement is the case of Theorem 18
where the predicate is equality of languages itself (`not_machineDecidable_eq_between_bool`).
Since the code of `encBool` has a primitive recursive decoder (`rcbDec`), it is not a computable
predicate either (`not_computablePred_langEqBool`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.LangEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing TD FreePreKA DiagonaLean.Synthetic.Definitions
  DiagonaLean.Halt.Undecidable

/-- **No Turing machine decides equality of languages over `{0, 1}`.** -/
theorem not_machineDecidable_langEqBool : ¬ MachineDecidable encBool LangEqBoolProblem :=
  not_machineDecidable_eq_between_bool _ (fun _ h => congrArg pl (mk_eq_mk.2 h)) fun _ h => h

/-- **Equality of languages over `{0, 1}` is not a computable predicate**: `encBool` writes the pair
of codes `rc (toNat e)` in binary, which has a primitive recursive decoder (`rcbDec`), so this
follows from `not_machineDecidable_langEqBool` (`not_computablePred_of_bitsPair`). -/
theorem not_computablePred_langEqBool : ¬ ComputablePred LangEqBoolProblem :=
  Foundations.Computability.not_computablePred_of_bitsPair rcb_prim rcbDec_prim rcbDec_rc
    not_machineDecidable_langEqBool

/-- **No Turing machine decides equality of languages over `{0, 1}`, under any encoding** that a
machine computes from `encBool`. -/
theorem not_machineDecidable_langEqBool_of_conv {enc : InstB → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encBool enc id) :
    ¬ MachineDecidable enc LangEqBoolProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_langEqBool hR

end DiagonaLean.KAComm.LangEqBool.Reduction
