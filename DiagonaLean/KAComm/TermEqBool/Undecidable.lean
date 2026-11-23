/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.TermEqBool.Reductions.Halt_to_TermEqBool
import DiagonaLean.Halt.Inseparable
import DiagonaLean.KAComm.KleeneAlgebra.BoolCode

@[expose] public section

/-! # Undecidability of equality on `T Σ̈` over `{0, 1}`

Provable equality in pre-Kleene algebra with commutativity over `{0, 1}` is synthetically
halting-hard (`KAComm.TermEqBool.synthFromHalt`), given finite constants that are only known to
exist. No Turing machine decides it under the encoding `encBool` of a pair of expressions as the
binary digits of its code (`not_machineDecidable_termEqBool`), or under any encoding that a machine
computes from `encBool` (`not_machineDecidable_termEqBool_of_conv`).
Since the code of `encBool` has a primitive recursive decoder (`rcbDec`), it is not a computable
predicate either (`not_computablePred_termEqBool`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

namespace DiagonaLean.KAComm.TermEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions DiagonaLean.Halt.Undecidable

/-- The former name of `KAComm.TermEqBool.synthFromHalt`. -/
@[deprecated DiagonaLean.KAComm.TermEqBool.synthFromHalt (since := "2026-11-23")]
abbrev undecidableTermEqBool := @DiagonaLean.KAComm.TermEqBool.synthFromHalt

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `{0, 1}`.** -/
theorem not_machineDecidable_termEqBool : ¬ MachineDecidable encBool TermEqBoolProblem :=
  not_machineDecidable_of_family (ka := false) instCodeB instCodeB_prim
    (fun K l => sbI (rInst K l)) enc_bool iff_bool (fun _ _ h => pos_bool h)
    (fun _ _ h => neg_bool h)

/-- **Provable equality in pre-Kleene algebra with commutativity over `{0, 1}` is not a computable
predicate**: `encBool` writes the pair of codes `rc (toNat e)` in binary, which has a primitive
recursive decoder (`rcbDec`), so this follows from `not_machineDecidable_termEqBool`
(`not_computablePred_of_bitsPair`). -/
theorem not_computablePred_termEqBool : ¬ ComputablePred TermEqBoolProblem :=
  Foundations.Computability.not_computablePred_of_bitsPair rcb_prim rcbDec_prim rcbDec_rc
    not_machineDecidable_termEqBool

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `{0, 1}`, under any
encoding** that a machine computes from `encBool`. -/
theorem not_machineDecidable_termEqBool_of_conv {enc : InstB → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encBool enc id) :
    ¬ MachineDecidable enc TermEqBoolProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_termEqBool hR

end DiagonaLean.KAComm.TermEqBool.Reduction
