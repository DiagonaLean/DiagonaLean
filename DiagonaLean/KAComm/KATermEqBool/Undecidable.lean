/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KATermEqBool.Reductions.Halt_to_KATermEqBool
import DiagonaLean.Halt.Inseparable

@[expose] public section

/-! # Undecidability of equality on `K Σ̈` over `{0, 1}`

Provable equality in Kleene algebra with commutativity over `{0, 1}` is synthetically halting-hard
(`KAComm.KATermEqBool.synthFromHalt`), given finite constants that are only known to exist. No
Turing machine decides it under the encoding `encBool` of a pair of expressions as the binary digits
of its code (`not_machineDecidable_kaTermEqBool`), or under any encoding that a machine computes
from `encBool` (`not_machineDecidable_kaTermEqBool_of_conv`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

namespace DiagonaLean.KAComm.KATermEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions DiagonaLean.Halt.Undecidable

/-- The former name of `KAComm.KATermEqBool.synthFromHalt`. -/
@[deprecated DiagonaLean.KAComm.KATermEqBool.synthFromHalt (since := "2026-11-23")]
abbrev undecidableKATermEqBool := @DiagonaLean.KAComm.KATermEqBool.synthFromHalt

/-- **No Turing machine decides provable equality in Kleene algebra over `{0, 1}`.** -/
theorem not_machineDecidable_kaTermEqBool : ¬ MachineDecidable encBool KATermEqBoolProblem :=
  not_machineDecidable_of_family (ka := true) instCodeB instCodeB_prim
    (fun K l => sbI (rInst K l)) enc_bool iff_bool_ka (fun _ _ h => pos_bool_ka h)
    (fun _ _ h => neg_bool_ka h)

/-- **No Turing machine decides provable equality in Kleene algebra over `{0, 1}`, under any
encoding** that a machine computes from `encBool`. -/
theorem not_machineDecidable_kaTermEqBool_of_conv {enc : InstB → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encBool enc id) :
    ¬ MachineDecidable enc KATermEqBoolProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_kaTermEqBool hR

end DiagonaLean.KAComm.KATermEqBool.Reduction
