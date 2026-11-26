/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KATermEq.Reductions.Halt_to_KATermEq
import DiagonaLean.KAComm.KleeneAlgebra.Separation
import DiagonaLean.KAComm.KleeneAlgebra.RExpPrimcodable
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Undecidability of equality on `K Σ̈`

Provable equality in Kleene algebra with commutativity over `ℕ` is synthetically halting-hard
(`KAComm.KATermEq.synthFromHalt`), given finite constants that are only known to exist. No Turing
machine decides it under the encoding `encNat` of a pair of expressions as the binary digits of its
code (`not_machineDecidable_kaTermEq`), or under any encoding that a machine computes from `encNat`
(`not_machineDecidable_kaTermEq_of_conv`). Since `rc` has a primitive recursive decoder, it is not a
computable predicate either (`not_computablePred_kaTermEq`). Nor does any machine decide it on the
instances `eqRed M` given the code of `M` (`not_machineDecidable_kaTermEq_eqRed`), by computable
inseparability.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

namespace DiagonaLean.KAComm.KATermEq.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Halt.Undecidable

/-- The former name of `KAComm.KATermEq.synthFromHalt`. -/
@[deprecated DiagonaLean.KAComm.KATermEq.synthFromHalt (since := "2026-11-23")]
abbrev undecidableKATermEq := @DiagonaLean.KAComm.KATermEq.synthFromHalt

/-- **No Turing machine decides provable equality in Kleene algebra over `ℕ`.** -/
theorem not_machineDecidable_kaTermEq : ¬ MachineDecidable encNat KATermEqProblem :=
  not_machineDecidable_of_family (ka := true) instCode instCode_prim rInst enc_nat iff_nat_ka
    (fun _ _ h => rInst_pos_ka h) (fun _ _ h => rInst_neg_ka h)

/-- **Provable equality in Kleene algebra with commutativity over `ℕ` is not a computable
predicate**: `encNat` writes the pair of codes `rc` in binary, and `rc` has a primitive recursive
decoder (`rcDec`), so this follows from `not_machineDecidable_kaTermEq`
(`not_computablePred_of_bitsPair`). -/
theorem not_computablePred_kaTermEq : ¬ ComputablePred KATermEqProblem :=
  Foundations.Computability.not_computablePred_of_bitsPair RExp.rc_primrec RExp.rcDec_primrec
    RExp.rcDec_rc not_machineDecidable_kaTermEq

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
