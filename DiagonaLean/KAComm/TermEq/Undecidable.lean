/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.TermEq.Reductions.Halt_to_TermEq
import DiagonaLean.KAComm.KleeneAlgebra.Separation

@[expose] public section

/-! # Undecidability of equality on `T Σ̈`

Provable equality in pre-Kleene algebra with commutativity over `ℕ` is synthetically halting-hard
(`KAComm.TermEq.synthFromHalt`), given finite constants that are only known to exist. No Turing
machine decides it under the encoding `encNat` of a pair of expressions as the binary digits of its
code (`not_machineDecidable_termEq`), or under any encoding that a machine computes from `encNat`
(`not_machineDecidable_termEq_of_conv`). Nor does any machine decide it on the instances `eqRed M`
given the code of `M` (`not_machineDecidable_termEq_eqRed`), by computable inseparability.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

namespace DiagonaLean.KAComm.TermEq.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Halt.Undecidable

/-- The former name of `KAComm.TermEq.synthFromHalt`. -/
@[deprecated DiagonaLean.KAComm.TermEq.synthFromHalt (since := "2026-11-23")]
abbrev undecidableTermEq := @DiagonaLean.KAComm.TermEq.synthFromHalt

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `ℕ`.** -/
theorem not_machineDecidable_termEq : ¬ MachineDecidable encNat TermEqProblem :=
  not_machineDecidable_of_family (ka := false) instCode instCode_prim rInst enc_nat iff_nat
    (fun _ _ h => rInst_pos h) (fun _ _ h => rInst_neg h)

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `ℕ`, under any
encoding** that a machine computes from `encNat`. -/
theorem not_machineDecidable_termEq_of_conv {enc : Inst → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc TermEqProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_termEq hR

/-- **No Turing machine decides provable equality in pre-Kleene algebra on the instances
`eqRed M`**, given the code of `M`. This is the case `X = T Σ̈` of Theorem 18 on a model. -/
theorem not_machineDecidable_termEq_eqRed :
    ¬ MachineDecidable encodeBoolTM fun M => TermEqProblem (eqRed M) := fun ⟨D, hD⟩ =>
  not_machineDecidable_selfEq factorT ⟨D, fun M =>
    ⟨fun h => (hD M).1 ((eqVia_factorT _).1 h), fun h => (hD M).2 (h ∘ (eqVia_factorT _).2)⟩⟩

end DiagonaLean.KAComm.TermEq.Reduction
