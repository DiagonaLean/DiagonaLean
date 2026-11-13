/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KATermEq.Reductions.Halt_to_KATermEq

@[expose] public section

/-! # Undecidability of equality on `K Σ̈`

Provable equality in Kleene algebra with commutativity is `Undecidable` over `ℕ`
(`undecidable_kaTermEq`) and over `{0, 1}` (`undecidable_kaTermEq_bool`). No Turing machine decides
it under the encoding of a pair of expressions as the binary digits of its code
(`not_machineDecidable_kaTermEq_nat`, `not_machineDecidable_kaTermEq_bool`), nor on the instances
`eqRed M` given the code of `M` (`not_machineDecidable_kaTermEq`). It separates the computably
inseparable pair `SelfOut true`, `SelfOut false` (`kaTermEq_separated`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

open scoped Computability

namespace DiagonaLean.KATermEq.Reduction

open DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing RExp TD FreePreKA Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation

/-- **Provable equality in Kleene algebra with commutativity is `Undecidable`.** -/
theorem undecidable_kaTermEq : Undecidable (@KATermEq.DecisionProblem ℕ) := by
  obtain ⟨B, hB⟩ := exists_base
  obtain ⟨C, hC⟩ := exists_raceProg true B
  exact ⟨haltReducesKATermEq B C hB hC⟩

/-- **Provable equality in Kleene algebra with commutativity over `{0, 1}` is `Undecidable`.** -/
theorem undecidable_kaTermEq_bool : Undecidable KATermEqProblem := by
  obtain ⟨B, hB⟩ := exists_base
  obtain ⟨C, hC⟩ := exists_raceProgB true B
  exact ⟨haltReducesKATermEqBool B C hB hC⟩

/-- **No Turing machine decides provable equality in Kleene algebra over `ℕ`.** -/
theorem not_machineDecidable_kaTermEq_nat :
    ¬ MachineDecidable encNat fun i : Inst => KAEquiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := true) instCode instCode_prim rInst enc_nat iff_nat_ka
    (fun _ _ h => rInst_pos_ka h) (fun _ _ h => rInst_neg_ka h)

/-- **No Turing machine decides provable equality in Kleene algebra over `{0, 1}`.** -/
theorem not_machineDecidable_kaTermEq_bool :
    ¬ MachineDecidable encBool fun i : InstB => KAEquiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := true) instCodeB instCodeB_prim
    (fun K l => sbI (rInst K l)) enc_bool iff_bool_ka (fun _ _ h => pos_bool_ka h)
    (fun _ _ h => neg_bool_ka h)

/-- The case `X = K Σ̈`: on machine codes, provable equality in KA has no machine decider. -/
theorem not_machineDecidable_kaTermEq :
    ¬ MachineDecidable encodeBoolTM fun M => KAEquiv DComm (eqRed M).1 (eqRed M).2 :=
  fun ⟨D, hD⟩ => not_machineDecidable_selfEq factorK ⟨D, fun M =>
    ⟨fun h => (hD M).1 ((eqVia_factorK _).1 h), fun h => (hD M).2 (h ∘ (eqVia_factorK _).2)⟩⟩

/-- `eqRed` separates the inseparable pair by provable equality of terms in Kleene algebra with
commutativity, the theory of the paper's title. -/
theorem kaTermEq_separated : InsepUndecidable fun i : Inst => KAEquiv DComm i.1 i.2 :=
  ⟨sepReducesKATermEq⟩

end DiagonaLean.KATermEq.Reduction
