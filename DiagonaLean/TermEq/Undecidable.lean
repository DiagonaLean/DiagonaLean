/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.TermEq.Reductions.Halt_to_TermEq

@[expose] public section

/-! # Undecidability of equality on `T Σ̈`

Provable equality in pre-Kleene algebra with commutativity is `Undecidable` over `ℕ`
(`undecidable_termEq`) and over `{0, 1}` (`undecidable_termEq_bool`). No Turing machine decides it
under the encoding of a pair of expressions as the binary digits of its code
(`not_machineDecidable_termEq_nat`, `not_machineDecidable_termEq_bool`), nor on the instances
`eqRed M` given the code of `M` (`not_machineDecidable_termEq`). It separates the computably
inseparable pair `SelfOut true`, `SelfOut false` (`termEq_separated`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

open scoped Computability

namespace DiagonaLean.TermEq.Reduction

open DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing RExp TD FreePreKA Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation

/-- **Provable equality in pre-Kleene algebra with commutativity is `Undecidable`.** -/
theorem undecidable_termEq : Undecidable (@TermEq.DecisionProblem ℕ) := by
  obtain ⟨B, hB⟩ := exists_base
  obtain ⟨C, hC⟩ := exists_raceProg false B
  exact ⟨haltReducesTermEq B C hB hC⟩

/-- **Provable equality in pre-Kleene algebra with commutativity over `{0, 1}` is
`Undecidable`.** -/
theorem undecidable_termEq_bool : Undecidable TermEqProblem := by
  obtain ⟨B, hB⟩ := exists_base
  obtain ⟨C, hC⟩ := exists_raceProgB false B
  exact ⟨haltReducesTermEqBool B C hB hC⟩

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `ℕ`.** -/
theorem not_machineDecidable_termEq_nat :
    ¬ MachineDecidable encNat fun i : Inst => Equiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := false) instCode instCode_prim rInst enc_nat iff_nat
    (fun _ _ h => rInst_pos h) (fun _ _ h => rInst_neg h)

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `{0, 1}`.** -/
theorem not_machineDecidable_termEq_bool :
    ¬ MachineDecidable encBool fun i : InstB => Equiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := false) instCodeB instCodeB_prim
    (fun K l => sbI (rInst K l)) enc_bool iff_bool (fun _ _ h => pos_bool h)
    (fun _ _ h => neg_bool h)

/-- The case `X = T Σ̈`: on machine codes, provable equality in pre-KA has no machine decider. -/
theorem not_machineDecidable_termEq :
    ¬ MachineDecidable encodeBoolTM fun M => Equiv DComm (eqRed M).1 (eqRed M).2 := fun ⟨D, hD⟩ =>
  not_machineDecidable_selfEq factorT ⟨D, fun M =>
    ⟨fun h => (hD M).1 ((eqVia_factorT _).1 h), fun h => (hD M).2 (h ∘ (eqVia_factorT _).2)⟩⟩

/-- `eqRed` separates the inseparable pair by provable equality of terms in pre-Kleene algebra
with commutativity. -/
theorem termEq_separated : InsepUndecidable fun i : Inst => Equiv DComm i.1 i.2 :=
  ⟨⟨eqRed, fun _ h => (eqVia_factorT _).1 (eqVia_eqRed_pos factorT h),
    fun _ h hE => eqVia_eqRed_neg factorT h ((eqVia_factorT _).2 hE)⟩⟩

/-- **Provable equality in pre-Kleene algebra with commutativity is `Undecidable`,** given a
Smullyan family for `T Σ̈`. -/
theorem undecidable_termEq_of_family (fam : SmullyanFamily (SelfEq factorT)) :
    Undecidable (@TermEq.DecisionProblem ℕ) :=
  ⟨haltReducesTermEqOfFamily fam⟩

end DiagonaLean.TermEq.Reduction
