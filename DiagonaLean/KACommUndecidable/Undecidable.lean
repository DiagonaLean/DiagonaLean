/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KACommUndecidable.Reductions.Halt_to_TermEq
import DiagonaLean.KACommUndecidable.Reductions.Halt_to_KATermEq
import DiagonaLean.KACommUndecidable.Reductions.Halt_to_LangEq
import DiagonaLean.KACommUndecidable.Reductions.Halt_to_ModelLe
import DiagonaLean.KACommUndecidable.KleeneAlgebra.Between

@[expose] public section

/-! # Kleene algebra with commutativity conditions is undecidable

The headline results of the paper, for the four problems of `KACommUndecidable.Basic`.

* **Equality on `T Σ̈` and `K Σ̈`** (provable equality in pre-Kleene algebra and in Kleene algebra
  with commutativity) is `Undecidable` over `ℕ` (`undecidableTermEq`, `undecidableKATermEq`) and
  over `{0, 1}` (`undecidableTermEqBool`, `undecidableKATermEqBool`), given finite constants that
  are only known to exist. No Turing machine decides it under the encoding of a pair of
  expressions as the binary digits of its code (`not_machineDecidable_termEq_nat`,
  `not_machineDecidable_termEq_bool` and the `kaTermEq` versions), nor on the instances `eqRed M`
  given the code of `M` (`not_machineDecidable_termEq`, `not_machineDecidable_kaTermEq`).
* **Equality on `L Σ̈`** fails undecidably over `ℕ` (`undecidableNotLangEq`) and over `{0, 1}`
  (`undecidableNotLangEqBool`).
* **Inclusion in `L Σ̈`** fails undecidably (`undecidableNotModelLe`).

The reductions from `HaltProblem` to equality on `T Σ̈` and `K Σ̈`, and the machine-level
statements over `ℕ` and `{0, 1}`, go through the race program of Theorem 19
(`KACommUndecidable/KleeneAlgebra/Race.lean`). The machine-level statements on the instances `eqRed M`
use computable inseparability instead (`Halt/Inseparable.lean`): `eqRed` sends machines that output
`1` on their own code to provably equal pairs and machines that output `0` to pairs with different
languages, so no machine decides any relation between pre-Kleene algebra provability and the
language model on these instances (`not_machineDecidable_selfEq`).
* **Every theory in between** (Theorem 18, general form): no machine decides any predicate on pairs
  of expressions over `ℕ` that contains provability in pre-Kleene algebra and is contained in the
  language model, for inequalities and for equations (`not_machineDecidable_between`,
  `not_machineDecidable_eq_between` in `KACommUndecidable/KleeneAlgebra/Between.lean`). In
  particular no machine decides equality or inclusion of languages
  (`not_machineDecidable_langEq_nat`, `not_machineDecidable_modelLe_nat`).
* **Encodings.** Each machine-level statement over `encNat` or `encBool` has an `_of_conv` version
  for any encoding that a machine computes from that one (`not_machineDecidable_of_conv`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

open scoped Computability

/-! ### Equality on `T Σ̈` -/

namespace DiagonaLean.TermEq.Reduction

open DiagonaLean.KACommUndecidable.KleeneAlgebra

open Cslib.Turing RExp TD FreePreKA Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Halt.Undecidable
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

/-- **Provable equality in pre-Kleene algebra with commutativity is `Undecidable`**, given the
interpreter constants `B` (`exists_base`) and the race program `C` (`exists_raceProg`). These finite
constants are only known to exist, since Mathlib's construction of a program from a `Partrec`
function is not executable, so they are arguments rather than computed here. The statement without
them is `not_machineDecidable_termEq_nat`. -/
def undecidableTermEq (B : Base) (C : Code) (hB : B.Good) (hC : RaceProg false B C) :
    Undecidable (@TermEq.DecisionProblem ℕ) :=
  haltReducesTermEq B C hB hC

/-- **Provable equality in pre-Kleene algebra with commutativity over `{0, 1}` is `Undecidable`**,
given the constants `B` (`exists_base`) and `C` (`exists_raceProgB`), as in `undecidableTermEq`. The
statement without them is `not_machineDecidable_termEq_bool`. -/
def undecidableTermEqBool (B : Base) (C : Code) (hB : B.Good) (hC : RaceProgB false B C) :
    Undecidable TermEqProblem :=
  haltReducesTermEqBool B C hB hC

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `ℕ`.** -/
theorem not_machineDecidable_termEq_nat :
    ¬ MachineDecidable encNat fun i : Inst => Equiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := false) instCode instCode_prim rInst enc_nat iff_nat
    (fun _ _ h => rInst_pos h) (fun _ _ h => rInst_neg h)

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `ℕ`, under any
encoding** that a machine computes from `encNat`. -/
theorem not_machineDecidable_termEq_nat_of_conv {enc : Inst → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc fun i : Inst => Equiv DComm i.1 i.2 :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_termEq_nat hR

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `{0, 1}`.** -/
theorem not_machineDecidable_termEq_bool :
    ¬ MachineDecidable encBool fun i : InstB => Equiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := false) instCodeB instCodeB_prim
    (fun K l => sbI (rInst K l)) enc_bool iff_bool (fun _ _ h => pos_bool h)
    (fun _ _ h => neg_bool h)

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `{0, 1}`, under any
encoding** that a machine computes from `encBool`. -/
theorem not_machineDecidable_termEq_bool_of_conv {enc : InstB → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encBool enc id) :
    ¬ MachineDecidable enc fun i : InstB => Equiv DComm i.1 i.2 :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_termEq_bool hR

/-- The case `X = T Σ̈`: on machine codes, provable equality in pre-KA has no machine decider. -/
theorem not_machineDecidable_termEq :
    ¬ MachineDecidable encodeBoolTM fun M => Equiv DComm (eqRed M).1 (eqRed M).2 := fun ⟨D, hD⟩ =>
  not_machineDecidable_selfEq factorT ⟨D, fun M =>
    ⟨fun h => (hD M).1 ((eqVia_factorT _).1 h), fun h => (hD M).2 (h ∘ (eqVia_factorT _).2)⟩⟩

end DiagonaLean.TermEq.Reduction

/-! ### Equality on `K Σ̈` -/

namespace DiagonaLean.KATermEq.Reduction

open DiagonaLean.KACommUndecidable.KleeneAlgebra

open Cslib.Turing RExp TD FreePreKA Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Halt.Undecidable
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

/-- **Provable equality in Kleene algebra with commutativity is `Undecidable`**, given the
interpreter constants `B` (`exists_base`) and the race program `C` (`exists_raceProg`). These finite
constants are only known to exist, since Mathlib's construction of a program from a `Partrec`
function is not executable, so they are arguments rather than computed here. The statement without
them is `not_machineDecidable_kaTermEq_nat`. -/
def undecidableKATermEq (B : Base) (C : Code) (hB : B.Good) (hC : RaceProg true B C) :
    Undecidable (@KATermEq.DecisionProblem ℕ) :=
  haltReducesKATermEq B C hB hC

/-- **Provable equality in Kleene algebra with commutativity over `{0, 1}` is `Undecidable`**,
given the constants `B` (`exists_base`) and `C` (`exists_raceProgB`), as in `undecidableKATermEq`.
The statement without them is `not_machineDecidable_kaTermEq_bool`. -/
def undecidableKATermEqBool (B : Base) (C : Code) (hB : B.Good) (hC : RaceProgB true B C) :
    Undecidable KATermEqProblem :=
  haltReducesKATermEqBool B C hB hC

/-- **No Turing machine decides provable equality in Kleene algebra over `ℕ`.** -/
theorem not_machineDecidable_kaTermEq_nat :
    ¬ MachineDecidable encNat fun i : Inst => KAEquiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := true) instCode instCode_prim rInst enc_nat iff_nat_ka
    (fun _ _ h => rInst_pos_ka h) (fun _ _ h => rInst_neg_ka h)

/-- **No Turing machine decides provable equality in Kleene algebra over `ℕ`, under any
encoding** that a machine computes from `encNat`. -/
theorem not_machineDecidable_kaTermEq_nat_of_conv {enc : Inst → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc fun i : Inst => KAEquiv DComm i.1 i.2 :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_kaTermEq_nat hR

/-- **No Turing machine decides provable equality in Kleene algebra over `{0, 1}`.** -/
theorem not_machineDecidable_kaTermEq_bool :
    ¬ MachineDecidable encBool fun i : InstB => KAEquiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := true) instCodeB instCodeB_prim
    (fun K l => sbI (rInst K l)) enc_bool iff_bool_ka (fun _ _ h => pos_bool_ka h)
    (fun _ _ h => neg_bool_ka h)

/-- **No Turing machine decides provable equality in Kleene algebra over `{0, 1}`, under any
encoding** that a machine computes from `encBool`. -/
theorem not_machineDecidable_kaTermEq_bool_of_conv {enc : InstB → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encBool enc id) :
    ¬ MachineDecidable enc fun i : InstB => KAEquiv DComm i.1 i.2 :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_kaTermEq_bool hR

/-- The case `X = K Σ̈`: on machine codes, provable equality in KA has no machine decider. -/
theorem not_machineDecidable_kaTermEq :
    ¬ MachineDecidable encodeBoolTM fun M => KAEquiv DComm (eqRed M).1 (eqRed M).2 :=
  fun ⟨D, hD⟩ => not_machineDecidable_selfEq factorK ⟨D, fun M =>
    ⟨fun h => (hD M).1 ((eqVia_factorK _).1 h), fun h => (hD M).2 (h ∘ (eqVia_factorK _).2)⟩⟩

end DiagonaLean.KATermEq.Reduction

/-! ### Equality on `L Σ̈` -/

namespace DiagonaLean.LangEq.Reduction

open DiagonaLean.KACommUndecidable.KleeneAlgebra

open Cslib.Turing RExp TD FreePreKA Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Halt.Undecidable
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

/-- **`Undecidable` for language inequality of two terms.** -/
def undecidableNotLangEq :
    Undecidable (Complement (@LangEq.DecisionProblem ℕ)) :=
  haltReducesNotLangEq

/-- **The failure of language equality over `{0, 1}` is `Undecidable`.** -/
def undecidableNotLangEqBool :
    Undecidable (Complement LangEqProblem) :=
  haltReducesNotLangEqBool

/-- **No Turing machine decides equality of languages over `ℕ`.** -/
theorem not_machineDecidable_langEq_nat :
    ¬ MachineDecidable encNat fun i : Inst => pl (mk i.1 : TD ℕ) = pl (mk i.2) :=
  not_machineDecidable_eq_between _ (fun _ h => congrArg pl (mk_eq_mk.2 h)) fun _ h => h

/-- **No Turing machine decides equality of languages over `ℕ`, under any
encoding** that a machine computes from `encNat`. -/
theorem not_machineDecidable_langEq_nat_of_conv {enc : Inst → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc fun i : Inst => pl (mk i.1 : TD ℕ) = pl (mk i.2) :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_langEq_nat hR

end DiagonaLean.LangEq.Reduction

/-! ### Inclusion in `L Σ̈` -/

namespace DiagonaLean.ModelLe.Reduction

open DiagonaLean.KACommUndecidable.KleeneAlgebra

open Cslib.Turing RExp TD FreePreKA DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Halt.Undecidable
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

/-- **Undecidability in the library's sense:** `HaltProblem ⪯ₘ` the complement of language-model
inclusion for KA with commutativity conditions. -/
def undecidableNotModelLe : Undecidable (Complement (@DecisionProblem ℕ)) :=
  haltReducesNotModelLe

/-- **No Turing machine decides inclusion of languages over `ℕ`.** -/
theorem not_machineDecidable_modelLe_nat : ¬ MachineDecidable encNat ModelLe :=
  not_machineDecidable_between _ (fun _ h => h.modelLe) fun _ h => h

/-- **No Turing machine decides inclusion of languages over `ℕ`, under any
encoding** that a machine computes from `encNat`. -/
theorem not_machineDecidable_modelLe_nat_of_conv {enc : Inst → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc ModelLe :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_modelLe_nat hR

end DiagonaLean.ModelLe.Reduction
