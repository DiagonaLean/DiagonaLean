/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.LangEqBool.Reductions.Halt_to_LangEqBool
import DiagonaLean.KAComm.KleeneAlgebra.Between

@[expose] public section

/-! # Undecidability of equality on `L Σ̈` over `{0, 1}`

The failure of equality of languages over `{0, 1}` is `Undecidable` (`undecidableNotLangEqBool`). No
Turing machine decides equality of languages under the encoding `encBool` of a pair of expressions
as the binary digits of its code (`not_machineDecidable_langEqBool`), or under any encoding that a
machine computes from `encBool` (`not_machineDecidable_langEqBool_of_conv`). The machine-level
statement is the case of Theorem 18 where the predicate is equality of languages itself
(`not_machineDecidable_eq_between_bool`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

open scoped Computability

namespace DiagonaLean.KAComm.LangEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing RExp TD FreePreKA Nat.Partrec
  DiagonaLean.Foundations.Computability DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation
  DiagonaLean.Halt.Undecidable

/-- **The failure of equality of languages over `{0, 1}` is `Undecidable`.** -/
def undecidableNotLangEqBool : Undecidable (Complement LangEqBoolProblem) :=
  haltReducesNotLangEqBool

/-- **No Turing machine decides equality of languages over `{0, 1}`.** -/
theorem not_machineDecidable_langEqBool : ¬ MachineDecidable encBool LangEqBoolProblem :=
  not_machineDecidable_eq_between_bool _ (fun _ h => congrArg pl (mk_eq_mk.2 h)) fun _ h => h

/-- **No Turing machine decides equality of languages over `{0, 1}`, under any encoding** that a
machine computes from `encBool`. -/
theorem not_machineDecidable_langEqBool_of_conv {enc : InstB → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encBool enc id) :
    ¬ MachineDecidable enc LangEqBoolProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_langEqBool hR

end DiagonaLean.KAComm.LangEqBool.Reduction
