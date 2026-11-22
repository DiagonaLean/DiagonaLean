/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.LangEq.Reductions.Halt_to_LangEq
import DiagonaLean.KAComm.KleeneAlgebra.Between

@[expose] public section

/-! # Undecidability of equality on `L Σ̈`

The failure of equality of languages over `ℕ` is synthetically halting-hard
(`undecidableNotLangEq`). No Turing machine decides equality of languages under the encoding
`encNat` of a pair of expressions as the binary digits of its code (`not_machineDecidable_langEq`),
or under any encoding that a machine computes from `encNat` (`not_machineDecidable_langEq_of_conv`).
The machine-level statement is the case of Theorem 18 where the predicate is equality of languages
itself (`not_machineDecidable_eq_between`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.LangEq.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing TD FreePreKA DiagonaLean.Synthetic.Definitions
  DiagonaLean.Halt.Undecidable

/-- **The failure of equality of languages over `ℕ` is synthetically halting-hard.** -/
def undecidableNotLangEq : SynthHaltReduction (Complement LangEqProblem) :=
  haltReducesNotLangEq

/-- **No Turing machine decides equality of languages over `ℕ`.** -/
theorem not_machineDecidable_langEq : ¬ MachineDecidable encNat LangEqProblem :=
  not_machineDecidable_eq_between _ (fun _ h => congrArg pl (mk_eq_mk.2 h)) fun _ h => h

/-- **No Turing machine decides equality of languages over `ℕ`, under any encoding** that a machine
computes from `encNat`. -/
theorem not_machineDecidable_langEq_of_conv {enc : Inst → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc LangEqProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_langEq hR

end DiagonaLean.KAComm.LangEq.Reduction
