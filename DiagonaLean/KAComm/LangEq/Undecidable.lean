/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.LangEq.Reductions.Halt_to_LangEq
import DiagonaLean.KAComm.KleeneAlgebra.Between
import DiagonaLean.KAComm.KleeneAlgebra.RExpPrimcodable
import DiagonaLean.Foundations.Computability.Undecidable

@[expose] public section

/-! # Undecidability of equality on `L Σ̈`

No Turing machine decides equality of languages under the encoding `encNat` of a pair of expressions
as the binary digits of its code (`not_machineDecidable_langEq`), or under any encoding that a
machine computes from `encNat` (`not_machineDecidable_langEq_of_conv`). Since `rc` has a primitive
recursive decoder, it is undecidable too (`KAComm.LangEq.not_computablePred`). The machine-level
statement is the case of Theorem 18 where the predicate is equality of languages itself
(`not_machineDecidable_eq_between`). The synthetic result is in `SynthHardness.lean`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.LangEq.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing TD FreePreKA DiagonaLean.Synthetic.Definitions
  DiagonaLean.Halt.Undecidable

/-- **No Turing machine decides equality of languages over `ℕ`.** -/
theorem not_machineDecidable_langEq : ¬ MachineDecidable encNat LangEqProblem :=
  not_machineDecidable_eq_between _ (fun _ h => congrArg pl (mk_eq_mk.2 h)) fun _ h => h

/-- **Equality of languages over `ℕ` is not a computable predicate**: `encNat` writes the pair of
codes `rc` in binary, and `rc` has a primitive recursive decoder (`rcDec`), so this follows from
`not_machineDecidable_langEq` (`not_computablePred_of_bitsPair`). -/
theorem _root_.DiagonaLean.KAComm.LangEq.not_computablePred :
    Foundations.Computability.Undecidable LangEqProblem :=
  Foundations.Computability.not_computablePred_of_bitsPair RExp.rc_primrec RExp.rcDec_primrec
    RExp.rcDec_rc not_machineDecidable_langEq

/-- **No Turing machine decides it under any computable encoding.** -/
theorem _root_.DiagonaLean.KAComm.LangEq.not_machineDecidable {enc : Inst → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc LangEqProblem :=
  Foundations.Computability.not_machineDecidable_of_not_computablePred henc
    DiagonaLean.KAComm.LangEq.not_computablePred

/-- **No Turing machine decides equality of languages over `ℕ`, under any encoding** that a machine
computes from `encNat`. -/
theorem not_machineDecidable_langEq_of_conv {enc : Inst → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc LangEqProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_langEq hR

end DiagonaLean.KAComm.LangEq.Reduction
