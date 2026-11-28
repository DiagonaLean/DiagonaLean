/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.LangEqBool.Reductions.Halt_to_LangEqBool

@[expose] public section

/-! # The failure of equality on `L Σ̈` over `{0, 1}` is synthetically halting-hard

The failure of equality of languages over `{0, 1}` is synthetically halting-hard
(`KAComm.LangEqBool.synthComplFromHalt`), through the reduction of
`Reductions/Halt_to_LangEqBool.lean`. The undecidability results are in `Undecidable.lean`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.LangEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions

/-- **The failure of equality of languages over `{0, 1}` is synthetically halting-hard.**
`HaltProblem` many-one reduces to the failure of language equality over `{0, 1}`. -/
def _root_.DiagonaLean.KAComm.LangEqBool.synthComplFromHalt :
    HaltProblem ⪯_s Complement LangEqBoolProblem :=
  ⟨haltEqRedB, halt_reducesto_not_langEqBool_spec⟩

end DiagonaLean.KAComm.LangEqBool.Reduction
