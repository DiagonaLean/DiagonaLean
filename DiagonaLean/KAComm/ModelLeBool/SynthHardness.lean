/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.ModelLeBool.Reductions.Halt_to_ModelLeBool

@[expose] public section

/-! # The failure of inclusion in `L Σ̈` over `{0, 1}` is synthetically halting-hard

The failure of inclusion of languages over `{0, 1}` is synthetically halting-hard
(`KAComm.ModelLeBool.synthComplFromHalt`), through the reduction of
`Reductions/Halt_to_ModelLeBool.lean`. The undecidability results are in `Undecidable.lean`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.ModelLeBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions

/-- **The failure of inclusion of languages over `{0, 1}` is synthetically halting-hard.**
`HaltProblem` many-one reduces to the failure of inclusion in the language model over `{0, 1}`. -/
def _root_.DiagonaLean.KAComm.ModelLeBool.synthComplFromHalt :
    HaltProblem ⪯_s Complement ModelLeBoolProblem :=
  ⟨haltRedB, halt_reducesto_not_modelLeBool_spec⟩

end DiagonaLean.KAComm.ModelLeBool.Reduction
