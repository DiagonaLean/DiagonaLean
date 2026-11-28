/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.ModelLe.Reductions.Halt_to_ModelLe

@[expose] public section

/-! # The failure of inclusion in `L Σ̈` is synthetically halting-hard

The failure of inclusion of languages over `ℕ` is synthetically halting-hard
(`KAComm.ModelLe.synthComplFromHalt`), through the reduction of `Reductions/Halt_to_ModelLe.lean`.
The undecidability results are in `Undecidable.lean`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.ModelLe.Reduction

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Halt DiagonaLean.Synthetic.Definitions

/-- **The failure of inclusion of languages over `ℕ` is synthetically halting-hard.** `HaltProblem`
many-one reduces to the failure of inclusion in the language model. -/
def _root_.DiagonaLean.KAComm.ModelLe.synthComplFromHalt :
    HaltProblem ⪯_s Complement ModelLeProblem :=
  ⟨haltRed, halt_reducesto_not_modelLe_spec⟩

end DiagonaLean.KAComm.ModelLe.Reduction
