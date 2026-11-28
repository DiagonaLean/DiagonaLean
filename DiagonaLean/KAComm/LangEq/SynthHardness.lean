/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.LangEq.Reductions.Halt_to_LangEq

@[expose] public section

/-! # The failure of equality on `L Σ̈` is synthetically halting-hard

The failure of equality of languages over `ℕ` is synthetically halting-hard
(`KAComm.LangEq.synthComplFromHalt`), through the reduction of `Reductions/Halt_to_LangEq.lean`. The
undecidability results are in `Undecidable.lean`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.LangEq.Reduction

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Halt DiagonaLean.Synthetic.Definitions

/-- **The failure of equality of languages over `ℕ` is synthetically halting-hard.** `HaltProblem`
many-one reduces to the failure of language equality over `ℕ`. -/
def _root_.DiagonaLean.KAComm.LangEq.synthComplFromHalt :
    HaltProblem ⪯_s Complement LangEqProblem :=
  ⟨haltEqRed, halt_reducesto_not_langEq_spec⟩

end DiagonaLean.KAComm.LangEq.Reduction
