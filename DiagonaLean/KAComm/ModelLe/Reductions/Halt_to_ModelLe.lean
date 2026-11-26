/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.ModelLe.Basic
import DiagonaLean.KAComm.KleeneAlgebra.Separation

@[expose] public section

/-! # `HaltProblem ⪯_s` the failure of inclusion in `L Σ̈`

`haltRed` sends `(M, w)` to the inequality `(init w)_r R_M∗ ≤ Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ_M`, with letters
renamed to their codes. `M` halts on `w` iff this inequality fails in the language model
(`halt_iff_not_modelLe`), so the reduction lands in the complement of inclusion.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.ModelLe.Reduction

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Halt DiagonaLean.Synthetic.Definitions

/-- `haltRed` reduces `HaltProblem` to the failure of inclusion in the language model. -/
theorem halt_reducesto_not_modelLe_spec :
    HaltProblem ⪯_s[haltRed] Complement ModelLeProblem :=
  halt_iff_not_modelLe

/-- **The failure of inclusion of languages over `ℕ` is synthetically halting-hard.** `HaltProblem`
many-one reduces to the failure of inclusion in the language model. -/
def _root_.DiagonaLean.KAComm.ModelLe.synthComplFromHalt :
    HaltProblem ⪯_s Complement ModelLeProblem :=
  ⟨haltRed, halt_reducesto_not_modelLe_spec⟩

end DiagonaLean.KAComm.ModelLe.Reduction
