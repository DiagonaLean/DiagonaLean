/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.ModelLe.Basic
import DiagonaLean.Foundations.KleeneAlgebra.Separation

@[expose] public section

/-! # `HaltProblem ⪯ₘ` the failure of inclusion in `L Σ̈`

`haltRed` sends `(M, w)` to the inequality `(init w)_r R_M∗ ≤ Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ_M`, with
letters renamed to their codes. `M` halts on `w` iff this inequality fails in the language model
(`halt_iff_not_modelLe`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

open scoped Computability

namespace DiagonaLean.ModelLe.Reduction

open DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing RExp TD FreePreKA DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation

/-- `HaltProblem` many-one reduces to the failure of language-model inclusion. -/
def haltReducesNotModelLe : HaltProblem ⪯ₘ Complement (@DecisionProblem ℕ) :=
  ⟨haltRed, halt_iff_not_modelLe⟩

end DiagonaLean.ModelLe.Reduction
