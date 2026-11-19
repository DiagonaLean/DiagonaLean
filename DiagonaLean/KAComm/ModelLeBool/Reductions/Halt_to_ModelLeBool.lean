/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.ModelLeBool.Basic
import DiagonaLean.KAComm.KleeneAlgebra.Race
import DiagonaLean.KAComm.KleeneAlgebra.Separation

@[expose] public section

/-! # `HaltProblem ⪯ₘ` the failure of inclusion in `L Σ̈` over `{0, 1}`

`haltRedB` sends `(M, w)` to the inequality of `haltRed` with each letter `n` replaced by the word
`1ⁿ0`. `M` halts on `w` iff the inequality over `ℕ` fails in the language model
(`halt_iff_not_modelLe`), and the substitution preserves and reflects inclusion (`pl_sb_le`,
`pl_le_of_sb`), so the reduction lands in the complement of inclusion over `{0, 1}`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.ModelLeBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions

/-- The inequality of `haltRed p`, with each letter `n` replaced by the word `1ⁿ0`. -/
def haltRedB (p : EncodableTM Bool × List Bool) : InstB := sbI (haltRed p)

/-- `haltRedB` reduces `HaltProblem` to the failure of inclusion in the language model over
`{0, 1}`. -/
theorem halt_reducesto_not_modelLeBool_spec :
    HaltProblem ⪯ₘ[haltRedB] Complement ModelLeBoolProblem :=
  fun p => (halt_iff_not_modelLe p).trans (not_congr ⟨pl_sb_le wordOf, pl_le_of_sb cd_injective⟩)

/-- **The reduction.** `HaltProblem` many-one reduces to the failure of inclusion in the language
model over `{0, 1}`. -/
def haltReducesNotModelLeBool : HaltProblem ⪯ₘ Complement ModelLeBoolProblem :=
  ⟨haltRedB, halt_reducesto_not_modelLeBool_spec⟩

end DiagonaLean.KAComm.ModelLeBool.Reduction
