/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.LangEq.Basic
import DiagonaLean.KAComm.KleeneAlgebra.Separation

@[expose] public section

/-! # `HaltProblem ⪯ₘ` the failure of equality on `L Σ̈`

`haltRed` sends `(M, w)` to an inequality that fails in the language model iff `M` halts on `w`, and
`haltEqRed` turns it into the equality `(e + f, f)`. Equality in the language model is co-r.e., so
the reduction lands in its complement.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

open scoped Computability

namespace DiagonaLean.KAComm.LangEq.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing RExp TD FreePreKA
  DiagonaLean.Foundations.Computability DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

/-- `haltEqRed` reduces `HaltProblem` to the failure of language equality over `ℕ`. -/
theorem halt_reducesto_not_langEq_spec :
    HaltProblem ⪯ₘ[haltEqRed] Complement LangEqProblem :=
  fun p => (halt_iff_not_modelLe p).trans (not_congr (modelLe_iff_langEq _))

/-- **The reduction.** `HaltProblem` many-one reduces to the failure of language equality over
`ℕ`. -/
def haltReducesNotLangEq : HaltProblem ⪯ₘ Complement LangEqProblem :=
  ⟨haltEqRed, halt_reducesto_not_langEq_spec⟩

end DiagonaLean.KAComm.LangEq.Reduction
