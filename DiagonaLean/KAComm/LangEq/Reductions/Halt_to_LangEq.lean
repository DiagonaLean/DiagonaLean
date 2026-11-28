/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.LangEq.Basic
import DiagonaLean.KAComm.KleeneAlgebra.Separation

@[expose] public section

/-! # `HaltProblem ⪯_s` the failure of equality on `L Σ̈`

`haltRed` sends `(M, w)` to an inequality that fails in the language model iff `M` halts on `w`, and
`haltEqRed` turns it into the equality `(e + f, f)`. Equality in the language model is co-r.e., so
the reduction lands in its complement.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.LangEq.Reduction

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Halt DiagonaLean.Synthetic.Definitions

/-- `haltEqRed` reduces `HaltProblem` to the failure of language equality over `ℕ`. -/
theorem halt_reducesto_not_langEq_spec :
    HaltProblem ⪯_s[haltEqRed] Complement LangEqProblem :=
  fun p => (halt_iff_not_modelLe p).trans (not_congr (modelLe_iff_langEq _))

end DiagonaLean.KAComm.LangEq.Reduction
