/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.LangEqBool.Basic
import DiagonaLean.KAComm.KleeneAlgebra.Race
import DiagonaLean.KAComm.KleeneAlgebra.Separation

@[expose] public section

/-! # `HaltProblem ⪯_s` the failure of equality on `L Σ̈` over `{0, 1}`

`haltEqRedB` sends `(M, w)` to the equality of `haltEqRed` with each letter `n` replaced by the word
`1ⁿ0`. An injective substitution preserves and reflects language equality (`pl_sb_eq_iff`), so the
reduction lands in the complement of equality over `{0, 1}`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.LangEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions

/-- The equality of `haltEqRed p`, with each letter `n` replaced by the word `1ⁿ0`. -/
def haltEqRedB (p : EncodableTM Bool × List Bool) : InstB := sbI (haltEqRed p)

/-- `haltEqRedB` reduces `HaltProblem` to the failure of language equality over `{0, 1}`. -/
theorem halt_reducesto_not_langEqBool_spec :
    HaltProblem ⪯_s[haltEqRedB] Complement LangEqBoolProblem :=
  fun p => (halt_iff_not_modelLe p).trans (not_congr
    ((modelLe_iff_langEq _).trans (pl_sb_eq_iff cd_injective).symm))

/-- **The failure of equality of languages over `{0, 1}` is synthetically halting-hard.**
`HaltProblem` many-one reduces to the failure of language equality over `{0, 1}`. -/
def _root_.DiagonaLean.KAComm.LangEqBool.synthComplFromHalt :
    HaltProblem ⪯_s Complement LangEqBoolProblem :=
  ⟨haltEqRedB, halt_reducesto_not_langEqBool_spec⟩

end DiagonaLean.KAComm.LangEqBool.Reduction
