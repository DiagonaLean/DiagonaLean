/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.LangEq.Basic
import DiagonaLean.Foundations.KleeneAlgebra.Race
import DiagonaLean.Foundations.KleeneAlgebra.Separation

@[expose] public section

/-! # `HaltProblem ⪯ₘ` the failure of equality on `L Σ̈`

`haltRed` sends `(M, w)` to an inequality that fails in the language model iff `M` halts on `w`,
and `haltEqRed` turns it into the equality `(e + f, f)`. Equality in the language model is co-r.e.,
so the reduction lands in its complement. `haltEqRedB` substitutes the code `1ⁿ0` for the letter
`n`, which moves the reduction to `Σ = {0, 1}`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

open scoped Computability

namespace DiagonaLean.LangEq.Reduction

open DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing RExp TD FreePreKA Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation

/-- `HaltProblem` many-one reduces to the failure of language equality over `ℕ`. -/
def haltReducesNotLangEq : HaltProblem ⪯ₘ Complement (@LangEq.DecisionProblem ℕ) :=
  ⟨haltEqRed, fun p => (halt_iff_not_modelLe p).trans (not_congr (modelLe_iff_langEq _))⟩

/-- The reduction to language inequality over `{0, 1}`. -/
def haltEqRedB (p : EncodableTM Bool × List Bool) : InstB := sbI (haltEqRed p)

/-- `haltEqRedB` reduces `HaltProblem` to the failure of language equality over `{0, 1}`. -/
theorem halt_reducesto_not_langEq_bool :
    HaltProblem ⪯ₘ[haltEqRedB] Complement LangEqProblem :=
  fun p => (halt_iff_not_modelLe p).trans (not_congr
    ((modelLe_iff_langEq _).trans (pl_sb_eq_iff cd_injective).symm))

/-- `HaltProblem` many-one reduces to the failure of language equality over `{0, 1}`. -/
def haltReducesNotLangEqBool :
    HaltProblem ⪯ₘ Complement LangEqProblem :=
  ⟨haltEqRedB, halt_reducesto_not_langEq_bool⟩

/-- `eqRed` separates `SelfOut true` from `SelfOut false` by equality of languages. -/
def sepReducesLangEq :
    SepReduces (SelfOut true) (SelfOut false) fun i : Inst => pl (mk i.1 : TD ℕ) = pl (mk i.2) :=
  ⟨eqRed, fun _ h => eqVia_eqRed_pos factorL h, fun _ h => eqVia_eqRed_neg factorL h⟩

end DiagonaLean.LangEq.Reduction
