/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.LangEq.Reductions.Halt_to_LangEq

@[expose] public section

/-! # Undecidability of equality on `L Σ̈`

The failure of language equality is `Undecidable` over `ℕ` (`undecidable_not_langEq`) and over
`{0, 1}` (`undecidable_not_langEq_bool`). Language equality separates the computably inseparable
pair `SelfOut true`, `SelfOut false` (`langEq_separated`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

open scoped Computability

namespace DiagonaLean.LangEq.Reduction

open DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing RExp TD FreePreKA Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation

/-- **`Undecidable` for language inequality of two terms.** -/
theorem undecidable_not_langEq :
    Undecidable (Complement (@LangEq.DecisionProblem ℕ)) :=
  ⟨haltReducesNotLangEq⟩

/-- **The failure of language equality over `{0, 1}` is `Undecidable`.** -/
theorem undecidable_not_langEq_bool :
    Undecidable (Complement LangEqProblem) :=
  ⟨haltReducesNotLangEqBool⟩

/-- `eqRed` separates the inseparable pair by equality of the languages of two terms. -/
theorem langEq_separated : InsepUndecidable fun i : Inst => pl (mk i.1 : TD ℕ) = pl (mk i.2) :=
  ⟨sepReducesEqVia factorL⟩

end DiagonaLean.LangEq.Reduction
