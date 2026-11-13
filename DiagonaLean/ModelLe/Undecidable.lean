/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.ModelLe.Reductions.Halt_to_ModelLe

@[expose] public section

/-! # Undecidability of inclusion in `L Σ̈`

The failure of language inclusion is `Undecidable` (`undecidable_not_modelLe`). Language inclusion
separates the computably inseparable pair `SelfOut true`, `SelfOut false`
(`insepUndecidable_modelLe`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

open scoped Computability

namespace DiagonaLean.ModelLe.Reduction

open DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing RExp TD FreePreKA DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation

/-- **Undecidability in the library's sense:** `HaltProblem ⪯ₘ` the complement of language-model
inclusion for KA with commutativity conditions. -/
theorem undecidable_not_modelLe : Undecidable (Complement (@DecisionProblem ℕ)) :=
  ⟨haltReducesNotModelLe⟩

/-- Inclusion in the language model (with commutativity) is undecidable too. -/
theorem insepUndecidable_modelLe : InsepUndecidable (@DecisionProblem ℕ) :=
  insepUndecidable_of_between _ (fun _ h => h.modelLe) fun _ h => h

end DiagonaLean.ModelLe.Reduction
