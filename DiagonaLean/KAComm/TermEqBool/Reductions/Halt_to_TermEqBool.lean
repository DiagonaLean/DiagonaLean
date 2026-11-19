/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.TermEqBool.Basic
import DiagonaLean.KAComm.KleeneAlgebra.Race

@[expose] public section

/-! # `HaltProblem ⪯ₘ` equality on `T Σ̈` over `{0, 1}`

`reductionB B C` sends a `HaltProblem` instance `p` to the instance of the race program of `p`, with
each letter `n` replaced by the word `1ⁿ0`. By Smullyan's argument, `p` halts iff the two sides are
provably equal in pre-Kleene algebra with commutativity over `{0, 1}` (`halt_iff_qb`). The constants
`B` and `C` are the interpreter's table and the race program from the recursion theorem.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

open scoped Computability

namespace DiagonaLean.KAComm.TermEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing RExp TD FreePreKA Nat.Partrec
  DiagonaLean.Foundations.Computability DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

/-- `reductionB B C` reduces `HaltProblem` to provable equality in pre-Kleene algebra over
`{0, 1}`. -/
theorem halt_reducesto_termEqBool_spec {B : Base} {C : Code} (hB : B.Good)
    (hC : RaceProgB false B C) : HaltProblem ⪯ₘ[reductionB B C] TermEqBoolProblem := fun p =>
  (halt_iff_qb hB hC p).trans (by
    simpa [QB, KAComm.KleeneAlgebra.Rel, reductionB, DecisionProblem] using equiv_iff_map)

/-- **The reduction.** `HaltProblem` many-one reduces to provable equality in pre-Kleene algebra
over `{0, 1}`. -/
def haltReducesTermEqBool (B : Base) (C : Code) (hB : B.Good) (hC : RaceProgB false B C) :
    HaltProblem ⪯ₘ TermEqBoolProblem :=
  ⟨reductionB B C, halt_reducesto_termEqBool_spec hB hC⟩

end DiagonaLean.KAComm.TermEqBool.Reduction
