/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.TermEqBool.Basic
import DiagonaLean.KAComm.KleeneAlgebra.Race

@[expose] public section

/-! # `HaltProblem ⪯_s` equality on `T Σ̈` over `{0, 1}`

`reductionB B C` sends a `HaltProblem` instance `p` to the instance of the race program of `p`, with
each letter `n` replaced by the word `1ⁿ0`. By Smullyan's argument, `p` halts iff the two sides are
provably equal in pre-Kleene algebra with commutativity over `{0, 1}` (`halt_iff_qb`). The constants
`B` and `C` are the interpreter's table and the race program from the recursion theorem.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

namespace DiagonaLean.KAComm.TermEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt

/-- `reductionB B C` reduces `HaltProblem` to provable equality in pre-Kleene algebra over
`{0, 1}`. -/
theorem halt_reducesto_termEqBool_spec {B : Base} {C : Code} (hB : B.Good)
    (hC : RaceProgB false B C) : HaltProblem ⪯_s[reductionB B C] TermEqBoolProblem := fun p =>
  (halt_iff_qb hB hC p).trans (by
    simpa [QB, KAComm.KleeneAlgebra.Rel, reductionB, DecisionProblem] using equiv_iff_map)

/-- **The reduction.** `HaltProblem` many-one reduces to provable equality in pre-Kleene algebra
over `{0, 1}`. -/
def _root_.DiagonaLean.KAComm.TermEqBool.synthFromHalt (B : Base) (C : Code) (hB : B.Good)
    (hC : RaceProgB false B C) :
    HaltProblem ⪯_s TermEqBoolProblem :=
  ⟨reductionB B C, halt_reducesto_termEqBool_spec hB hC⟩

/-- The former name of `KAComm.TermEqBool.synthFromHalt`. -/
@[deprecated DiagonaLean.KAComm.TermEqBool.synthFromHalt (since := "2026-11-23")]
abbrev haltReducesTermEqBool := @DiagonaLean.KAComm.TermEqBool.synthFromHalt

end DiagonaLean.KAComm.TermEqBool.Reduction
