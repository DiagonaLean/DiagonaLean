/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KATermEqBool.Basic
import DiagonaLean.KAComm.KleeneAlgebra.Race

@[expose] public section

/-! # `HaltProblem ⪯_s` equality on `K Σ̈` over `{0, 1}`

`reductionB B C` sends a `HaltProblem` instance `p` to the instance of the race program of `p`, with
each letter `n` replaced by the word `1ⁿ0`. By Smullyan's argument, `p` halts iff the two sides are
provably equal in Kleene algebra with commutativity over `{0, 1}` (`halt_iff_qb`). The constants `B`
and `C` are the interpreter's table and the race program from the recursion theorem.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

namespace DiagonaLean.KAComm.KATermEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt

/-- `reductionB B C` reduces `HaltProblem` to provable equality in Kleene algebra over `{0, 1}`. -/
theorem halt_reducesto_kaTermEqBool_spec {B : Base} {C : Code} (hB : B.Good)
    (hC : RaceProgB true B C) : HaltProblem ⪯_s[reductionB B C] KATermEqBoolProblem := fun p =>
  (halt_iff_qb hB hC p).trans (by
    simpa [QB, KAComm.KleeneAlgebra.Rel, reductionB, DecisionProblem] using kaEquiv_iff_map)

/-- **The reduction.** `HaltProblem` many-one reduces to provable equality in Kleene algebra over
`{0, 1}`. -/
def _root_.DiagonaLean.KAComm.KATermEqBool.synthFromHalt (B : Base) (C : Code) (hB : B.Good)
    (hC : RaceProgB true B C) :
    HaltProblem ⪯_s KATermEqBoolProblem :=
  ⟨reductionB B C, halt_reducesto_kaTermEqBool_spec hB hC⟩

/-- The former name of `KAComm.KATermEqBool.synthFromHalt`. -/
@[deprecated DiagonaLean.KAComm.KATermEqBool.synthFromHalt (since := "2026-11-23")]
abbrev haltReducesKATermEqBool := @DiagonaLean.KAComm.KATermEqBool.synthFromHalt

end DiagonaLean.KAComm.KATermEqBool.Reduction
