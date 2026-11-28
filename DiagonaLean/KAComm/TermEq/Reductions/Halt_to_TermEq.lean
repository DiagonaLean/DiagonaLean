/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.TermEq.Basic
import DiagonaLean.KAComm.KleeneAlgebra.Race

@[expose] public section

/-! # `HaltProblem ⪯_s` equality on `T Σ̈`

`reduction B C` sends a `HaltProblem` instance `p` to the instance (`rInst`) of the race program of
`p` over `ℕ`. By Smullyan's argument, `p` halts iff the two sides are provably equal in pre-Kleene
algebra with commutativity (`halt_iff_rel`). The constants `B` and `C` are the interpreter's table
and the race program from the recursion theorem.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

namespace DiagonaLean.KAComm.TermEq.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt

/-- `reduction B C` reduces `HaltProblem` to provable equality in pre-Kleene algebra with
commutativity. -/
theorem halt_reducesto_termEq_spec {B : Base} {C : Code} (hB : B.Good)
    (hC : RaceProg false B C) : HaltProblem ⪯_s[reduction B C] TermEqProblem := fun p => by
  simpa [KAComm.KleeneAlgebra.Rel, DecisionProblem] using halt_iff_rel hB hC p

end DiagonaLean.KAComm.TermEq.Reduction
