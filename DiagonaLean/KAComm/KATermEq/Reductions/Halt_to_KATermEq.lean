/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KATermEq.Basic
import DiagonaLean.KAComm.KleeneAlgebra.Race

@[expose] public section

/-! # `HaltProblem ⪯ₘ` equality on `K Σ̈`

`reduction B C` sends a `HaltProblem` instance `p` to the instance (`rInst`) of the race program of
`p` over `ℕ`. By Smullyan's argument, `p` halts iff the two sides are provably equal in Kleene
algebra with commutativity (`halt_iff_rel`). The constants `B` and `C` are the interpreter's table
and the race program from the recursion theorem.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

namespace DiagonaLean.KAComm.KATermEq.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt

/-- `reduction B C` reduces `HaltProblem` to provable equality in Kleene algebra with
commutativity. -/
theorem halt_reducesto_kaTermEq_spec {B : Base} {C : Code} (hB : B.Good)
    (hC : RaceProg true B C) : HaltProblem ⪯ₘ[reduction B C] KATermEqProblem := fun p => by
  simpa [KAComm.KleeneAlgebra.Rel, DecisionProblem] using halt_iff_rel hB hC p

/-- **The reduction.** `HaltProblem` many-one reduces to provable equality in Kleene algebra with
commutativity. -/
def haltReducesKATermEq (B : Base) (C : Code) (hB : B.Good) (hC : RaceProg true B C) :
    HaltProblem ⪯ₘ KATermEqProblem :=
  ⟨reduction B C, halt_reducesto_kaTermEq_spec hB hC⟩

end DiagonaLean.KAComm.KATermEq.Reduction
