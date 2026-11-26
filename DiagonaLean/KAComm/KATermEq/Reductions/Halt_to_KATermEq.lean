/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KATermEq.Basic
import DiagonaLean.KAComm.KleeneAlgebra.Race

@[expose] public section

/-! # `HaltProblem ⪯_s` equality on `K Σ̈`

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
    (hC : RaceProg true B C) : HaltProblem ⪯_s[reduction B C] KATermEqProblem := fun p => by
  simpa [KAComm.KleeneAlgebra.Rel, DecisionProblem] using halt_iff_rel hB hC p

/-- **Provable equality in Kleene algebra with commutativity over `ℕ` is synthetically
halting-hard**, given the interpreter constants `B` (`exists_base`) and the race program `C`
(`exists_raceProg`). These finite constants are only known to exist, since Mathlib's construction of
a program from a `Partrec` function is not executable, so they are arguments rather than computed
here. The statement without them is `not_machineDecidable_kaTermEq`. `HaltProblem` many-one reduces
to provable equality in Kleene algebra with commutativity. -/
def _root_.DiagonaLean.KAComm.KATermEq.synthFromHalt (B : Base) (C : Code) (hB : B.Good)
    (hC : RaceProg true B C) :
    HaltProblem ⪯_s KATermEqProblem :=
  ⟨reduction B C, halt_reducesto_kaTermEq_spec hB hC⟩

/-- The former name of `KAComm.KATermEq.synthFromHalt`. -/
@[deprecated DiagonaLean.KAComm.KATermEq.synthFromHalt (since := "2026-11-23")]
abbrev haltReducesKATermEq := @DiagonaLean.KAComm.KATermEq.synthFromHalt

end DiagonaLean.KAComm.KATermEq.Reduction
