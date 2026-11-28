/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KATermEq.Reductions.Halt_to_KATermEq

@[expose] public section

/-! # Equality on `K Σ̈` is synthetically halting-hard

Provable equality in Kleene algebra with commutativity over `ℕ` is synthetically halting-hard
(`KAComm.KATermEq.synthFromHalt`), through `reduction` (`Reductions/Halt_to_KATermEq.lean`), given
finite constants that are only known to exist. The undecidability results are in `Undecidable.lean`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

namespace DiagonaLean.KAComm.KATermEq.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Synthetic.Definitions

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

end DiagonaLean.KAComm.KATermEq.Reduction
