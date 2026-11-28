/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KATermEqBool.Reductions.Halt_to_KATermEqBool

@[expose] public section

/-! # Equality on `K Σ̈` over `{0, 1}` is synthetically halting-hard

Provable equality in Kleene algebra with commutativity over `{0, 1}` is synthetically halting-hard
(`KAComm.KATermEqBool.synthFromHalt`), through `reductionB`
(`Reductions/Halt_to_KATermEqBool.lean`), given finite constants that are only known to exist. The
undecidability results are in `Undecidable.lean`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

namespace DiagonaLean.KAComm.KATermEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Synthetic.Definitions

/-- **Provable equality in Kleene algebra with commutativity over `{0, 1}` is synthetically
halting-hard**, given the interpreter constants `B` (`exists_base`) and the race program `C`
(`exists_raceProgB`). These finite constants are only known to exist, since Mathlib's construction
of a program from a `Partrec` function is not executable, so they are arguments rather than computed
here. The statement without them is `not_machineDecidable_kaTermEqBool`. `HaltProblem` many-one
reduces to provable equality in Kleene algebra over `{0, 1}`. -/
def _root_.DiagonaLean.KAComm.KATermEqBool.synthFromHalt (B : Base) (C : Code) (hB : B.Good)
    (hC : RaceProgB true B C) :
    HaltProblem ⪯_s KATermEqBoolProblem :=
  ⟨reductionB B C, halt_reducesto_kaTermEqBool_spec hB hC⟩

end DiagonaLean.KAComm.KATermEqBool.Reduction
