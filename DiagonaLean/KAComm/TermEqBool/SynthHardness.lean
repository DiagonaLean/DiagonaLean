/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.TermEqBool.Reductions.Halt_to_TermEqBool

@[expose] public section

/-! # Equality on `T Σ̈` over `{0, 1}` is synthetically halting-hard

Provable equality in pre-Kleene algebra with commutativity over `{0, 1}` is synthetically
halting-hard (`KAComm.TermEqBool.synthFromHalt`), through `reductionB`
(`Reductions/Halt_to_TermEqBool.lean`), given finite constants that are only known to exist. The
undecidability results are in `Undecidable.lean`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

namespace DiagonaLean.KAComm.TermEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Synthetic.Definitions

/-- **Provable equality in pre-Kleene algebra with commutativity over `{0, 1}` is synthetically
halting-hard**, given the interpreter constants `B` (`exists_base`) and the race program `C`
(`exists_raceProgB`). These finite constants are only known to exist, since Mathlib's construction
of a program from a `Partrec` function is not executable, so they are arguments rather than computed
here. The statement without them is `not_machineDecidable_termEqBool`. `HaltProblem` many-one
reduces to provable equality in pre-Kleene algebra over `{0, 1}`. -/
def _root_.DiagonaLean.KAComm.TermEqBool.synthFromHalt (B : Base) (C : Code) (hB : B.Good)
    (hC : RaceProgB false B C) :
    HaltProblem ⪯_s TermEqBoolProblem :=
  ⟨reductionB B C, halt_reducesto_termEqBool_spec hB hC⟩

end DiagonaLean.KAComm.TermEqBool.Reduction
