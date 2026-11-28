/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.KAComm.KATermEqBool.Reductions.Halt_to_KATermEqBool
import DiagonaLean.Halt.Inseparable
import DiagonaLean.KAComm.KleeneAlgebra.BoolCode
import DiagonaLean.KAComm.KleeneAlgebra.CanonRace
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # From the halting problem on canonical machines to equality on `K Σ̈` over `{0, 1}`

The reduction from canonical machines, `canonReductionB B C`
(`KAComm/KleeneAlgebra/CanonRace.lean`), reduces `HaltCanon` to provable equality in Kleene algebra
with commutativity over `{0, 1}` (`haltCanon_reducesto_spec`), for each choice of the interpreter
constants `B` and the race program `C`. The halting reduction `KAComm.KATermEqBool.fromHaltWith`
built from it is in `Undecidable.lean`.

## Main statements

* `haltCanon_reducesto_spec`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 19
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.KAComm.KATermEqBool

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- `canonReductionB B C` reduces `HaltCanon` to provable equality in Kleene algebra with
commutativity over `{0, 1}`. -/
theorem haltCanon_reducesto_spec {B : Base} {C : Code} (hB : B.Good) (hC : RaceProgB true B C) :
    HaltCanon ⪯_s[canonReductionB B C] KATermEqBoolProblem := fun x =>
  (haltCanon_iff_qb hB hC x).trans (by
    simpa [QB, KAComm.KleeneAlgebra.Rel, canonReductionB, DecisionProblem] using kaEquiv_iff_map)

end DiagonaLean.KAComm.KATermEqBool
