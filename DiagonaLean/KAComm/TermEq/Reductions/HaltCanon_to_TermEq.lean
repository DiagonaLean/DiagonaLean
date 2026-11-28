/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.KAComm.TermEq.Reductions.Halt_to_TermEq
import DiagonaLean.KAComm.KleeneAlgebra.Separation
import DiagonaLean.KAComm.KleeneAlgebra.RExpPrimcodable
import DiagonaLean.KAComm.KleeneAlgebra.CanonRace
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # From the halting problem on canonical machines to equality on `T Σ̈`

The reduction from canonical machines, `canonReduction B C` (`KAComm/KleeneAlgebra/CanonRace.lean`),
reduces `HaltCanon` to provable equality in pre-Kleene algebra with commutativity over `ℕ`
(`haltCanon_reducesto_spec`), for each choice of the interpreter constants `B` and the race program
`C`. The halting reduction `KAComm.TermEq.fromHaltWith` built from it is in `Undecidable.lean`.

## Main statements

* `haltCanon_reducesto_spec`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 19
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.KAComm.TermEq

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- `canonReduction B C` reduces `HaltCanon` to provable equality in pre-Kleene algebra with
commutativity over `ℕ`. -/
theorem haltCanon_reducesto_spec {B : Base} {C : Code} (hB : B.Good) (hC : RaceProg false B C) :
    HaltCanon ⪯_s[canonReduction B C] TermEqProblem := fun x => by
  simpa [KAComm.KleeneAlgebra.Rel, DecisionProblem] using haltCanon_iff_rel hB hC x

end DiagonaLean.KAComm.TermEq
