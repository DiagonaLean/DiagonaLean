/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.TermEqBool.Reductions.Halt_to_TermEqBool
import DiagonaLean.Halt.Inseparable
import DiagonaLean.KAComm.KleeneAlgebra.BoolCode
import DiagonaLean.KAComm.TermEqBool.Reductions.HaltCanon_to_TermEqBool
import DiagonaLean.Foundations.Computability.HaltResults
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # Undecidability of equality on `T Σ̈` over `{0, 1}`

The reduction from canonical machines, `canonReductionB B C` (`KAComm/KleeneAlgebra/CanonRace.lean`,
correct by `haltCanon_reducesto_spec` in `Reductions/HaltCanon_to_TermEqBool.lean`), is proved
computable, so `KAComm.TermEqBool.fromHaltWith B C …` is a proved halting reduction to provable
equality in pre-Kleene algebra with commutativity over `{0, 1}`, for each choice of the interpreter
constants `B` and the race program `C`. These exist only classically, so halting-hardness, a
proposition, obtains them in its proof (`KAComm.TermEqBool.haltHard`); the problem is undecidable
(`KAComm.TermEqBool.not_computablePred`) and no machine decides it under any computable encoding
(`KAComm.TermEqBool.not_machineDecidable`).

Independently, no Turing machine decides it under the encoding `encBool` of a pair of expressions as
the binary digits of its code (`not_machineDecidable_termEqBool`), or under any encoding that a
machine computes from `encBool` (`not_machineDecidable_termEqBool_of_conv`). The synthetic result is
in `SynthHardness.lean`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.KAComm.TermEqBool.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions DiagonaLean.Halt.Undecidable

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `{0, 1}`.** -/
theorem not_machineDecidable_termEqBool : ¬ MachineDecidable encBool TermEqBoolProblem :=
  not_machineDecidable_of_family (ka := false) instCodeB instCodeB_prim
    (fun K l => sbI (rInst K l)) enc_bool iff_bool (fun _ _ h => pos_bool h)
    (fun _ _ h => neg_bool h)

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `{0, 1}`, under any
encoding** that a machine computes from `encBool`. -/
theorem not_machineDecidable_termEqBool_of_conv {enc : InstB → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encBool enc id) :
    ¬ MachineDecidable enc TermEqBoolProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_termEqBool hR

end DiagonaLean.KAComm.TermEqBool.Reduction

namespace DiagonaLean.KAComm.TermEqBool

open DiagonaLean.KAComm.KleeneAlgebra Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- **A proved halting reduction**, given the interpreter constants `B` and the race program `C`. -/
def fromHaltWith (B : Base) (C : Code) (hB : B.Good) (hC : RaceProgB false B C) :
    HaltReduction TermEqBoolProblem :=
  ⟨canonReductionB B C, (canonReductionB_prim B C).to_comp, haltCanon_reducesto_spec hB hC⟩

-- Halting-hardness and its consequences: the interpreter constants and the race program exist
-- (`exists_base`, `exists_raceProgB`), so the proof obtains them, and only the existence of a
-- reduction is stated.
halt_results TermEqBoolProblem from
  exists_base.elim fun B hB => (exists_raceProgB false B).elim fun C hC =>
    ⟨fromHaltWith B C hB hC⟩

end DiagonaLean.KAComm.TermEqBool
