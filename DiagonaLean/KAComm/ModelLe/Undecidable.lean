/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.ModelLe.Reductions.Halt_to_ModelLe
import DiagonaLean.KAComm.KleeneAlgebra.Between

@[expose] public section

/-! # Undecidability of inclusion in `L Σ̈`

The failure of inclusion of languages over `ℕ` is `Undecidable` (`undecidableNotModelLe`). No Turing
machine decides inclusion of languages under the encoding `encNat` of a pair of expressions as the
binary digits of its code (`not_machineDecidable_modelLe`), or under any encoding that a machine
computes from `encNat` (`not_machineDecidable_modelLe_of_conv`). The machine-level statement is the
case of Theorem 18 where the predicate is inclusion of languages itself
(`not_machineDecidable_between`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

namespace DiagonaLean.KAComm.ModelLe.Reduction

open DiagonaLean.KAComm.KleeneAlgebra Cslib.Turing DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation DiagonaLean.Halt.Undecidable

/-- **The failure of inclusion of languages over `ℕ` is `Undecidable`.** -/
def undecidableNotModelLe : Undecidable (Complement ModelLeProblem) :=
  haltReducesNotModelLe

/-- **No Turing machine decides inclusion of languages over `ℕ`.** -/
theorem not_machineDecidable_modelLe : ¬ MachineDecidable encNat ModelLeProblem :=
  not_machineDecidable_between _ (fun _ h => h.modelLe) fun _ h => h

/-- **No Turing machine decides inclusion of languages over `ℕ`, under any encoding** that a machine
computes from `encNat`. -/
theorem not_machineDecidable_modelLe_of_conv {enc : Inst → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc ModelLeProblem :=
  Halt.Inseparable.not_machineDecidable_of_conv not_machineDecidable_modelLe hR

end DiagonaLean.KAComm.ModelLe.Reduction
