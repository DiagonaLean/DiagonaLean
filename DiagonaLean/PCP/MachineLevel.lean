/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga
-/

import DiagonaLean.PCP.Primrec
import DiagonaLean.MPCP.Hardness

@[expose] public section

/-! # PCP is not a computable predicate

PCP is not a computable predicate over any nontrivial alphabet (`not_computablePred_pcp`), so no
Turing machine decides it under any computable encoding (`not_machineDecidable_pcp`). This follows
from `MPCP.MachineLevel.not_computablePred_mpcp` (`MPCP/Hardness.lean`) along the primitive
recursive reductions `PCP.synthFromMPCP` (`mpcpToPcp_primrec`) and `PCP.synthAlphabetLift`
(`pcpAlphabetLift_primrec`).

The reductions themselves are also proved computable: `PCP.fromMPCP`, and the halting reductions
`PCP.fromHalt` (from `MPCP.fromHalt`), `PCP.fromHaltOver b0 b1 hne` and `PCP.fromHaltBool`.


## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.PCP.MachineLevel

open DiagonaLean.PCP.Reduction DiagonaLean.PCP.AlphabetLift DiagonaLean.MPCP.Reduction
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions

/-- PCP over the alphabet `Ext (Alpha ℕ Sym2)` is not a computable predicate. -/
theorem not_computablePred_pcp_ext :
    ¬ ComputablePred (@DecisionProblem (Ext (Alpha ℕ Normalize.Sym2))) :=
  not_computablePred_of_reduces PCP.synthFromMPCP
    (mpcpToPcp_primrec (α := Alpha ℕ Normalize.Sym2)).to_comp
    MPCP.MachineLevel.not_computablePred_mpcp

/-- **PCP is not a computable predicate** over any alphabet with two distinct letters. -/
theorem not_computablePred_pcp {α : Type} [Primcodable α] [Nontrivial α] :
    ¬ ComputablePred (@DecisionProblem α) := by
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne α
  exact not_computablePred_of_reduces
    (PCP.synthAlphabetLift (γ₁ := Ext (Alpha ℕ Normalize.Sym2)) b0 b1 hne)
    (pcpAlphabetLift_primrec hne).to_comp not_computablePred_pcp_ext

/-- **No Turing machine decides PCP** over any alphabet with two distinct letters, under any
computable encoding of instances as bit strings. -/
theorem not_machineDecidable_pcp {α : Type} [Primcodable α] [Nontrivial α]
    {enc : Stack α → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc (@DecisionProblem α) :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_pcp

end DiagonaLean.PCP.MachineLevel

namespace DiagonaLean.PCP

open DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Computability

/-- **The reduction from MPCP to PCP, proved computable** (`mpcpToPcp_primrec`). -/
def fromMPCP {α : Type} [Primcodable α] :
    @MPCP.DecisionProblem α ⪯ @PCP.DecisionProblem (Ext α) :=
  .ofSynth PCP.synthFromMPCP mpcpToPcp_primrec.to_comp

/-- **PCP is halting-hard**, over the alphabet `Ext (Alpha ℕ Sym2)`: `MPCP.fromHalt`, then
`fromMPCP`. -/
def fromHalt : HaltReduction (@PCP.DecisionProblem (Ext (Alpha ℕ Normalize.Sym2))) := by
  reduce_from MPCP.fromHalt via PCP.synthFromMPCP

/-- **PCP is halting-hard over any alphabet with two distinct letters**: `fromHalt`, then the
change of alphabet `synthAlphabetLift`, proved computable (`liftMap_primrec`). -/
def fromHaltOver {α : Type} [Primcodable α] (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction (@PCP.DecisionProblem α) := by
  reduce_from fromHalt via (PCP.synthAlphabetLift b0 b1 hne)

/-- **PCP over `Bool` is halting-hard.** -/
def fromHaltBool : HaltReduction (@PCP.DecisionProblem Bool) :=
  fromHaltOver false true Bool.false_ne_true

end DiagonaLean.PCP
