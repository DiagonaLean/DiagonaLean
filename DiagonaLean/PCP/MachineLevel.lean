/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga
-/

import DiagonaLean.PCP.Primrec
import DiagonaLean.MPCP.MachineLevel

@[expose] public section

/-! # PCP is not a computable predicate

PCP is not a computable predicate over any nontrivial alphabet (`not_computablePred_pcp`), so no
Turing machine decides it under any computable encoding (`not_machineDecidable_pcp`). This follows
from `MPCP.MachineLevel.not_computablePred_mpcp` along the primitive recursive reductions
`mpcpReducesPCP` (`mpcpToPcp_primrec`) and `pcpAlphabetLift` (`pcpAlphabetLift_primrec`).

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
  not_computablePred_of_reduces mpcpReducesPCP
    (mpcpToPcp_primrec (α := Alpha ℕ Normalize.Sym2)).to_comp
    MPCP.MachineLevel.not_computablePred_mpcp

/-- **PCP is not a computable predicate** over any alphabet with two distinct letters. -/
theorem not_computablePred_pcp {α : Type} [Primcodable α] [Nontrivial α] :
    ¬ ComputablePred (@DecisionProblem α) := by
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne α
  exact not_computablePred_of_reduces
    (pcpAlphabetLift (γ₁ := Ext (Alpha ℕ Normalize.Sym2)) b0 b1 hne)
    (pcpAlphabetLift_primrec hne).to_comp not_computablePred_pcp_ext

/-- **No Turing machine decides PCP** over any alphabet with two distinct letters, under any
computable encoding of instances as bit strings. -/
theorem not_machineDecidable_pcp {α : Type} [Primcodable α] [Nontrivial α]
    {enc : Stack α → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc (@DecisionProblem α) :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_pcp

end DiagonaLean.PCP.MachineLevel
