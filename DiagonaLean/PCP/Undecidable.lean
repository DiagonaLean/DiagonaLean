/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga
-/

import DiagonaLean.PCP.Reductions.Halt_to_PCP
import DiagonaLean.MPCP.MachineLevel

@[expose] public section

/-! # Undecidability of PCP

PCP is undecidable over the fixed alphabet `Ext (Alpha ℕ Bool)` (`undecidablePCP'`), and over
any alphabet with two distinct letters (`undecidablePCP`), by transporting the first result along
`AlphabetLift.pcpAlphabetLift`.

It is not a computable predicate over any nontrivial alphabet (`not_computablePred_pcp`), so no
Turing machine decides it under any computable encoding (`not_machineDecidable_pcp`). This follows
from `MPCP.MachineLevel.not_computablePred_mpcp` along the primitive recursive reductions
`mpcpToPcp` and `liftInstance`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.PCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.MPCP.Reduction DiagonaLean.Halt
  DiagonaLean.Halt.Encoding DiagonaLean.PCP.AlphabetLift DiagonaLean.Synthetic.Notation

/-- **PCP is `Undecidable` over the fixed alphabet `Ext (Alpha ℕ Bool)`.** -/
def undecidablePCP' :
    Undecidable (@DecisionProblem (Ext (Alpha ℕ Bool))) :=
  haltReducesPCP

/-- **PCP is `Undecidable` over any alphabet `α` with two distinct letters `b0`, `b1`.**
Obtained by transporting `undecidablePCP'` along `AlphabetLift.pcpAlphabetLift`. The letters are
arguments rather than taken from `Nontrivial α`, since a definition cannot extract data from a
proof. -/
def undecidablePCP {α : Type} (b0 b1 : α) (hne : b0 ≠ b1) :
    Undecidable (@DecisionProblem α) :=
  undecidabilityFromReducibility undecidablePCP' (AlphabetLift.pcpAlphabetLift b0 b1 hne)

open DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions

/-- MPCP many-one reduces to PCP over the extended alphabet, through `mpcpToPcp`. -/
def mpcpReducesPCP {α : Type} :
    (fun x : Tile α × Stack α => MPCP.DecisionProblem x.1 x.2) ⪯ₘ (@DecisionProblem (Ext α)) :=
  ⟨fun x => mpcpToPcp x.1 x.2, fun x => mpcp_iff_pcp x.1 x.2⟩

/-- PCP over the alphabet `Ext (Alpha ℕ Sym2)` is not a computable predicate. -/
theorem not_computablePred_pcp_ext :
    ¬ ComputablePred (@DecisionProblem (Ext (Alpha ℕ MPCP.Normalize.Sym2))) :=
  not_computablePred_of_reduces mpcpReducesPCP
    (mpcpToPcp_primrec (α := Alpha ℕ MPCP.Normalize.Sym2)).to_comp
    MPCP.MachineLevel.not_computablePred_mpcp

/-- **PCP is not a computable predicate** over any alphabet with two distinct letters. -/
theorem not_computablePred_pcp {α : Type} [Primcodable α] [Nontrivial α] :
    ¬ ComputablePred (@DecisionProblem α) := by
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne α
  exact not_computablePred_of_reduces
    (pcpAlphabetLift (γ₁ := Ext (Alpha ℕ MPCP.Normalize.Sym2)) b0 b1 hne)
    (pcpAlphabetLift_primrec hne).to_comp not_computablePred_pcp_ext

/-- **No Turing machine decides PCP** over any alphabet with two distinct letters, under any
computable encoding of instances as bit strings. -/
theorem not_machineDecidable_pcp {α : Type} [Primcodable α] [Nontrivial α]
    {enc : Stack α → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc (@DecisionProblem α) :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_pcp

end DiagonaLean.PCP.Reduction
