/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga
-/

import DiagonaLean.Foundations.Computability.UndecTransfer
import DiagonaLean.PCP.Primrec
import DiagonaLean.MPCP.Undecidable
import DiagonaLean.PCP.AlphabetLift

@[expose] public section

/-! # Undecidability of PCP

MPCP is halting-hard (`MPCP.fromHalt`), and the reduction `mpcpToPcp` from MPCP to PCP is primitive
recursive (`mpcpToPcp_primrec`), so PCP is halting-hard over `Ext (Alpha ℕ Sym2)` (`PCP.fromHalt`).
The change of alphabet `liftInstance b0 b1` is primitive recursive too (`liftInstance_primrec`), so
PCP is halting-hard over every alphabet with two distinct letters (`PCP.fromHaltOver b0 b1 hne`,
`PCP.fromHaltBool`). So over every nontrivial alphabet PCP is undecidable, and no Turing machine
decides it under any computable encoding.

## Main statements

* `PCP.fromHalt`, `PCP.fromHaltOver`, `PCP.fromHaltBool`: reductions from the halting problem,
  proved computable.
* `PCP.haltHard`, `PCP.not_computablePred`, `PCP.not_machineDecidable` (`halt_results`): over every
  nontrivial alphabet.

The synthetic results are in `SynthHardness.lean`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.PCP

open DiagonaLean.PCP.Reduction DiagonaLean.PCP.AlphabetLift DiagonaLean.MPCP.Reduction
  DiagonaLean.Foundations.Computability

/-- **PCP is halting-hard**, over the alphabet `Ext (Alpha ℕ Sym2)`: `MPCP.fromHalt`, then
`mpcpToPcp` (`mpcp_reducesto_pcp_spec`, `mpcpToPcp_primrec`). -/
def fromHalt : HaltReduction (@PCP.DecisionProblem (Ext (Alpha ℕ Normalize.Sym2))) := by
  hard_reduce_from MPCP.fromHalt with (fun x => mpcpToPcp x.1 x.2) using mpcp_reducesto_pcp_spec

/-- **PCP is halting-hard over any alphabet with two distinct letters**: `fromHalt`, then the
change of alphabet `liftInstance b0 b1` (`pcp_alphabet_lift_spec`, `liftInstance_primrec`). -/
def fromHaltOver {α : Type} [Primcodable α] (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction (@PCP.DecisionProblem α) := by
  hard_reduce_from fromHalt with (liftInstance b0 b1) using (pcp_alphabet_lift_spec b0 b1 hne)

/-- **PCP over `Bool` is halting-hard.** -/
def fromHaltBool : HaltReduction (@PCP.DecisionProblem Bool) :=
  fromHaltOver false true Bool.false_ne_true

/-- PCP over `Bool` is registered as halting-hard. -/
instance : HaltSource (@PCP.DecisionProblem Bool) := ⟨fromHaltBool⟩

section
variable {α : Type} [Primcodable α] [Nontrivial α]

halt_results (@PCP.DecisionProblem α) over_letters from fromHaltOver

attribute [undecHardness] not_computablePred

end

end DiagonaLean.PCP
