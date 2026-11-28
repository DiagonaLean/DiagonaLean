/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.Reductions.HaltCanon_to_MPCP
import DiagonaLean.MPCP.AlphabetLift
import DiagonaLean.Foundations.Codes.Tactic
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Undecidability of MPCP

`canonInst` (`Reductions/HaltCanon_to_MPCP.lean`) reduces the halting problem on canonical machines
to MPCP over `Alpha ℕ Sym2`, computably, so it gives the halting reduction `MPCP.fromHalt`. Changing
the alphabet along `mpcpFunctor` (`AlphabetLift.lean`) gives a halting reduction over every alphabet
with two distinct letters. The synthetic results are in `SynthHardness.lean`.

## Main statements

* `MPCP.fromHalt`: MPCP over `Alpha ℕ Sym2` is halting-hard.
* `MPCP.fromHaltOver b0 b1 hne`, `MPCP.fromHaltBool`: over any alphabet with two distinct letters.
* `MPCP.haltHard`, `MPCP.not_computablePred`, `MPCP.not_machineDecidable` (`halt_results`): over
  every nontrivial alphabet, MPCP is halting-hard, so it is undecidable, and no Turing machine
  decides it under any computable encoding.
* `mpcp_manyOneEquiv`: MPCP is many-one equivalent over all nontrivial alphabets.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.MPCP

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Computability

/-- **MPCP is halting-hard**, over the alphabet `Alpha ℕ Sym2`: a reduction from the halting problem
on canonical machines, proved computable. -/
def fromHalt : HaltReduction (@MPCP.DecisionProblem (Alpha ℕ Normalize.Sym2)) :=
  ⟨canonInst, canonInst_prim.to_comp, haltCanon_iff_mpcp⟩

/-- **MPCP is halting-hard over any alphabet with two distinct letters**: `fromHalt`, then the
change of alphabet along `mpcpFunctor`, proved computable. -/
def fromHaltOver {α : Type} [Primcodable α] (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction (@MPCP.DecisionProblem α) := by
  code_lift mpcpFunctor from fromHalt

/-- **MPCP over `Bool` is halting-hard.** -/
def fromHaltBool : HaltReduction MPCProblem :=
  fromHaltOver false true Bool.false_ne_true

/-- MPCP over `Bool` is registered as halting-hard, so `hard_reduce_from MPCProblem …` finds it. -/
instance : HaltSource MPCProblem := ⟨fromHaltBool⟩

section
variable {α : Type} [Primcodable α] [Nontrivial α]

halt_results (@MPCP.DecisionProblem α) over_letters from fromHaltOver

end

end DiagonaLean.MPCP

namespace DiagonaLean.MPCP

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

open Foundations.Codes in
/-- **Alphabet invariance of MPCP**: over any two nontrivial `Primcodable` alphabets, MPCP is
many-one equivalent, so every property closed under computable many-one reductions holds over all
of them or none (`ComputablePred.computable_of_manyOneReducible`,
`REPred.of_manyOneReducible`). -/
theorem mpcp_manyOneEquiv {α β : Type} [Primcodable α] [Primcodable β] [Nontrivial α]
    [Nontrivial β] :
    ManyOneEquiv (@MPCP.DecisionProblem α)
      (@MPCP.DecisionProblem β) := by
  code_lift mpcpFunctor

end DiagonaLean.MPCP
