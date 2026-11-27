/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.EmpCFG.Reductions.PCP_to_EmpCFGCode
import DiagonaLean.EmpCFG.AlphabetLift
import DiagonaLean.PCP.Undecidable
import DiagonaLean.Foundations.Codes.Tactic
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Undecidability of the non-emptiness of CFG intersection

The statements are about grammar codes (`Foundations.Grammar.CFGCode`): a machine reads a finite
description, and `CFGCode.toCFG` is the grammar a code describes. `empCode`
(`Reductions/PCP_to_EmpCFGCode.lean`) sends a PCP instance to two grammar codes, primitive
recursively, so with `PCP.fromHaltOver` it gives the halting reduction `EmpCFG.codeFromHaltTerm`
over the terminals `Term α`. The lifting along `empCodeFunctor` (`AlphabetLift.lean`) moves it to
grammar codes over every alphabet with two distinct letters (`EmpCFG.codeFromHaltOver`). The
synthetic results, about Mathlib's grammars, are in `SynthHardness.lean`.

## Main statements

* `EmpCFG.codeFromHaltTerm`: whether the languages of two grammar codes over the terminals `Term α`
  intersect is halting-hard.
* `EmpCFG.codeFromHaltOver`, and by `halt_results` `EmpCFG.Code.haltHard`,
  `EmpCFG.Code.not_computablePred`, `EmpCFG.Code.not_machineDecidable`: over every nontrivial
  alphabet.
* `not_computablePred_empCFGCode_empty`, `not_machineDecidable_empCFGCode_empty`: whether they are
  disjoint is undecidable, and no Turing machine decides it under any computable encoding.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace DiagonaLean.EmpCFG

open DiagonaLean.EmpCFG.Reduction DiagonaLean.EmpCFG.AlphabetLift
  DiagonaLean.Foundations.Computability DiagonaLean.Foundations.Grammar

variable {α : Type} [DecidableEq α] [Primcodable α]

/-- **Non-emptiness of the intersection of two grammar codes is halting-hard**, over the terminals
`Term α` for any alphabet `α` with two distinct letters: `PCP.fromHaltOver`, then `empCode`
(`pcp_reducesto_empCFGCode_spec`, `empCode_prim`). -/
def codeFromHaltTerm (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction
      fun c : CFGCode (Term α) × CFGCode (Term α) => IntersectionNonempty c.1.toCFG c.2.toCFG := by
  hard_reduce_from (PCP.fromHaltOver b0 b1 hne) with empCode using pcp_reducesto_empCFGCode_spec

end DiagonaLean.EmpCFG

namespace DiagonaLean.EmpCFG

open DiagonaLean.PCP DiagonaLean.EmpCFG DiagonaLean.EmpCFG.Reduction
  DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

variable {α : Type} [DecidableEq α] [Primcodable α]

/-- **Whether the languages of two grammar codes are disjoint is undecidable**, over
the terminals `Term α` for any alphabet `α` with two distinct letters: the complement of a
halting-hard problem (`EmpCFG.codeFromHaltTerm`). -/
theorem not_computablePred_empCFGCode_empty [Nontrivial α] :
    Undecidable fun c : CFGCode (Term α) × CFGCode (Term α) =>
      IntersectionEmpty c.1.toCFG c.2.toCFG := fun h => by
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne α
  refine (EmpCFG.codeFromHaltTerm b0 b1 hne).not_computablePred ?_
  have := h.not
  simpa [not_intersectionEmpty_iff_nonempty] using this

/-- **No Turing machine decides whether the languages of two grammar codes are disjoint**, under
any computable encoding of pairs of codes as bit strings. -/
theorem not_machineDecidable_empCFGCode_empty [Nontrivial α]
    {enc : CFGCode (Term α) × CFGCode (Term α) → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc fun c => IntersectionEmpty c.1.toCFG c.2.toCFG :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_empCFGCode_empty

end DiagonaLean.EmpCFG

namespace DiagonaLean.EmpCFG

open DiagonaLean.EmpCFG.Reduction DiagonaLean.EmpCFG.AlphabetLift DiagonaLean.Foundations.Codes
  DiagonaLean.Foundations.Computability DiagonaLean.Foundations.Grammar

variable {α : Type} [Primcodable α] [DecidableEq α]

/-- **Non-emptiness of the intersection of two grammar codes is halting-hard over any alphabet with
two distinct letters**: `codeFromHaltTerm` over `Term Bool`, then the lifting along
`empCodeFunctor`, proved computable. -/
def codeFromHaltOver (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction fun c : CFGCode α × CFGCode α => IntersectionNonempty c.1.toCFG c.2.toCFG := by
  have h : HaltReduction (@CodeProblem (Reduction.Term Bool)) := by
    rw [codeProblem_eq]
    exact codeFromHaltTerm false true Bool.false_ne_true
  rw [← codeProblem_eq]
  code_lift empCodeFunctor from h

section
variable [Nontrivial α]

halt_results Code for (fun c : CFGCode α × CFGCode α => IntersectionNonempty c.1.toCFG c.2.toCFG)
  over_letters from codeFromHaltOver

end

end DiagonaLean.EmpCFG
