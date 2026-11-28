/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.AmbigCFG.Reductions.PCP_to_AmbigCFGCode
import DiagonaLean.AmbigCFG.AlphabetLift
import DiagonaLean.PCP.Undecidable
import DiagonaLean.Foundations.Codes.Tactic
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Undecidability of CFG ambiguity

The statements are about grammar codes (`Foundations.Grammar.CFGCode`): a machine reads a finite
description, and `CFGCode.toCFG` is the grammar a code describes. `ambCode`
(`Reductions/PCP_to_AmbigCFGCode.lean`) sends a PCP instance to a grammar code over `α ⊕ ℕ`,
primitive recursively, so with `PCP.fromHaltOver` it gives the halting reduction
`AmbigCFG.codeFromHaltSum`. The lifting along `ambCodeFunctor` (`AlphabetLift.lean`) moves it to
grammar codes over every alphabet with two distinct letters (`AmbigCFG.codeFromHaltOver`). The
synthetic results are in `SynthHardness.lean`.

## Main statements

* `AmbigCFG.codeFromHaltSum`: whether a grammar code over the terminals `α ⊕ ℕ` is ambiguous is
  halting-hard.
* `AmbigCFG.codeFromHaltOver`: a halting reduction, proved computable, over any alphabet with two
  distinct letters.
* `AmbigCFG.Code.haltHard`, `AmbigCFG.Code.not_computablePred`, `AmbigCFG.Code.not_machineDecidable`
  (`halt_results`): over every nontrivial `Primcodable` alphabet, ambiguity of grammar codes is
  halting-hard and undecidable, and no Turing machine decides it under any computable encoding.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
  Theorem 9.20.
-/

namespace DiagonaLean.AmbigCFG

open DiagonaLean.AmbigCFG.Reduction DiagonaLean.AmbigCFG.AlphabetLift
  DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Grammar

variable {α : Type} [DecidableEq α] [Primcodable α]

/-- **Ambiguity of grammar codes is halting-hard**, over the terminals `α ⊕ ℕ` for any alphabet `α`
with two distinct letters: `PCP.fromHaltOver`, then `ambCode` (`pcp_reducesto_ambigCFGCode_spec`,
`ambCode_prim`). -/
def codeFromHaltSum (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction fun c : CFGCode (α ⊕ ℕ) => AmbigCFG.DecisionProblem c.toCFG := by
  haveI : Nonempty α := ⟨b0⟩
  hard_reduce_from (PCP.fromHaltOver b0 b1 hne) with ambCode using pcp_reducesto_ambigCFGCode_spec

end DiagonaLean.AmbigCFG

namespace DiagonaLean.AmbigCFG

open DiagonaLean.AmbigCFG.Reduction DiagonaLean.AmbigCFG.AlphabetLift DiagonaLean.Foundations.Codes
  DiagonaLean.Foundations.Computability DiagonaLean.Foundations.Grammar

variable {α : Type} [Primcodable α] [DecidableEq α]

/-- **Ambiguity of grammar codes is halting-hard over any alphabet with two distinct letters**:
`codeFromHaltSum` over `Bool ⊕ ℕ`, then the lifting along `ambCodeFunctor`, proved computable. -/
def codeFromHaltOver (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction fun c : CFGCode α => AmbigCFG.DecisionProblem c.toCFG := by
  have h : HaltReduction (@CodeProblem (Bool ⊕ ℕ)) := by
    rw [codeProblem_eq]
    exact codeFromHaltSum false true Bool.false_ne_true
  rw [← codeProblem_eq]
  code_lift ambCodeFunctor from h

section
variable [Nontrivial α]

halt_results Code for (fun c : CFGCode α => AmbigCFG.DecisionProblem c.toCFG)
  over_letters from codeFromHaltOver

end

end DiagonaLean.AmbigCFG
