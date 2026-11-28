/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.EmpCFG.Undecidable
import DiagonaLean.EmpCFG.RE
import DiagonaLean.Foundations.Computability.CoHalt

@[expose] public section

/-! # Emptiness of the intersection of context-free languages is co-halting-hard

Emptiness of the intersection is the complement of non-emptiness, which is halting-hard for
grammar codes over any alphabet with two letters (`EmpCFG.Code.haltHard`) and recursively
enumerable (`EmpCFG.Code.rePred`). So emptiness is co-halting-hard (`EmpCFG.Code.empty_coHaltHard`),
its complement is recursively enumerable (`EmpCFG.Code.empty_coRE`), and it is not recursively
enumerable (`EmpCFG.Code.empty_not_rePred`): it has the degree of the complement of the halting
problem.

## Main statements

* `EmpCFG.Code.empty_coHaltHard`: emptiness of the intersection of grammar codes is co-halting-hard.
* `EmpCFG.Code.empty_coRE`, `EmpCFG.Code.empty_not_rePred`: its complement is recursively
  enumerable, and it is not.
-/

namespace DiagonaLean.EmpCFG.Code

open Foundations.Grammar Foundations.Computability

variable {α : Type} [Primcodable α] [DecidableEq α]

/-- **Emptiness of the intersection of grammar codes is co-halting-hard**, over any alphabet with
two letters. -/
theorem empty_coHaltHard [Nontrivial α] :
    CoHaltHard fun c : CFGCode α × CFGCode α => IntersectionEmpty c.1.toCFG c.2.toCFG := by
  unfold CoHaltHard
  simpa only [not_intersectionEmpty_iff_nonempty] using EmpCFG.Code.haltHard (α := α)

/-- The complement of emptiness of the intersection of grammar codes is recursively enumerable. -/
theorem empty_coRE :
    REPred fun c : CFGCode α × CFGCode α => ¬ IntersectionEmpty c.1.toCFG c.2.toCFG := by
  simpa only [not_intersectionEmpty_iff_nonempty] using EmpCFG.Code.rePred (α := α)

/-- **Emptiness of the intersection of grammar codes is not recursively enumerable**, over any
alphabet with two letters. -/
theorem empty_not_rePred [Nontrivial α] :
    ¬ REPred fun c : CFGCode α × CFGCode α => IntersectionEmpty c.1.toCFG c.2.toCFG :=
  empty_coHaltHard.not_rePred

end DiagonaLean.EmpCFG.Code
