/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.PCP.Primrec
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # PCP is recursively enumerable

A PCP instance is solvable iff some stack of tiles is a solution, and checking a candidate stack
(non-empty, drawn from the instance, with equal concatenations) is primitive recursive in the
instance and the stack (`τ1_primrec`, `τ2_primrec`). So PCP is recursively enumerable over every
alphabet with a `Primcodable` type (`PCP.rePred`), by a search over stacks
(`REPred.of_exists_primrecPred_witness`). With `PCP.haltHard` it is as hard as the halting problem
and no harder.

## Main statements

* `PCP.rePred`: the Post correspondence problem is recursively enumerable.
-/

namespace DiagonaLean.PCP

variable {α : Type} [Primcodable α]

/-- **PCP is recursively enumerable**: search for a solution stack. -/
theorem rePred : REPred (@DecisionProblem α) :=
  REPred.of_exists_primrecPred_witness
    (q := fun P A => A ≠ [] ∧ (∀ t ∈ A, t ∈ P) ∧ τ1 A = τ2 A) (by fun_prop) fun _ => Iff.rfl

end DiagonaLean.PCP
