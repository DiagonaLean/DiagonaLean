/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.MPCP.Basic
import DiagonaLean.PCP.Primrec
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # MPCP is recursively enumerable

An MPCP instance `(c, P)` is solvable iff some stack `A` drawn from `c :: P` completes the start
tile `c` to a solution, and checking a candidate stack is primitive recursive in the instance and
the stack (`PCP.τ1_primrec`, `PCP.τ2_primrec`). So MPCP is recursively enumerable over every
alphabet with a `Primcodable` type (`MPCP.rePred`), by a search over stacks
(`REPred.of_exists_primrecPred_witness`). With `MPCP.haltHard` it is as hard as the halting problem
and no harder.

## Main statements

* `MPCP.rePred`: the modified Post correspondence problem is recursively enumerable.
-/

namespace DiagonaLean.MPCP

open DiagonaLean.PCP

variable {α : Type} [Primcodable α]

/-- **MPCP is recursively enumerable**: search for the rest of a solution after the start tile. -/
theorem rePred : REPred (@DecisionProblem α) :=
  REPred.of_exists_primrecPred_witness
    (q := fun x A => (∀ t ∈ A, t ∈ x.1 :: x.2) ∧ x.1.top ++ τ1 A = x.1.bot ++ τ2 A)
    (by fun_prop) fun _ => Iff.rfl

end DiagonaLean.MPCP
