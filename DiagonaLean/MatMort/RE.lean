/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.MatMort.Primrec
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Matrix mortality is recursively enumerable

A finite set of integer `3 × 3` matrices is mortal iff some list of its members has product zero,
and checking a candidate list is primitive recursive in the set and the list. So matrix mortality
is recursively enumerable (`MatMort.rePred`), by a search over lists of matrices
(`REPred.of_exists_primrecPred_witness`).

## Main statements

* `MatMort.rePred`: the mortality problem for `3 × 3` integer matrices is recursively enumerable.
-/

namespace DiagonaLean.MatMort

open Foundations.Computability

/-- **Matrix mortality is recursively enumerable**: search for a product equal to zero. -/
theorem rePred : REPred DecisionProblem :=
  REPred.of_exists_primrecPred_witness
    (q := fun Ms (Ms' : List (Matrix (Fin 3) (Fin 3) ℤ)) => (∀ M ∈ Ms', M ∈ Ms) ∧ Ms'.prod = 0)
    (by fun_prop) fun _ => Iff.rfl

end DiagonaLean.MatMort
