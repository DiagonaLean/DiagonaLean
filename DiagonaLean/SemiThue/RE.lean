/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.SemiThue.Basic
import DiagonaLean.Foundations.Grammar.Rewriting
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # The word problem for string rewriting systems is recursively enumerable

A word `u` rewrites to `v` in a system `R` iff some program of the stack machine `srsSys` checks the
derivation (`Foundations.Grammar.derives_iff_checks`), and checking is primitive recursive in the
system, the program and the two words (`StackProof.checks_prim`). So the word problem is recursively
enumerable over every alphabet with a `Primcodable` type and decidable equality
(`SemiThue.rePred`), uniformly in the system. With `SemiThue.haltHard` it is as hard as the halting
problem and no harder.

## Main statements

* `SemiThue.rePred`: the word problem for string rewriting systems is recursively enumerable.
-/

namespace DiagonaLean.SemiThue

open Foundations.Grammar Foundations.Rewriting Foundations.Computability

variable {T : Type} [Primcodable T] [DecidableEq T]

/-- **The word problem is recursively enumerable**: search for a program that checks the
derivation. -/
theorem rePred : REPred (@DecisionProblem T) :=
  REPred.of_exists_primrecPred (q := fun x k => StackProof.Checks srsSys x.1 k (x.2.1, x.2.2))
    ((StackProof.checks_prim srsSys).comp
      (f := fun y : Instance T × ℕ => (y.1.1, y.2, (y.1.2.1, y.1.2.2))) (by fun_prop))
    fun x => derives_iff_checks x.1 x.2.1 x.2.2

end DiagonaLean.SemiThue
