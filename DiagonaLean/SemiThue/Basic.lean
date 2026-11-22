/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Grammar.Rewriting

@[expose] public section

/-! # The word problem for string rewriting systems

A string rewriting system (semi-Thue system) over `T` is a list of rules `l → r` between strings
(`Foundations.Grammar.SRS`). Its word problem asks whether `u` rewrites to `v` in some number of
steps (`DecisionProblem`). `ToEmptyProblem` is the special case `v = []`.

## References

* E. L. Post, *Recursive unsolvability of a problem of Thue* (1947)
* A. A. Markov, *On the impossibility of certain algorithms in the theory of associative systems*
  (1947)
-/

namespace DiagonaLean.SemiThue

open DiagonaLean.Foundations.Grammar

variable {T : Type}

/-- The word problem: does `u` rewrite to `v` in the system `R`? -/
def DecisionProblem (x : SRS T × List T × List T) : Prop := x.1.Derives x.2.1 x.2.2

/-- Does `u` rewrite to the empty string in the system `R`? -/
def ToEmptyProblem (x : SRS T × List T) : Prop := x.1.Derives x.2 []

end DiagonaLean.SemiThue
