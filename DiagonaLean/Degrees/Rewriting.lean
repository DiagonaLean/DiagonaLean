/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.Degrees.Complete

@[expose] public section

/-! # The three rewriting problems have the same degree

The word problem for string rewriting systems, convertibility of SKI terms and β-conversion of
λ-terms are each halting-hard (`SemiThue.haltHard`, `SKIConv.haltHard`, `BetaConv.haltHard`) and
recursively enumerable (`SemiThue.rePred`, `SKIConv.rePred`, `BetaConv.rePred`), so each is complete
for the recursively enumerable problems (`SemiThue.complete`, `SKIConv.complete`,
`BetaConv.complete`, in `Complete.lean`), and the three are many-one equivalent
(`manyOneEquiv_of_complete`). They are not linked by a translation of one rewriting system into
another (the translation of SKI terms into λ-terms does not reflect convertibility,
`tr_not_reflect`); they are linked by having the degree of the halting problem.

## Main statements

* `semiThue_equiv_skiConv`, `skiConv_equiv_betaConv`, `semiThue_equiv_betaConv`: the three are
  many-one equivalent, the word problem over every nontrivial alphabet.

## References

* H. Rogers, *Theory of Recursive Functions and Effective Computability* (1967), Section 7.2
-/

namespace DiagonaLean

open Foundations.Computability

variable {α : Type} [Primcodable α] [Nontrivial α]

namespace Degrees

/-- **The word problem and SKI convertibility are many-one equivalent**, over every nontrivial
alphabet. -/
theorem semiThue_equiv_skiConv :
    ManyOneEquiv (@SemiThue.DecisionProblem α) SKIConv.DecisionProblem :=
  manyOneEquiv_of_complete _ _

/-- **SKI convertibility and β-conversion are many-one equivalent.** -/
theorem skiConv_equiv_betaConv : ManyOneEquiv SKIConv.DecisionProblem BetaConv.DecisionProblem :=
  manyOneEquiv_of_complete _ _

/-- **The word problem and β-conversion are many-one equivalent**, over every nontrivial
alphabet. -/
theorem semiThue_equiv_betaConv :
    ManyOneEquiv (@SemiThue.DecisionProblem α) BetaConv.DecisionProblem :=
  manyOneEquiv_of_complete _ _

end Degrees

end DiagonaLean
