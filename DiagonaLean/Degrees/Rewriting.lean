/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.SemiThue.Undecidable
import DiagonaLean.SemiThue.RE
import DiagonaLean.SKIConv.Undecidable
import DiagonaLean.SKIConv.RE
import DiagonaLean.BetaConv.Undecidable
import DiagonaLean.BetaConv.RE
import DiagonaLean.Foundations.Computability.HaltComplete

@[expose] public section

/-! # The three rewriting problems have the same degree

The word problem for string rewriting systems, convertibility of SKI terms and β-conversion of
λ-terms are each halting-hard (`SemiThue.haltHard`, `SKIConv.haltHard`, `BetaConv.haltHard`) and
recursively enumerable (`SemiThue.rePred`, `SKIConv.rePred`, `BetaConv.rePred`). The halting problem
is complete for the recursively enumerable problems (`manyOneReducible_haltCanon_of_rePred`), so
each of the three is: every recursively enumerable problem reduces to it, and the three are
many-one equivalent. They are not linked by a translation of one rewriting system into another
(the translation of SKI terms into λ-terms does not reflect convertibility, `tr_not_reflect`); they
are linked by having the degree of the halting problem.

## Main statements

* `SemiThue.complete`, `SKIConv.complete`, `BetaConv.complete`: every recursively enumerable
  problem many-one reduces to each.
* `semiThue_equiv_skiConv`, `skiConv_equiv_betaConv`, `semiThue_equiv_betaConv`: the three are
  many-one equivalent, the word problem over every nontrivial alphabet.

## References

* H. Rogers, *Theory of Recursive Functions and Effective Computability* (1967), Section 7.2
-/

namespace DiagonaLean

open Foundations.Computability

variable {α : Type} [Primcodable α] [DecidableEq α] [Nontrivial α]
  {β : Type*} [Primcodable β] {p : β → Prop}

omit [DecidableEq α] in
/-- **The word problem is complete for the r.e. problems**, over every nontrivial alphabet. -/
theorem SemiThue.complete (hp : REPred p) : ManyOneReducible p (@SemiThue.DecisionProblem α) :=
  .of_rePred_of_haltHard hp SemiThue.haltHard

/-- **SKI convertibility is complete for the r.e. problems.** -/
theorem SKIConv.complete (hp : REPred p) : ManyOneReducible p SKIConv.DecisionProblem :=
  .of_rePred_of_haltHard hp SKIConv.haltHard

/-- **β-conversion is complete for the r.e. problems.** -/
theorem BetaConv.complete (hp : REPred p) : ManyOneReducible p BetaConv.DecisionProblem :=
  .of_rePred_of_haltHard hp BetaConv.haltHard

namespace Degrees

/-- **The word problem and SKI convertibility are many-one equivalent**, over every nontrivial
alphabet. -/
theorem semiThue_equiv_skiConv :
    ManyOneEquiv (@SemiThue.DecisionProblem α) SKIConv.DecisionProblem :=
  manyOneEquiv_of_haltHard_of_rePred SemiThue.haltHard SemiThue.rePred SKIConv.haltHard
    SKIConv.rePred

/-- **SKI convertibility and β-conversion are many-one equivalent.** -/
theorem skiConv_equiv_betaConv : ManyOneEquiv SKIConv.DecisionProblem BetaConv.DecisionProblem :=
  manyOneEquiv_of_haltHard_of_rePred SKIConv.haltHard SKIConv.rePred BetaConv.haltHard
    BetaConv.rePred

/-- **The word problem and β-conversion are many-one equivalent**, over every nontrivial
alphabet. -/
theorem semiThue_equiv_betaConv :
    ManyOneEquiv (@SemiThue.DecisionProblem α) BetaConv.DecisionProblem :=
  manyOneEquiv_of_haltHard_of_rePred SemiThue.haltHard SemiThue.rePred BetaConv.haltHard
    BetaConv.rePred

end Degrees

end DiagonaLean
