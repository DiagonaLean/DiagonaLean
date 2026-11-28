/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.TeamGame.Reductions.Halt_to_TeamGame

@[expose] public section

/-! # Team games with imperfect information are synthetically halting-hard

`TeamGame.synthFromHalt` many-one reduces, through `haltToTeamReach`
(`Reductions/Halt_to_TeamGame.lean`), the halting problem to team reachability games, so deciding
whether two players with private observations have a joint strategy against Nature that reaches a
target is synthetically halting-hard. `TeamGame.synthComplFromHalt` many-one reduces the halting
problem to the complement of team safety games, so deciding whether the team has a joint strategy
that avoids the bad positions is synthetically co-halting-hard.

## Main statements

* `TeamGame.synthFromHalt`: the halting problem reduces to team reachability games.
* `TeamGame.synthComplFromHalt`: the halting problem reduces to the complement of team safety
  games.

## References

* [G. L. Peterson, J. H. Reif, *Multiple-person alternation*][PetersonReif1979]
* [A. Pnueli, R. Rosner, *Distributed reactive systems are hard to synthesize*][PnueliRosner1990]
* D. Berwanger, Ł. Kaiser, *Information tracking in distributed games*, talk at ACTS 2010 (slides)
-/

namespace DiagonaLean.TeamGame.Reduction

open DiagonaLean.Halt DiagonaLean.Synthetic.Definitions

/-- **Team reachability games are synthetically halting-hard**: the halting problem many-one
reduces to them through `haltToTeamReach`. -/
@[undecReduction] def _root_.DiagonaLean.TeamGame.synthFromHalt :
    HaltProblem ⪯_s @DecisionProblem ℕ _ :=
  ⟨haltToTeamReach, halt_reducesto_teamReach_spec⟩

/-- **The complement of team safety games is synthetically halting-hard**: the halting problem
many-one reduces to it through `haltToTeamSafety`. -/
def _root_.DiagonaLean.TeamGame.synthComplFromHalt :
    HaltProblem ⪯_s Complement (@DecisionProblemSafety ℕ _) :=
  ⟨haltToTeamSafety, halt_reducesto_not_teamSafety_spec⟩

end DiagonaLean.TeamGame.Reduction
