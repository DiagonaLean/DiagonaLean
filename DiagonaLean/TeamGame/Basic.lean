/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Data.List.Basic

@[expose] public section

/-! # Team games with imperfect information

Two players form a team against Nature on a finite game graph (`Game`). In each round both players
choose an action from a finite list at the same time, without seeing each other's actions, and
Nature picks any successor of the current position along an edge labelled with the pair of
actions. Player `i` sees only an observation of each position, so a strategy of player `i` maps
the sequence of its observations to an action. A play is an infinite sequence of positions from
the initial one (`IsPlay`). In the reachability problem the team must make every play visit a
target position (`TeamWinsReach`, `DecisionProblem`); in the safety problem it must make every
play avoid the bad positions (`TeamWinsSafety`, `DecisionProblemSafety`). Strategies must choose
listed actions (`Legal`). Positions, actions and observations are all of one type `α`.

To audit the definitions, read `IsPlay`, `Legal`, `decisionProblem_mk` and
`decisionProblemSafety_mk`; the last two are pinned in `scripts/HeadlineTest.lean`.

## Main definitions

* `Game`, `IsPlay`, `Legal`: games, plays and legal strategies.
* `TeamWinsReach`, `TeamWinsSafety`: the two winning conditions, curried.
* `DecisionProblem`, `DecisionProblemSafety`: the problems on instances `(G, d)`.

## References

* [G. L. Peterson, J. H. Reif, *Multiple-person alternation*][PetersonReif1979]
* [A. Pnueli, R. Rosner, *Distributed reactive systems are hard to synthesize*][PnueliRosner1990]
-/

namespace DiagonaLean.TeamGame

variable {α : Type}

/-- A team game: the initial position, the actions, the edges `(v, a₀, a₁, v')` from `v` to `v'`
when player 0 plays `a₀` and player 1 plays `a₁`, the observations `(v, o₀, o₁)` of the two
players at `v`, and the target (for reachability) or bad (for safety) positions. -/
structure Game (α : Type) where
  /-- The initial position. -/
  init : α
  /-- The actions of the players. -/
  acts : List α
  /-- The edges, labelled by the actions of the two players. -/
  edges : List (α × α × α × α)
  /-- The observations of the two players at each position. -/
  obs : List (α × α × α)
  /-- The target or bad positions. -/
  goal : List α

/-- The observation of player 0 at `v`: the first listed one, or `d` if none is listed. -/
def Game.obs₀ [DecidableEq α] (G : Game α) (d v : α) : α :=
  ((G.obs.find? fun o => o.1 = v).map fun o => o.2.1).getD d

/-- The observation of player 1 at `v`: the first listed one, or `d` if none is listed. -/
def Game.obs₁ [DecidableEq α] (G : Game α) (d v : α) : α :=
  ((G.obs.find? fun o => o.1 = v).map fun o => o.2.2).getD d

/-- The observations of a player along the first `k + 1` positions of a play. -/
def history {β : Type} (o : α → β) (f : ℕ → α) (k : ℕ) : List β :=
  (List.range (k + 1)).map fun j => o (f j)

/-- `f` is a play of `G` in which player 0 follows `σ₀` and player 1 follows `σ₁`: it starts at
the initial position, and each step follows an edge labelled by the actions the strategies choose
from the observations so far. Unlisted observations are `d`. A play that reaches a position with
no edge for the chosen actions cannot continue, so it is no play: the problems quantify only over
plays, so a dead end counts for the team. -/
def IsPlay [DecidableEq α] (G : Game α) (d : α) (σ₀ σ₁ : List α → α) (f : ℕ → α) : Prop :=
  f 0 = G.init ∧ ∀ k, (f k, σ₀ (history (G.obs₀ d) f k), σ₁ (history (G.obs₁ d) f k), f (k + 1))
    ∈ G.edges

/-- The strategies `σ₀` and `σ₁` choose actions of `G`. -/
def Legal (G : Game α) (σ₀ σ₁ : List α → α) : Prop := ∀ h, σ₀ h ∈ G.acts ∧ σ₁ h ∈ G.acts

/-- **The team wins the reachability game** `G`, with the default observation `d` of unlisted
positions: it has legal strategies that make every play visit a goal position. -/
def TeamWinsReach [DecidableEq α] (G : Game α) (d : α) : Prop :=
  ∃ σ₀ σ₁ : List α → α, Legal G σ₀ σ₁ ∧ ∀ f, IsPlay G d σ₀ σ₁ f → ∃ k, f k ∈ G.goal

/-- **The team wins the safety game** `G`, with the default observation `d` of unlisted positions:
it has legal strategies that make every play avoid the goal positions, which are the bad ones. -/
def TeamWinsSafety [DecidableEq α] (G : Game α) (d : α) : Prop :=
  ∃ σ₀ σ₁ : List α → α, Legal G σ₀ σ₁ ∧ ∀ f, IsPlay G d σ₀ σ₁ f → ∀ k, f k ∉ G.goal

/-! ### The problems on instances, for the reductions and the computability statements -/

/-- **Team reachability games on an instance `(G, d)`**: `TeamWinsReach G d`. Read it curried,
`decisionProblem_mk`. -/
def DecisionProblem [DecidableEq α] (x : Game α × α) : Prop := TeamWinsReach x.1 x.2

/-- **Team safety games on an instance `(G, d)`**: `TeamWinsSafety G d`. Read it curried,
`decisionProblemSafety_mk`. -/
def DecisionProblemSafety [DecidableEq α] (x : Game α × α) : Prop := TeamWinsSafety x.1 x.2

/-- The reachability problem on an instance `(G, d)` is the curried problem. -/
@[simp] theorem decisionProblem_mk [DecidableEq α] (G : Game α) (d : α) :
    DecisionProblem (G, d) ↔ TeamWinsReach G d := Iff.rfl

/-- The safety problem on an instance `(G, d)` is the curried problem. -/
@[simp] theorem decisionProblemSafety_mk [DecidableEq α] (G : Game α) (d : α) :
    DecisionProblemSafety (G, d) ↔ TeamWinsSafety G d := Iff.rfl

end DiagonaLean.TeamGame
