/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga, Claude Opus
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic

@[expose] public section

/-! # Zero reachability in an alternating matrix multiplication game

Eve and Adam each have a finite set of `3 × 3` integer matrices (an `Arena`). Play starts at the
identity. In each round Eve right-multiplies the product by one of her matrices, then Adam, who has
seen the whole play, right-multiplies it by one of his. Eve wins if the product reaches zero after
finitely many rounds. The problem asks whether Eve has a winning strategy: a strategy that plays
only her moves and wins against every strategy of Adam that plays only his.

* **Objects.** Positions (`Position`), arenas (`Arena`), histories (`History`, the rounds played
  so far, oldest first) and their products (`histProd`).
* **Strategies and plays.** A strategy for Eve chooses her next move from the history
  (`EveStrategy`), one for Adam his reply from the history and Eve's move (`AdamStrategy`); a
  strategy is legal if it plays only its player's moves (`LegalEve`, `LegalAdam`). Two strategies
  determine a play (`play`), and Eve's strategy wins from `p` if, against every legal strategy of
  Adam, the product of the play started at `p` reaches zero (`WinsFrom`).
* **The question.** `EveWins eve adam`, curried: Eve has a legal strategy that wins from the
  identity; and `DecisionProblem` on an arena, for the reductions and the computability
  statements (`decisionProblem_mk`, by `Iff.rfl`).

When Eve has no move she has no legal strategy, and loses. When Adam has no move he has no legal
strategy, and any legal strategy of Eve wins. The proofs use an equivalent inductive form, the
least set of positions that contains zero and is closed under "some move of Eve after which every
reply of Adam stays in the set" (`ForceZero`, `decisionProblem_iff_forceZero` in `Attractor.lean`).

To audit the definition, read `play`, `WinsFrom`, `EveWins`, `eveWins_iff` and
`decisionProblem_mk`; the last two are pinned in `scripts/HeadlineTest.lean`.

## Main definitions

* `History`, `histProd`, `EveStrategy`, `AdamStrategy`, `LegalEve`, `LegalAdam`, `play`,
  `WinsFrom`: the game.
* `EveWins eve adam`: the problem, curried.
* `DecisionProblem`: the same, on arenas.

## Main statements

* `eveWins_iff`, `decisionProblem_mk`: the problem unfolded, by `Iff.rfl`.

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatrixGame

/-! ### Objects -/

/-- Positions are three-by-three integer matrices. -/
abbrev Position := Matrix (Fin 3) (Fin 3) ℤ

/-- An arena is Eve's and Adam's finite move sets, in that order. -/
abbrev Arena := Finset Position × Finset Position

/-- A history: the rounds played so far, oldest first. A round is Eve's move and Adam's reply. -/
abbrev History := List (Position × Position)

/-- The product of the moves of a history, in the order they were played. -/
def histProd : History → Position
  | [] => 1
  | r :: h => r.1 * r.2 * histProd h

/-! ### Strategies and plays -/

/-- A strategy for Eve: her next move after each history. -/
abbrev EveStrategy := History → Position

/-- A strategy for Adam: his reply to Eve's move after each history. -/
abbrev AdamStrategy := History → Position → Position

/-- Eve's strategy plays only her moves. -/
def LegalEve (G : Arena) (σ : EveStrategy) : Prop := ∀ h, σ h ∈ G.1

/-- Adam's strategy plays only his moves. -/
def LegalAdam (G : Arena) (τ : AdamStrategy) : Prop := ∀ h e, τ h e ∈ G.2

/-- The history of the first `t` rounds of the play of `σ` against `τ`. -/
def play (σ : EveStrategy) (τ : AdamStrategy) : ℕ → History
  | 0 => []
  | t + 1 => play σ τ t ++ [(σ (play σ τ t), τ (play σ τ t) (σ (play σ τ t)))]

/-- Eve's strategy `σ` wins from `p`: against every legal strategy of Adam, the product of the
play, started at `p`, reaches zero. -/
def WinsFrom (G : Arena) (σ : EveStrategy) (p : Position) : Prop :=
  ∀ τ, LegalAdam G τ → ∃ t, p * histProd (play σ τ t) = 0

/-! ### The problem, curried -/

/-- **Does Eve, with the moves `eve` against Adam's `adam`, have a winning strategy?** A legal
strategy that brings the product from the identity to zero against every legal strategy of
Adam. -/
def EveWins (eve adam : Finset Position) : Prop :=
  ∃ σ, LegalEve (eve, adam) σ ∧ WinsFrom (eve, adam) σ 1

/-- The curried problem, unfolded: a legal strategy of Eve that wins from the identity. -/
theorem eveWins_iff (eve adam : Finset Position) :
    EveWins eve adam ↔ ∃ σ, LegalEve (eve, adam) σ ∧ WinsFrom (eve, adam) σ 1 := Iff.rfl

/-! ### The problem on instances, for the reductions and the computability statements -/

/-- **The matrix game on an arena `G`**: `EveWins G.1 G.2`. Read it curried,
`decisionProblem_mk`. -/
def DecisionProblem (G : Arena) : Prop := EveWins G.1 G.2

/-- The problem on an arena `(eve, adam)` is the curried problem. -/
@[simp] theorem decisionProblem_mk (eve adam : Finset Position) :
    DecisionProblem (eve, adam) ↔ EveWins eve adam := Iff.rfl

end DiagonaLean.MatrixGame
