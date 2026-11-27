/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic

@[expose] public section

/-! # Zero reachability in an alternating matrix multiplication game

Eve and Adam each have a finite set of `3 × 3` integer matrices (an `Arena`). Play starts at the
identity. In each round Eve right-multiplies by one of her matrices, then Adam right-multiplies by
one of his. Eve wins when the product reaches zero (`ForceZero`). The problem asks whether Eve can
force zero from the identity: `EveForcesZero eve adam`, curried, and `DecisionProblem` on an arena,
for the reductions and the computability statements (`decisionProblem_mk`, by `Iff.rfl`).

To audit the definition, read `ForceZero`, `EveForcesZero` and `decisionProblem_mk`; the last is
pinned in `scripts/HeadlineTest.lean`.

## Main definitions

* `ForceZero G p`: Eve can force zero from the position `p` in the arena `G`.
* `EveForcesZero eve adam`: the problem, curried.
* `DecisionProblem`: the same, on arenas.
## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatrixGame

/-- Positions are three-by-three integer matrices. -/
abbrev Position := Matrix (Fin 3) (Fin 3) ℤ

/-- An arena is Eve's and Adam's finite move sets, in that order. -/
abbrev Arena := Finset Position × Finset Position

/-- `ForceZero G p` holds when Eve can force zero from `p`: Eve chooses one move and must win
after every legal reply. Zero is absorbing, so testing for it at round boundaries also detects
hits on Eve's turn. An empty reply set gives Eve the win after a legal move, by the normal-play
convention. -/
inductive ForceZero (G : Arena) : Position → Prop where
  | target : ForceZero G 0
  | move {p : Position} (a : Position) (ha : a ∈ G.1)
      (next : ∀ b ∈ G.2, ForceZero G (p * a * b)) : ForceZero G p

/-! ### The problem, curried -/

/-- **Can Eve, with the moves `eve` against Adam's `adam`, force the product from the identity to
zero?** -/
abbrev EveForcesZero (eve adam : Finset Position) : Prop := ForceZero (eve, adam) 1

/-! ### The problem on instances, for the reductions and the computability statements -/

/-- **The matrix game on an arena `G`**: `EveForcesZero G.1 G.2`. Read it curried,
`decisionProblem_mk`. -/
def DecisionProblem (G : Arena) : Prop := EveForcesZero G.1 G.2

/-- The problem on an arena `(eve, adam)` is the curried problem. -/
@[simp] theorem decisionProblem_mk (eve adam : Finset Position) :
    DecisionProblem (eve, adam) ↔ EveForcesZero eve adam := Iff.rfl

end DiagonaLean.MatrixGame
