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
one of his. Eve wins when the product reaches zero (`ForceZero`). The problem
(`DecisionProblem`) asks whether Eve can force zero from the identity.
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

/-- Eve can force zero from the identity in the arena `G`. -/
def DecisionProblem (G : Arena) : Prop := ForceZero G 1

end DiagonaLean.MatrixGame
