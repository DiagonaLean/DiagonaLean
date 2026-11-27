/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.MatrixGame.Search
import DiagonaLean.MatMort.Basic
import DiagonaLean.Foundations.Computability.FinsetPrim
import DiagonaLean.Foundations.Computability.IntPrim
import DiagonaLean.Foundations.Computability.MatrixPrim
import DiagonaLean.Synthetic.Definitions
import DiagonaLean.Synthetic.Tactics.ReductionPath

@[expose] public section

/-! # Matrix mortality reduces to the matrix game

`signGame moves` gives Eve the matrices `moves` and Adam the two signs `1` and `-1`. Adam's moves
only change the sign of the product, so Eve can force zero within `n` rounds iff a word of length
at most `n` over `moves` has product zero (`winsWithin_signGame_iff`). So `signGame` many-one
reduces matrix mortality to the matrix game (`matMort_reducesto_matrixGame_spec`,
`MatrixGame.synthFromMatMort`).

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatrixGame.Reduction

open DiagonaLean.MatrixGame DiagonaLean.Synthetic.Definitions

/-- The arena where Eve plays `moves` and Adam plays `1` or `-1`. -/
def signGame (moves : Finset Position) : Arena := (moves, {1, -1})

/-- `signGame` is computable. -/
@[fun_prop] theorem computable_signGame : Computable signGame :=
  Computable.id.pair (Computable.const _)

/-- Against the two signs, a deadline of n rounds is achievable exactly when a word of at
most n generators annihilates the starting position. -/
theorem winsWithin_signGame_iff (moves : Finset Position) (n : ℕ) (p : Position) :
    winsWithin (signGame moves) n p = true ↔
      ∃ w : List Position, w.length ≤ n ∧ (∀ a ∈ w, a ∈ moves) ∧ p * w.prod = 0 := by
  induction n generalizing p with
  | zero => simp [winsWithin]
  | succ n ih =>
    rw [winsWithin, decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨a, ha, next⟩)
      · exact ⟨[], by simp, by simp, by simp⟩
      · obtain ⟨w, hlen, hw, hz⟩ := (ih _).mp (next 1 (by simp [signGame]))
        exact ⟨a :: w, by simpa using hlen, by simpa [signGame] using And.intro ha hw,
          by simpa [mul_assoc] using hz⟩
    · rintro ⟨w, hlen, hw, hz⟩
      cases w with
      | nil => exact Or.inl (by simpa using hz)
      | cons a w =>
        refine Or.inr ⟨a, hw a (by simp), fun b hb => (ih _).mpr ?_⟩
        refine ⟨w, by simpa using hlen, fun x hx => hw x (by simp [hx]), ?_⟩
        have hprod : p * a * w.prod = 0 := by simpa [mul_assoc] using hz
        have hsign : b = 1 ∨ b = -1 := by simpa [signGame] using hb
        rcases hsign with rfl | rfl <;> simp [neg_mul, hprod]

/-- A finite set of matrices is mortal iff Eve wins `signGame` with it. -/
theorem matMort_reducesto_matrixGame_spec :
    MatMort.DecisionProblem ⪯_s[signGame] DecisionProblem := fun moves => by
  unfold DecisionProblem
  rw [forceZero_iff_exists_bound]
  constructor
  · rintro ⟨w, hw, hz⟩
    exact ⟨w.length, (winsWithin_signGame_iff _ _ _).mpr ⟨w, le_rfl, hw, by simpa using hz⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨w, _, hw, hz⟩ := (winsWithin_signGame_iff _ _ _).mp hn
    exact ⟨w, hw, by simpa using hz⟩

/-- The matrix game is displayed as "Matrix-game winner". -/
instance : Synthetic.ReductionChain.ProblemName DecisionProblem :=
  ⟨"Matrix-game winner"⟩

/-- **The reduction.** Matrix mortality many-one reduces to the matrix game through `signGame`. -/
@[undecReduction] def _root_.DiagonaLean.MatrixGame.synthFromMatMort :
    MatMort.DecisionProblem ⪯_s DecisionProblem :=
  ⟨signGame, matMort_reducesto_matrixGame_spec⟩

end DiagonaLean.MatrixGame.Reduction
