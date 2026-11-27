/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Data.Matrix.Mul
import DiagonaLean.MatrixGame.Basic

@[expose] public section

/-! # Bounded search in the matrix game

`winsWithin G n p` checks by exhaustive search whether Eve can force zero from `p` within `n`
rounds. Since the move sets are finite, every winning strategy has a round bound, so Eve can force
zero iff the search succeeds for some bound (`forceZero_iff_exists_bound`).
## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatrixGame

/-- `winsWithin G n p` holds when Eve can force zero from `p` within `n` rounds. -/
def winsWithin (G : Arena) : ℕ → Position → Bool
  | 0, p => decide (p = 0)
  | n + 1, p => decide (p = 0 ∨ ∃ a ∈ G.1, ∀ b ∈ G.2, winsWithin G n (p * a * b) = true)

/-- A win within `n` rounds is a win within any `m ≥ n` rounds. -/
private theorem winsWithin_mono (G : Arena) {n m : ℕ} (hle : n ≤ m) (p : Position)
    (h : winsWithin G n p = true) : winsWithin G m p = true := by
  suffices hs : ∀ n p, winsWithin G n p = true → winsWithin G (n + 1) p = true by
    induction hle with
    | refl => exact h
    | step _ ih => exact hs _ p ih
  intro k
  induction k with
  | zero => intro p hp; simp_all [winsWithin]
  | succ k ih =>
    intro p hp
    rw [winsWithin, decide_eq_true_eq] at hp ⊢
    exact hp.imp_right (fun ⟨a, ha, hnext⟩ => ⟨a, ha, fun b hb => ih _ (hnext b hb)⟩)

/-- The finite move sets give a common round bound for every winning strategy tree. -/
theorem forceZero_iff_exists_bound (G : Arena) (p : Position) :
    ForceZero G p ↔ ∃ n, winsWithin G n p = true := by
  constructor
  · intro h
    induction h with
    | target => exact ⟨0, by simp [winsWithin]⟩
    | @move p a ha _ ih =>
      classical
      let bound (b : Position) := if hb : b ∈ G.2 then (ih b hb).choose else 0
      refine ⟨G.2.sup bound + 1, ?_⟩
      rw [winsWithin, decide_eq_true_eq]
      refine Or.inr ⟨a, ha, fun b hb => ?_⟩
      apply winsWithin_mono G (Finset.le_sup (f := bound) hb)
      simpa [bound, hb] using (ih b hb).choose_spec
  · rintro ⟨n, hn⟩
    induction n generalizing p with
    | zero =>
      have h : p = 0 := by simpa [winsWithin] using hn
      exact h ▸ .target
    | succ n ih =>
      rw [winsWithin, decide_eq_true_eq] at hn
      rcases hn with rfl | ⟨a, ha, hnext⟩
      · exact .target
      · exact .move a ha (fun b hb => ih _ (hnext b hb))

end DiagonaLean.MatrixGame
