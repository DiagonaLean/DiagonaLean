/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

import DiagonaLean.Foundations.Computability.Normalize.Invariant

@[expose] public section

/-! # The encoded input

The initial tape of the normalised machine on `encInput w` encodes the initial tape of the
simulated machine on `w` (`invAt_init`). `cellAt_encInput_nonneg` and `cellAt_encInput_neg`
compute the cells of that tape at the positions `fold j`.
-/

namespace DiagonaLean.Foundations.Computability.Normalize

open Cslib.Turing SingleTapeTM

/-- `encInput w` is the marker followed by each letter `b` of `w` as `(b, true)`, then `Bl`. -/
theorem encInput_eq (w : List Bool) :
    encInput w = Mk :: w.flatMap (fun b => [(b, true), Bl]) := rfl

/-- Position `2 * k` of the interleaved input holds letter `k` of `w`, paired with `true`. -/
theorem encPairs_even (w : List Bool) (k : ℕ) :
    (w.flatMap (fun b => [(b, true), Bl]))[2 * k]? = (w[k]?).map (fun b => (b, true)) := by
  induction w generalizing k with
  | nil => simp
  | cons b w ih =>
    cases k with
    | zero => simp
    | succ k =>
      have h2 : 2 * (k + 1) = (2 * k) + 1 + 1 := by ring
      simp only [List.flatMap_cons, List.cons_append, h2, List.getElem?_cons_succ]
      simpa using ih k

/-- Position `2 * k + 1` of the interleaved input holds `Bl` if `w` has a letter `k`, and is
empty otherwise. -/
theorem encPairs_odd (w : List Bool) (k : ℕ) :
    (w.flatMap (fun b => [(b, true), Bl]))[2 * k + 1]? = (w[k]?).map (fun _ => Bl) := by
  induction w generalizing k with
  | nil => simp
  | cons b w ih =>
    cases k with
    | zero => simp
    | succ k =>
      have h2 : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by ring
      simp only [List.flatMap_cons, List.cons_append, h2, List.getElem?_cons_succ]
      simpa using ih k

/-- For `j ≥ 0`, cell `fold j` of the initial tape holds letter `j` of `w`, paired with
`true`, and is blank if there is no such letter. -/
theorem cellAt_encInput_nonneg (w : List Bool) {j : ℤ} (hj : 0 ≤ j) :
    cellAt (BiTape.mk₁ (encInput w)) (fold j) = (w[j.toNat]?).map (fun b => (b, true)) := by
  rw [cellAt_mk₁, ite_eq_left (by have := fold_pos j; omega)]
  have hfold : (fold j).toNat = 2 * j.toNat + 1 := by
    rw [fold_of_nonneg hj]; omega
  rw [hfold, encInput_eq]
  simp only [List.getElem?_cons_succ]
  exact encPairs_even w j.toNat

/-- For `j < 0`, cell `fold j` of the initial tape holds `Bl` if `w` has a letter `-j - 1`,
and is blank otherwise. -/
theorem cellAt_encInput_neg (w : List Bool) {j : ℤ} (hj : j < 0) :
    cellAt (BiTape.mk₁ (encInput w)) (fold j) = (w[(-j).toNat - 1]?).map (fun _ => Bl) := by
  rw [cellAt_mk₁, ite_eq_left (by have := fold_pos j; omega)]
  have hm : 1 ≤ (-j).toNat := by omega
  have hfold : (fold j).toNat = 2 * ((-j).toNat - 1) + 1 + 1 := by
    rw [fold_of_neg hj]; omega
  rw [hfold, encInput_eq]
  simp only [List.getElem?_cons_succ]
  exact encPairs_odd w ((-j).toNat - 1)

/-- The initial configuration of the normalised machine encodes the initial configuration of
the simulated machine (with the head still on the marker). -/
theorem invAt_init (w : List Bool) :
    InvAt (BiTape.mk₁ w) 0 (BiTape.mk₁ (encInput w)) 0 where
  data j := by
    rw [sub_zero, sub_zero]
    rcases le_or_gt 0 j with hj | hj
    · rw [cellAt_encInput_nonneg w hj, cellAt_mk₁, ite_eq_left hj]
      cases h : w[j.toNat]? <;> simp [decSym]
    · rw [cellAt_encInput_neg w hj, cellAt_mk₁, ite_eq_right (by omega)]
      cases h : w[(-j).toNat - 1]? <;> simp [decSym, Bl]
  noMk j := by
    rw [sub_zero]
    rcases le_or_gt 0 j with hj | hj
    · rw [cellAt_encInput_nonneg w hj]
      cases h : w[j.toNat]? <;> simp [Mk]
    · rw [cellAt_encInput_neg w hj]
      cases h : w[(-j).toNat - 1]? <;> simp [Mk, Bl]
  marker := by
    rw [neg_zero, cellAt_mk₁, ite_eq_left (le_refl 0)]
    simp [encInput_eq]
  left n hn := by
    rw [sub_zero, cellAt_mk₁, ite_eq_right (by omega)]

end DiagonaLean.Foundations.Computability.Normalize
