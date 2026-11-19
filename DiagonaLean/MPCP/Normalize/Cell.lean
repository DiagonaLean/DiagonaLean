/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

import Cslib.Foundations.Data.BiTape
import Mathlib.Tactic

@[expose] public section

/-! # Cell-wise view of a `BiTape`

A `BiTape` is a bi-infinite tape. For reasoning about Turing machine simulations it is easier
to view it as a function `ℤ → Option Symbol`, sending an offset relative to the head to the
symbol stored there. `cellAt t d` is the symbol at offset `d`, defined through `stCell`, the
entries of a `StackTape`. The lemmas `cellAt_write`, `cellAt_moveRight`, `cellAt_moveLeft` and
`cellAt_mk₁` describe how `cellAt` interacts with `write`, the moves and `mk₁`.
-/

namespace DiagonaLean.MPCP.Normalize

open Cslib.Turing

variable {S : Type*}

/-- The `n`-th entry of a `StackTape` (blank if beyond the stored prefix). -/
def stCell (l : StackTape S) (n : ℕ) : Option S := (l.toList[n]?).getD none

/-- Every entry of the empty stack tape is blank. -/
@[simp]
theorem stCell_nil (n : ℕ) : stCell (StackTape.nil : StackTape S) n = none := by
  simp [stCell]

/-- Entry `0` of a stack tape is its head. -/
theorem stCell_zero (l : StackTape S) : stCell l 0 = l.head := by
  unfold stCell StackTape.head
  cases l.toList with
  | nil => simp
  | cons a t => simp

/-- Entry `n + 1` of a stack tape is entry `n` of its tail. -/
theorem stCell_succ (l : StackTape S) (n : ℕ) : stCell l (n + 1) = stCell l.tail n := by
  obtain ⟨L, hL⟩ := l
  cases L with
  | nil => simp [stCell, StackTape.tail]
  | cons a t => simp [stCell, StackTape.tail]

/-- Entry `0` of `StackTape.cons o l` is `o`. -/
theorem stCell_cons_zero (o : Option S) (l : StackTape S) : stCell (StackTape.cons o l) 0 = o := by
  rw [stCell_zero, StackTape.head_cons]

/-- Entry `n + 1` of `StackTape.cons o l` is entry `n` of `l`. -/
theorem stCell_cons_succ (o : Option S) (l : StackTape S) (n : ℕ) :
    stCell (StackTape.cons o l) (n + 1) = stCell l n := by
  rw [stCell_succ, StackTape.tail_cons]

/-- If a stack tape stores no symbols, every entry is blank. -/
theorem stCell_eq_none_of_toList_nil {l : StackTape S} (h : l.toList = []) (n : ℕ) :
    stCell l n = none := by
  simp [stCell, h]

/-- Entry `n` of `StackTape.mapSome l` is `l[n]?`. -/
theorem stCell_mapSome (l : List S) (n : ℕ) : stCell (StackTape.mapSome l) n = l[n]? := by
  simp only [stCell, StackTape.mapSome, List.getElem?_map]
  cases l[n]? <;> simp

/-- The symbol at offset `d` from the head of a `BiTape`. -/
def cellAt (t : BiTape S) (d : ℤ) : Option S :=
  if d = 0 then t.head
  else if 0 < d then stCell t.right (d - 1).toNat
  else stCell t.left (-d - 1).toNat

/-- The cell at offset `0` is the head. -/
@[simp]
theorem cellAt_zero (t : BiTape S) : cellAt t 0 = t.head := by simp [cellAt]

/-- For a positive offset `d`, the cell at `d` is entry `d - 1` of the right part. -/
theorem cellAt_pos (t : BiTape S) {d : ℤ} (h : 0 < d) :
    cellAt t d = stCell t.right (d - 1).toNat := by
  rw [cellAt, ite_eq_right (by omega), ite_eq_left h]

/-- For a negative offset `d`, the cell at `d` is entry `-d - 1` of the left part. -/
theorem cellAt_neg (t : BiTape S) {d : ℤ} (h : d < 0) :
    cellAt t d = stCell t.left (-d - 1).toNat := by
  rw [cellAt, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Writing `a` sets the cell at offset `0` to `a` and leaves every other cell unchanged. -/
@[simp]
theorem cellAt_write (t : BiTape S) (a : Option S) (d : ℤ) :
    cellAt (t.write a) d = if d = 0 then a else cellAt t d := by
  unfold cellAt BiTape.write
  split <;> simp_all

/-- After a move right, the cell at offset `d` is the old cell at offset `d + 1`. -/
theorem cellAt_moveRight (t : BiTape S) (d : ℤ) : cellAt t.moveRight d = cellAt t (d + 1) := by
  rcases lt_trichotomy d 0 with h | h | h
  · rcases eq_or_lt_of_le (by omega : d + 1 ≤ 0) with h1 | h1
    · have hd : d = -1 := by omega
      subst hd
      rw [cellAt_neg _ h]
      simp only [BiTape.moveRight]
      norm_num
      rw [stCell_cons_zero]
    · rw [cellAt_neg _ h, cellAt_neg _ h1]
      simp only [BiTape.moveRight]
      have : (-d - 1).toNat = (-(d + 1) - 1).toNat + 1 := by omega
      rw [this, stCell_cons_succ]
  · subst h
    simp only [cellAt_zero, BiTape.moveRight]
    rw [cellAt_pos _ (by omega)]
    simp [stCell_zero]
  · rw [cellAt_pos _ h, cellAt_pos _ (by omega)]
    simp only [BiTape.moveRight]
    have : (d + 1 - 1).toNat = (d - 1).toNat + 1 := by omega
    rw [this, stCell_succ]

/-- After a move left, the cell at offset `d` is the old cell at offset `d - 1`. -/
theorem cellAt_moveLeft (t : BiTape S) (d : ℤ) : cellAt t.moveLeft d = cellAt t (d - 1) := by
  rcases lt_trichotomy d 0 with h | h | h
  · rw [cellAt_neg _ h, cellAt_neg _ (by omega)]
    simp only [BiTape.moveLeft]
    have : (-(d - 1) - 1).toNat = (-d - 1).toNat + 1 := by omega
    rw [this, stCell_succ]
  · subst h
    simp only [cellAt_zero, BiTape.moveLeft]
    rw [cellAt_neg _ (by omega)]
    simp [stCell_zero]
  · rcases eq_or_lt_of_le (by omega : 0 ≤ d - 1) with h1 | h1
    · have hd : d = 1 := by omega
      subst hd
      rw [cellAt_pos _ h]
      simp only [BiTape.moveLeft]
      norm_num
      rw [stCell_cons_zero]
    · rw [cellAt_pos _ h, cellAt_pos _ h1]
      simp only [BiTape.moveLeft]
      have : (d - 1).toNat = (d - 1 - 1).toNat + 1 := by omega
      rw [this, stCell_cons_succ]

/-- Not moving leaves every cell unchanged. -/
@[simp]
theorem cellAt_optionMove_none (t : BiTape S) (d : ℤ) :
    cellAt (t.optionMove none) d = cellAt t d := rfl

/-- After `optionMove` to the left, the cell at offset `d` is the old cell at offset
`d - 1`. -/
theorem cellAt_optionMove_left (t : BiTape S) (d : ℤ) :
    cellAt (t.optionMove (some Turing.Dir.left)) d = cellAt t (d - 1) := cellAt_moveLeft t d

/-- After `optionMove` to the right, the cell at offset `d` is the old cell at offset
`d + 1`. -/
theorem cellAt_optionMove_right (t : BiTape S) (d : ℤ) :
    cellAt (t.optionMove (some Turing.Dir.right)) d = cellAt t (d + 1) := cellAt_moveRight t d

/-- The tape `BiTape.mk₁ l` holds `l[d]?` at each offset `d ≥ 0` and a blank at each negative
offset. -/
theorem cellAt_mk₁ (l : List S) (d : ℤ) :
    cellAt (BiTape.mk₁ l) d = if 0 ≤ d then l[d.toNat]? else none := by
  cases l with
  | nil =>
    simp only [BiTape.mk₁]
    rcases lt_trichotomy d 0 with h | h | h
    · rw [cellAt_neg _ h]; simp [h.not_ge, BiTape.nil]
    · subst h; simp [BiTape.nil]
    · rw [cellAt_pos _ h]; simp [BiTape.nil, h.le]
  | cons a t =>
    simp only [BiTape.mk₁]
    rcases lt_trichotomy d 0 with h | h | h
    · rw [cellAt_neg _ h]; simp [h.not_ge]
    · subst h; simp
    · rw [cellAt_pos _ h, ite_eq_left h.le]
      simp only [stCell_mapSome]
      have : d.toNat = (d - 1).toNat + 1 := by omega
      rw [this]
      simp

/-- If the left part of the tape is empty, every cell to the left of the head is blank. -/
theorem cellAt_eq_none_of_left_nil {t : BiTape S} (h : t.left.toList = []) {d : ℤ} (hd : d < 0) :
    cellAt t d = none := by
  rw [cellAt_neg _ hd, stCell_eq_none_of_toList_nil h]

/-- If a cell to the left of the head is not blank, the left part of the tape is not empty. -/
theorem left_toList_ne_nil {t : BiTape S} {d : ℤ} (hd : d < 0) (h : cellAt t d ≠ none) :
    t.left.toList ≠ [] := fun hnil => h (cellAt_eq_none_of_left_nil hnil hd)

end DiagonaLean.MPCP.Normalize
