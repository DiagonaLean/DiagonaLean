/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Tactic.DeriveEncodable
import DiagonaLean.Foundations.Computability.ListMachine

@[expose] public section

/-! # Rows of a list machine and their local rule

The row of a configuration of a list machine is the sequence of its cells, left to right, with
the head marked by its state and blanks beyond the right end (`row`). The next row is obtained
cell by cell from the cell and its two neighbours (`localRule`, `row_next`). The tableau of a run
lists its rows, a halting head staying in place (`tab`); it has a halting head iff the machine halts
(`halts_iff_tab`), and row `t` is blank from `n + t` on, `n` the number of cells of the initial
configuration (`tab_blank`).
-/

namespace DiagonaLean.TeamGame

open DiagonaLean.Foundations.Computability.ListMachine

variable {Q Γ : Type}

/-- A cell of a row: a tape symbol, or the head in a state on a tape symbol. -/
inductive Cell (Q Γ : Type) where
  /-- A cell without the head. -/
  | plain (c : Γ)
  /-- The head, in state `q`, on a cell holding `c`. -/
  | head (q : Q) (c : Γ)
  deriving DecidableEq, Encodable

/-- The cells of a configuration, left to right. -/
def cells (k : Cfg Q Γ) : List (Cell Q Γ) :=
  k.l.reverse.map .plain ++ .head k.q k.c :: k.r.map .plain

/-- The row of a configuration: its cells, then blanks. -/
def row (bl : Γ) (k : Cfg Q Γ) (j : ℕ) : Cell Q Γ := (cells k).getD j (.plain bl)

/-- `afterHead q c a` is the cell after a head in state `q` on `c` whose transition is `a`: the
halting head stays, a head that stays writes and changes state, and a head that moves leaves the
written symbol. -/
def afterHead (q : Q) (c : Γ) : Act Q Γ → Cell Q Γ
  | .halt => .head q c
  | .stay q' b => .head q' b
  | .right _ b => .plain b
  | .left _ b => .plain b

/-- The state a head on the left neighbour brings by moving right, if it does. -/
def fromLeft (δ : Q → Γ → Act Q Γ) : Option (Cell Q Γ) → Option Q
  | some (.head q c) =>
    match δ q c with
    | .right q' _ => some q'
    | _ => none
  | _ => none

/-- The state a head on the right neighbour brings by moving left, if it does. -/
def fromRight (δ : Q → Γ → Act Q Γ) : Cell Q Γ → Option Q
  | .head q c =>
    match δ q c with
    | .left q' _ => some q'
    | _ => none
  | _ => none

/-- The local rule: the next value of a cell from its left neighbour (`none` at the left border),
itself and its right neighbour. -/
def localRule (δ : Q → Γ → Act Q Γ) (left : Option (Cell Q Γ)) (mid right : Cell Q Γ) :
    Cell Q Γ :=
  match mid with
  | .head q c => afterHead q c (δ q c)
  | .plain d =>
    match fromLeft δ left with
    | some q' => .head q' d
    | none =>
      match fromRight δ right with
      | some q' => .head q' d
      | none => .plain d

/-- The left neighbour of cell `j` of a row, `none` at the left border. -/
def leftOf (r : ℕ → Cell Q Γ) (j : ℕ) : Option (Cell Q Γ) :=
  if j = 0 then none else some (r (j - 1))

/-- The row after one application of the local rule. -/
def stepRow (δ : Q → Γ → Act Q Γ) (r : ℕ → Cell Q Γ) (j : ℕ) : Cell Q Γ :=
  localRule δ (leftOf r j) (r j) (r (j + 1))

/-! ### Cells of a row -/

variable {bl : Γ}

/-- Left of the head, a row holds the left cells in reverse. -/
theorem row_lt (k : Cfg Q Γ) {j : ℕ} (hj : j < k.l.length) :
    row bl k j = .plain (k.l.reverse[j]'(by simpa using hj)) := by
  have hj' : j < (k.l.reverse.map (Cell.plain (Q := Q))).length := by simpa using hj
  unfold row cells
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hj', List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hj)]
  rfl

/-- The head is at the length of the left cells. -/
theorem row_head (k : Cfg Q Γ) : row bl k k.l.length = .head k.q k.c := by
  simp [row, cells, List.getD_eq_getElem?_getD]

/-- Right of the head, a row holds the right cells, then blanks. -/
theorem row_gt (k : Cfg Q Γ) (i : ℕ) :
    row bl k (k.l.length + 1 + i) = .plain (k.r.getD i bl) := by
  simp only [row, cells, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map, List.length_reverse, show k.l.length + 1 + i - k.l.length = i + 1 by
    omega, List.getElem?_cons_succ, List.getElem?_map]
  cases k.r[i]? <;> simp

/-- A row holds the left cells in reverse, the head, then the right cells and blanks. -/
theorem row_def (k : Cfg Q Γ) (j : ℕ) :
    row bl k j = if j < k.l.length then .plain (k.l.reverse.getD j bl)
      else if j = k.l.length then .head k.q k.c
      else .plain (k.r.getD (j - k.l.length - 1) bl) := by
  split_ifs with h1 h2
  · rw [row_lt k h1, List.getD_eq_getElem _ _ (by simpa using h1)]
  · rw [h2, row_head]
  · obtain ⟨i, rfl⟩ : ∃ i, j = k.l.length + 1 + i := ⟨j - k.l.length - 1, by omega⟩
    rw [row_gt, show k.l.length + 1 + i - k.l.length - 1 = i by omega]

/-- **A step of the machine applies the local rule to every cell of the row.** -/
theorem row_next {δ : Q → Γ → Act Q Γ} {k k' : Cfg Q Γ} (h : next δ bl k = some k') (j : ℕ) :
    row bl k' j = stepRow δ (row bl k) j := by
  obtain ⟨q, l, c, r⟩ := k
  simp only [next] at h
  revert h
  cases hδ : δ q c with
  | halt => simp
  | stay q' b =>
    intro h; cases h
    simp only [stepRow, leftOf, row_def]
    split_ifs <;> simp_all [localRule, afterHead, fromLeft, fromRight]
  | right q' b =>
    intro h; cases h
    simp only [stepRow, leftOf, row_def]
    split_ifs <;> simp_all [localRule, afterHead, fromLeft, fromRight,
      List.getD_eq_getElem?_getD, List.headD_eq_head?_getD]
    all_goals first
      | omega
      | (cases r <;> rfl)
      | rw [show j - (l.length + 1) - 1 + 1 = j - l.length - 1 by omega]
  | left q' b =>
    cases l with
    | nil => simp
    | cons d l =>
      intro h; cases h
      simp only [stepRow, leftOf, row_def]
      split_ifs <;> simp_all [localRule, afterHead, fromLeft, fromRight]
      all_goals first
        | omega
        | rw [show j - l.length - 1 = j - (l.length + 1) - 1 + 1 by omega, List.getElem?_cons_succ]

/-! ### The tableau -/

/-- The configuration after `t` steps from `k`, if the machine is still running. -/
def runCfg (δ : Q → Γ → Act Q Γ) (bl : Γ) (k : Cfg Q Γ) : ℕ → Option (Cfg Q Γ)
  | 0 => some k
  | t + 1 => (runCfg δ bl k t).bind (next δ bl)

/-- Row `t` of the tableau from `k`: the local rule applied `t` times to the row of `k`. -/
def tab (δ : Q → Γ → Act Q Γ) (bl : Γ) (k : Cfg Q Γ) : ℕ → ℕ → Cell Q Γ
  | 0 => row bl k
  | t + 1 => stepRow δ (tab δ bl k t)

/-- `x` is a head whose transition halts. -/
def IsHaltCell (δ : Q → Γ → Act Q Γ) : Cell Q Γ → Prop
  | .head q c => δ q c = .halt
  | .plain _ => False

/-- A cell is a head. -/
def IsHeadCell : Cell Q Γ → Prop
  | .head _ _ => True
  | .plain _ => False

/-- A halting head is a head. -/
theorem isHeadCell_of_isHaltCell {δ : Q → Γ → Act Q Γ} {x : Cell Q Γ} (h : IsHaltCell δ x) :
    IsHeadCell x := by
  cases x <;> simp_all [IsHaltCell, IsHeadCell]

/-- The local rule makes no head from plain cells. -/
theorem stepRow_plain {δ : Q → Γ → Act Q Γ} {r : ℕ → Cell Q Γ} (h : ∀ j, ¬ IsHeadCell (r j))
    (j : ℕ) : ¬ IsHeadCell (stepRow δ r j) := by
  have hp : ∀ i, ∃ d, r i = .plain d := fun i => by
    cases hr : r i with
    | plain d => exact ⟨d, rfl⟩
    | head q c => exact absurd (by simp [hr, IsHeadCell]) (h i)
  obtain ⟨d, hd⟩ := hp j
  obtain ⟨e, he⟩ := hp (j + 1)
  have hl : fromLeft δ (leftOf r j) = none := by
    unfold leftOf
    split_ifs
    · rfl
    · obtain ⟨d', hd'⟩ := hp (j - 1)
      rw [hd']
      rfl
  simp [stepRow, localRule, hd, he, hl, fromRight, IsHeadCell]

/-- Away from the head, every cell of a row is plain. -/
theorem isHeadCell_row {k : Cfg Q Γ} {j : ℕ} (h : IsHeadCell (row bl k j)) : j = k.l.length := by
  rw [row_def] at h
  split_ifs at h with h1 h2
  · exact absurd h id
  · exact h2
  · exact absurd h id

/-- A move left from the left end leaves a row with no head. -/
theorem stepRow_stuck {δ : Q → Γ → Act Q Γ} {k : Cfg Q Γ} (hl : k.l = []) {q' : Q} {b : Γ}
    (hδ : δ k.q k.c = .left q' b) (j : ℕ) : ¬ IsHeadCell (stepRow δ (row bl k) j) := by
  obtain ⟨q, l, c, r⟩ := k
  simp only at hl hδ
  subst hl
  simp only [stepRow, leftOf, row_def]
  split_ifs <;> simp_all [localRule, afterHead, fromLeft, fromRight, IsHeadCell]

/-- **The tableau and the run**: row `t` is the row of the configuration after `t` steps, or the
machine halted at an earlier step, or row `t` has no head. -/
theorem tab_cases (δ : Q → Γ → Act Q Γ) (k₀ : Cfg Q Γ) (t : ℕ) :
    (∃ k, runCfg δ bl k₀ t = some k ∧ tab δ bl k₀ t = row bl k) ∨
      (∃ t' ≤ t, ∃ k, runCfg δ bl k₀ t' = some k ∧ δ k.q k.c = .halt) ∨
      ∀ j, ¬ IsHeadCell (tab δ bl k₀ t j) := by
  induction t with
  | zero => exact Or.inl ⟨k₀, rfl, rfl⟩
  | succ t ih =>
    rcases ih with ⟨k, hk, hr⟩ | ⟨t', ht', k, hk, hh⟩ | hn
    · cases hn : next δ bl k with
      | some k' =>
        refine Or.inl ⟨k', by simp [runCfg, hk, hn], ?_⟩
        funext j
        simp only [tab, hr]
        exact (row_next hn j).symm
      | none =>
        cases hδ : δ k.q k.c with
        | halt => exact Or.inr (Or.inl ⟨t, by omega, k, hk, hδ⟩)
        | stay q' b => simp [next, hδ] at hn
        | right q' b => simp [next, hδ] at hn
        | left q' b =>
          have hl : k.l = [] := by
            cases hl : k.l with
            | nil => rfl
            | cons d l => simp [next, hδ, hl] at hn
          refine Or.inr (Or.inr fun j => ?_)
          simp only [tab, hr]
          exact stepRow_stuck hl hδ j
    · exact Or.inr (Or.inl ⟨t', by omega, k, hk, hh⟩)
    · exact Or.inr (Or.inr fun j => by simp only [tab]; exact stepRow_plain hn j)

/-- A configuration reached after `t` steps is reached by the step relation. -/
theorem reflTransGen_of_runCfg {δ : Q → Γ → Act Q Γ} {k₀ k : Cfg Q Γ} {t : ℕ}
    (h : runCfg δ bl k₀ t = some k) :
    Relation.ReflTransGen (fun a b => next δ bl a = some b) k₀ k := by
  induction t generalizing k with
  | zero => cases h; exact .refl
  | succ t ih =>
    simp only [runCfg, Option.bind_eq_some_iff] at h
    obtain ⟨k', hk', hn⟩ := h
    exact (ih hk').tail hn

/-- A configuration reached by the step relation is reached after some number of steps. -/
theorem exists_runCfg {δ : Q → Γ → Act Q Γ} {k₀ k : Cfg Q Γ}
    (h : Relation.ReflTransGen (fun a b => next δ bl a = some b) k₀ k) :
    ∃ t, runCfg δ bl k₀ t = some k := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hn ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t + 1, by simp [runCfg, ht, hn]⟩

/-- While the machine runs, row `t` of the tableau is the row of its configuration. -/
theorem tab_eq_row {δ : Q → Γ → Act Q Γ} {k₀ k : Cfg Q Γ} {t : ℕ}
    (h : runCfg δ bl k₀ t = some k) : tab δ bl k₀ t = row bl k := by
  induction t generalizing k with
  | zero => cases h; rfl
  | succ t ih =>
    simp only [runCfg, Option.bind_eq_some_iff] at h
    obtain ⟨k', hk', hn⟩ := h
    funext j
    simp only [tab, ih hk']
    exact (row_next hn j).symm

/-- **The machine halts iff some row of the tableau holds a halting head.** -/
theorem halts_iff_tab {δ : Q → Γ → Act Q Γ} {k₀ : Cfg Q Γ} :
    Halts δ bl k₀ ↔ ∃ t j, IsHaltCell δ (tab δ bl k₀ t j) := by
  constructor
  · rintro ⟨k, hrun, hk⟩
    obtain ⟨t, ht⟩ := exists_runCfg hrun
    refine ⟨t, k.l.length, ?_⟩
    rw [tab_eq_row ht, row_head]
    exact hk
  · rintro ⟨t, j, hj⟩
    rcases tab_cases δ k₀ t (bl := bl) with ⟨k, hk, hr⟩ | ⟨t', -, k, hk, hh⟩ | hn
    · rw [hr] at hj
      have hjl : j = k.l.length := isHeadCell_row (isHeadCell_of_isHaltCell hj)
      rw [hjl, row_head] at hj
      exact ⟨k, reflTransGen_of_runCfg hk, hj⟩
    · exact ⟨k, reflTransGen_of_runCfg hk, hh⟩
    · exact absurd (isHeadCell_of_isHaltCell hj) (hn j)

/-- **Row `t` of the tableau is blank from `n + t` on**, where `n` is the number of cells of the
initial configuration. -/
theorem tab_blank {δ : Q → Γ → Act Q Γ} {k₀ : Cfg Q Γ} {t j : ℕ}
    (hj : (cells k₀).length + t ≤ j) : tab δ bl k₀ t j = .plain bl := by
  induction t generalizing j with
  | zero =>
    simp only [tab, row]
    exact List.getD_eq_default _ _ (by omega)
  | succ t ih =>
    have hj0 : j ≠ 0 := by omega
    simp only [tab, stepRow, leftOf, hj0, ↓reduceIte,
      ih (show (cells k₀).length + t ≤ j - 1 by omega),
      ih (show (cells k₀).length + t ≤ j by omega),
      ih (show (cells k₀).length + t ≤ j + 1 by omega)]
    rfl

end DiagonaLean.TeamGame
