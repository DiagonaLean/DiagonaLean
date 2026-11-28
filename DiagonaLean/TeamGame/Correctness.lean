/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.TeamGame.Construction

@[expose] public section

/-! # Correctness of the game of a list machine

A player's history is all `false` until its trigger round, then `true`, then `false` again
(`trig`). Its output after a trigger at round `m` is therefore the stream `j ↦ σ (trig m j)`, the
same in every check that triggers it at round `m`. This file collects the facts about plays used
to prove that the team wins the reachability variant iff the machine halts, and the safety
variant iff it does not.
-/

namespace DiagonaLean.TeamGame

open DiagonaLean.Foundations.Computability.ListMachine

variable {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-! ### Histories -/

/-- The history of a player triggered at round `m`, `j` rounds after the trigger. -/
def trig (m j : ℕ) : List Bool := List.replicate m false ++ true :: List.replicate j false

/-- The observations along the first `m + j + 1` rounds are `trig m j` when the trigger is at
round `m` only. -/
theorem range_map_eq_trig {g : ℕ → Bool} {m j : ℕ} (hb : ∀ i < m, g i = false) (hm : g m = true)
    (ha : ∀ i, m < i → i ≤ m + j → g i = false) :
    (List.range (m + j + 1)).map g = trig m j := by
  induction j with
  | zero =>
    rw [Nat.add_zero, List.range_succ, List.map_append, trig, List.replicate_zero]
    congr 1
    · rw [List.eq_replicate_iff]
      refine ⟨by simp, fun b hb' => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb'
      exact hb i (List.mem_range.1 hi)
    · simp [hm]
  | succ j ih =>
    rw [show m + (j + 1) + 1 = m + j + 1 + 1 by omega, List.range_succ, List.map_append,
      ih fun i h1 h2 => ha i h1 (by omega), trig, trig, List.replicate_succ']
    simp [ha (m + j + 1) (by omega) (by omega)]

/-- The observations along the first `k + 1` rounds are all `false` when there is no trigger. -/
theorem range_map_eq_replicate {g : ℕ → Bool} {k : ℕ} (h : ∀ i ≤ k, g i = false) :
    (List.range (k + 1)).map g = List.replicate (k + 1) false := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp, fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
  exact h i (by have := List.mem_range.1 hi; omega)

/-- The trigger round and the rounds since, read off a history. -/
def decodeTrig (h : List Bool) : Option (ℕ × ℕ) :=
  let m := (h.takeWhile (· == false)).length
  if h.drop m = true :: List.replicate (h.length - m - 1) false then some (m, h.length - m - 1)
  else none

/-- `decodeTrig` reads the trigger round and the rounds since from `trig`. -/
theorem decodeTrig_trig (m j : ℕ) : decodeTrig (trig m j) = some (m, j) := by
  simp [decodeTrig, trig]

/-- A history with no trigger has no decoding. -/
theorem decodeTrig_replicate (k : ℕ) : decodeTrig (List.replicate k false) = none := by
  simp [decodeTrig, List.drop_replicate]

/-! ### Checks as functions of the outputs -/

section Checks

variable (δ : Q → Γ → Act Q Γ) (bl : Γ) (c₀ : List (Cell Q Γ)) (var : Variant)

/-- One step of a check: a sink stays, an output halting head in the safety variant leads to `hlt`,
and otherwise the check moves on. -/
def stepC (p : Pos Q Γ) (a₀ a₁ : Move Q Γ) : Pos Q Γ :=
  if isSink p then p
  else if var = .safety && (haltMove δ a₀ || haltMove δ a₁) then .hlt
  else chk δ bl c₀ p a₀ a₁

/-- The positions of a check from `p`, when the players' moves are the streams `A₀` and `A₁`. -/
def chkRun (p : Pos Q Γ) (A₀ A₁ : ℕ → Move Q Γ) : ℕ → Pos Q Γ
  | 0 => p
  | j + 1 => stepC δ bl c₀ var (chkRun p A₀ A₁ j) (A₀ j) (A₁ j)

/-- The moves of a player outputting the row `w`: its cells, then `fin`, then nothing. -/
def rowMove (w : List (Cell Q Γ)) (j : ℕ) : Move Q Γ :=
  if h : j < w.length then .out w[j] else if j = w.length then .fin else .idle

/-- A row has a halting head, as a test. -/
def hasHalt (w : List (Cell Q Γ)) : Bool := w.any (isHaltCellB δ)

/-- A sink stays put along a check. -/
theorem chkRun_sink {p : Pos Q Γ} {A₀ A₁ : ℕ → Move Q Γ} {j : ℕ}
    (h : isSink (chkRun δ bl c₀ var p A₀ A₁ j)) (i : ℕ) :
    chkRun δ bl c₀ var p A₀ A₁ (j + i) = chkRun δ bl c₀ var p A₀ A₁ j := by
  induction i with
  | zero => rfl
  | succ i ih => simp [chkRun, stepC, ih, h]

/-- The Eq check moves on when both players output the same cell. -/
theorem chk_eq_out (f s seen : Bool) (x : Cell Q Γ) :
    chk δ bl c₀ (.eq f s seen) (.out x) (.out x) = .eq false s (seen || isHaltCellB δ x) := by
  show (if x = x then _ else _) = _
  simp

/-- The Eq check ends when both players output `fin`. -/
theorem chk_eq_fin (f s seen : Bool) :
    chk δ bl c₀ (.eq f s seen) .fin .fin = if s && !seen then .err else .ok := rfl

omit [DecidableEq Q] [DecidableEq Γ] in
/-- The first `j + 1` cells of a row have a halting head iff the first `j` cells have one or cell
`j` is one. -/
theorem hasHalt_take_succ {w : List (Cell Q Γ)} {j : ℕ} (hj : j < w.length) :
    hasHalt δ (w.take (j + 1)) = (hasHalt δ (w.take j) || isHaltCellB δ w[j]) := by
  unfold hasHalt
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.any_append]
  simp

omit [DecidableEq Q] [DecidableEq Γ] in
/-- A row without halting heads makes no halting move. -/
theorem haltMove_rowMove {w : List (Cell Q Γ)} (h : hasHalt δ w = false) (j : ℕ) :
    haltMove δ (rowMove w j) = false := by
  unfold rowMove
  split_ifs with hj
  · simp only [hasHalt, List.any_eq_false] at h
    simpa [haltMove] using h w[j] (List.getElem_mem hj)
  · rfl
  · rfl

/-- The Eq check on equal outputs of a row: after `j` cells it is still running, with `seen`
recording a halting head among them, when in the safety variant these cells have none. -/
theorem chkRun_eq_prefix {w : List (Cell Q Γ)} {s : Bool} {j : ℕ} (hj : j ≤ w.length)
    (hs : var = .safety → hasHalt δ (w.take j) = false) :
    chkRun δ bl c₀ var (.eq true s false) (rowMove w) (rowMove w) j =
      .eq (j == 0) s (hasHalt δ (w.take j)) := by
  induction j with
  | zero => simp [chkRun, hasHalt]
  | succ j ih =>
    have hjw : j < w.length := by omega
    have hm : rowMove w j = .out w[j] := by simp [rowMove, hjw]
    have hs' : var = .safety → hasHalt δ (w.take j) = false ∧ isHaltCellB δ w[j] = false :=
      fun hv => by simpa [hasHalt_take_succ δ hjw] using hs hv
    have hno :
        (var = .safety && (haltMove δ (rowMove w j) || haltMove δ (rowMove w j))) = false := by
      rcases hv : var with _ | _
      · simp [hm, haltMove, (hs' hv).2]
      · rfl
    rw [chkRun, ih (by omega) fun hv => (hs' hv).1, stepC]
    simp only [isSink, hno, Bool.false_eq_true, ↓reduceIte]
    rw [hm, chk_eq_out, hasHalt_take_succ δ hjw]
    simp

/-- The Eq check passes on equal outputs of a row, when the row has no halting head in the safety
variant and has one in stop mode. -/
theorem chkRun_eq_ok {w : List (Cell Q Γ)} {s : Bool} (hs : var = .safety → hasHalt δ w = false)
    (hstop : s = true → hasHalt δ w = true) :
    chkRun δ bl c₀ var (.eq true s false) (rowMove w) (rowMove w) (w.length + 1) = .ok := by
  rw [chkRun, chkRun_eq_prefix δ bl c₀ var le_rfl (by simpa using hs), List.take_length, stepC]
  have hf : rowMove w w.length = (.fin : Move Q Γ) := by simp [rowMove]
  simp only [isSink, hf, haltMove, Bool.or_false, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte, chk_eq_fin]
  cases s <;> simp_all

/-- The Eq check fails unless both players output the same cell or both end. -/
theorem chk_eq_err {f s seen : Bool} {a₀ a₁ : Move Q Γ}
    (h : ¬ ((∃ x, a₀ = .out x ∧ a₁ = .out x) ∨ (a₀ = .fin ∧ a₁ = .fin))) :
    chk δ bl c₀ (.eq f s seen) a₀ a₁ = .err := by
  rcases a₀ with x | _ | _ | _ <;> rcases a₁ with y | _ | _ | _ <;> simp_all [chk, eq_comm]

/-- **The Eq check, read backwards**: if it never fails, the two players output the same cells,
until both end. -/
theorem eq_of_chkRun {A₀ A₁ : ℕ → Move Q Γ} {s : Bool}
    (h : ∀ j, chkRun δ bl c₀ var (.eq true s false) A₀ A₁ j ≠ .err ∧
      chkRun δ bl c₀ var (.eq true s false) A₀ A₁ j ≠ .hlt) :
    ∀ j, (∀ i < j, A₀ i ≠ .fin) →
      ((∃ x, A₀ j = .out x ∧ A₁ j = .out x) ∨ (A₀ j = .fin ∧ A₁ j = .fin)) := by
  have key : ∀ j, (∀ i < j, A₀ i ≠ .fin) → ∃ f seen,
      chkRun δ bl c₀ var (.eq true s false) A₀ A₁ j = .eq f s seen := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨true, false, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨f, seen, hfs⟩ := ih fun i hi => hj i (by omega)
      have hstep := h (j + 1)
      rw [chkRun, hfs, stepC] at hstep ⊢
      simp only [isSink, Bool.false_eq_true, ↓reduceIte] at hstep ⊢
      split_ifs at hstep ⊢ with hh
      · exact absurd rfl hstep.2
      · by_cases hgood : ∃ x, A₀ j = .out x ∧ A₁ j = .out x
        · obtain ⟨x, hx₀, hx₁⟩ := hgood
          rw [hx₀, hx₁, chk_eq_out]
          exact ⟨false, _, rfl⟩
        · exfalso
          refine hstep.1 (chk_eq_err δ bl c₀ ?_)
          rintro (hg | ⟨hf, -⟩)
          · exact hgood hg
          · exact hj j (by omega) hf
  intro j hj
  obtain ⟨f, seen, hfs⟩ := key j hj
  by_contra hbad
  have hstep := h (j + 1)
  rw [chkRun, hfs, stepC] at hstep
  simp only [isSink, Bool.false_eq_true, ↓reduceIte] at hstep
  split_ifs at hstep
  · exact hstep.2 rfl
  · exact hstep.1 (chk_eq_err δ bl c₀ hbad)

/-- Before the end of the initial row, the Init check moves on iff player 1 outputs the next
cell. -/
theorem chk_init_lt {i : ℕ} (hi : i < c₀.length) (f : Bool) (a₀ a₁ : Move Q Γ) :
    chk δ bl c₀ (.init i f) a₀ a₁ = if a₁ = .out c₀[i] then .init (i + 1) false else .err := by
  simp only [chk, hi, ↓reduceDIte]

/-- At the end of the initial row, the Init check passes iff player 1 ends its output. -/
theorem chk_init_ge {i : ℕ} (hi : ¬ i < c₀.length) (f : Bool) (a₀ a₁ : Move Q Γ) :
    chk δ bl c₀ (.init i f) a₀ a₁ = if a₁ = .fin then .ok else .err := by
  simp only [chk, hi, ↓reduceDIte]

/-- The no-halting condition of a check step in the safety variant. -/
def NoHalt (a₀ a₁ : Move Q Γ) : Prop :=
  var = .safety → haltMove δ a₀ = false ∧ haltMove δ a₁ = false

/-- **The Init check passes** when player 1 outputs the initial row and, in the safety variant, no
move is a halting head. -/
theorem chkRun_init_ok {A₀ : ℕ → Move Q Γ}
    (hn : ∀ j ≤ c₀.length, NoHalt δ var (A₀ j) (rowMove c₀ j)) :
    chkRun δ bl c₀ var (.init 0 true) A₀ (rowMove c₀) (c₀.length + 1) = .ok := by
  have hpre : ∀ j ≤ c₀.length,
      chkRun δ bl c₀ var (.init 0 true) A₀ (rowMove c₀) j = .init j (j == 0) := by
    intro j
    induction j with
    | zero => intro; rfl
    | succ j ih =>
      intro hj
      have hjc : j < c₀.length := by omega
      have hno : (var = .safety && (haltMove δ (A₀ j) || haltMove δ (rowMove c₀ j))) = false := by
        rcases hv : var with _ | _
        · obtain ⟨h1, h2⟩ := hn j (by omega) hv
          simp [h1, h2]
        · rfl
      rw [chkRun, ih (by omega), stepC]
      simp only [isSink, hno, Bool.false_eq_true, ↓reduceIte]
      rw [chk_init_lt δ bl c₀ hjc]
      simp [rowMove, hjc]
  have hno : (var = .safety && (haltMove δ (A₀ c₀.length) ||
      haltMove δ (rowMove c₀ c₀.length))) = false := by
    rcases hv : var with _ | _
    · obtain ⟨h1, h2⟩ := hn c₀.length le_rfl hv
      simp [h1, h2]
    · rfl
  rw [chkRun, hpre _ le_rfl, stepC]
  simp only [isSink, hno, Bool.false_eq_true, ↓reduceIte]
  rw [chk_init_ge δ bl c₀ (lt_irrefl _)]
  simp [rowMove]

/-- **The Init check, read backwards**: if it never fails, player 1 outputs the initial row. -/
theorem init_of_chkRun {A₀ A₁ : ℕ → Move Q Γ}
    (h : ∀ j, chkRun δ bl c₀ var (.init 0 true) A₀ A₁ j ≠ .err ∧
      chkRun δ bl c₀ var (.init 0 true) A₀ A₁ j ≠ .hlt) :
    ∀ j ≤ c₀.length, A₁ j = rowMove c₀ j := by
  have key : ∀ j ≤ c₀.length, ∃ f, chkRun δ bl c₀ var (.init 0 true) A₀ A₁ j = .init j f := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨true, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨f, hf⟩ := ih (by omega)
      have hstep := h (j + 1)
      rw [chkRun, hf, stepC] at hstep ⊢
      simp only [isSink, Bool.false_eq_true, ↓reduceIte] at hstep ⊢
      split_ifs at hstep ⊢
      · exact absurd rfl hstep.2
      · rw [chk_init_lt δ bl c₀ (by omega)] at hstep ⊢
        split_ifs at hstep ⊢
        · exact ⟨false, rfl⟩
        · exact absurd rfl hstep.1
  intro j hj
  obtain ⟨f, hf⟩ := key j hj
  have hstep := h (j + 1)
  rw [chkRun, hf, stepC] at hstep
  simp only [isSink, Bool.false_eq_true, ↓reduceIte] at hstep
  split_ifs at hstep
  · exact absurd rfl hstep.2
  · by_cases hjc : j < c₀.length
    · rw [chk_init_lt δ bl c₀ hjc] at hstep
      split_ifs at hstep with ha
      · simp [rowMove, hjc, ha]
      · exact absurd rfl hstep.1
    · rw [chk_init_ge δ bl c₀ hjc] at hstep
      split_ifs at hstep with ha
      · obtain rfl : j = c₀.length := by omega
        simp [rowMove, ha]
      · exact absurd rfl hstep.1

/-- Cell `i` of a row, with blanks beyond its end. -/
def cellAt (u : List (Cell Q Γ)) (i : ℕ) : Cell Q Γ := u.getD i (.plain bl)

/-- The left neighbour of cell `j` of a row, `none` at the border. -/
def leftAt (u : List (Cell Q Γ)) (j : ℕ) : Option (Cell Q Γ) :=
  if j = 0 then none else some (cellAt bl u (j - 1))

/-- The row after `u` by the local rule, one cell longer. -/
def succWord (u : List (Cell Q Γ)) : List (Cell Q Γ) :=
  (List.range (u.length + 1)).map fun j =>
    localRule δ (leftAt bl u j) (cellAt bl u j) (cellAt bl u (j + 1))

/-- Player 0's output at the trigger round starts the Succ check. -/
theorem chk_succ₀_out (x : Cell Q Γ) (a₁ : Move Q Γ) :
    chk δ bl c₀ .succ₀ (.out x) a₁ = .succ true none x 0 := rfl

/-- An empty output of player 0 starts the Succ check at its end. -/
theorem chk_succ₀_fin (a₁ : Move Q Γ) :
    chk δ bl c₀ .succ₀ .fin a₁ = .succ true none (.plain bl) 1 := rfl

/-- While player 0 outputs cells, the Succ check moves on iff player 1 outputs the local rule of
player 0's cells. -/
theorem chk_succ_out (f : Bool) (l : Option (Cell Q Γ)) (m x : Cell Q Γ) (a₁ : Move Q Γ) :
    chk δ bl c₀ (.succ f l m 0) (.out x) a₁ =
      if a₁ = .out (localRule δ l m x) then .succ false (some m) x 0 else .err := by
  rcases a₁ with y | _ | _ | _ <;> simp [chk, eq_comm]

/-- When player 0 ends, the Succ check moves on iff player 1 outputs the local rule with a blank on
the right. -/
theorem chk_succ_fin (f : Bool) (l : Option (Cell Q Γ)) (m : Cell Q Γ) (a₁ : Move Q Γ) :
    chk δ bl c₀ (.succ f l m 0) .fin a₁ =
      if a₁ = .out (localRule δ l m (.plain bl)) then .succ false (some m) (.plain bl) 1
      else .err := by
  rcases a₁ with y | _ | _ | _ <;> simp [chk, eq_comm]

/-- At player 1's last cell, the Succ check moves on iff player 1 outputs the local rule with a
blank on the right. -/
theorem chk_succ_one (f : Bool) (l : Option (Cell Q Γ)) (m : Cell Q Γ) (a₀ a₁ : Move Q Γ) :
    chk δ bl c₀ (.succ f l m 1) a₀ a₁ =
      if a₁ = .out (localRule δ l m (.plain bl)) then .succ false (some m) (.plain bl) 2
      else .err := by
  rcases a₀ with x | _ | _ | _ <;> rcases a₁ with y | _ | _ | _ <;> simp [chk, eq_comm]

/-- At player 1's end, the Succ check passes iff player 1 ends its output. -/
theorem chk_succ_two (f : Bool) (l : Option (Cell Q Γ)) (m : Cell Q Γ) (a₀ a₁ : Move Q Γ) :
    chk δ bl c₀ (.succ f l m 2) a₀ a₁ = if a₁ = .fin then .ok else .err := by
  rcases a₀ with x | _ | _ | _ <;> rcases a₁ with y | _ | _ | _ <;> simp [chk]

/-- The rounds since player 0's end, at player 1's cell `j`. -/
def cnt (u : List (Cell Q Γ)) (j : ℕ) : ℕ :=
  if j < u.length then 0 else if j = u.length then 1 else 2

/-- The position of the Succ check at player 1's cell `j`. -/
def succPos (u : List (Cell Q Γ)) (j : ℕ) : Pos Q Γ :=
  .succ (j == 0) (leftAt bl u j) (cellAt bl u j) (cnt u j)

omit [DecidableEq Q] [DecidableEq Γ] in
/-- Cell `j` of the row after `u` is the local rule of cells `j - 1`, `j`, `j + 1` of `u`. -/
theorem succWord_getElem (u : List (Cell Q Γ)) {j : ℕ} (hj : j < (succWord δ bl u).length) :
    (succWord δ bl u)[j] = localRule δ (leftAt bl u j) (cellAt bl u j) (cellAt bl u (j + 1)) := by
  simp [succWord]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- The row after `u` is one cell longer than `u`. -/
@[simp]
theorem length_succWord (u : List (Cell Q Γ)) : (succWord δ bl u).length = u.length + 1 := by
  simp [succWord]

/-- One step of the Succ check from its position at player 1's cell `j`, when player 0 outputs `u`
and player 1 outputs the row after it: the check moves to cell `j + 1`. -/
theorem chk_succPos {u : List (Cell Q Γ)} {j : ℕ} (hj : j ≤ u.length) :
    chk δ bl c₀ (succPos bl u j) (rowMove u (j + 1)) (rowMove (succWord δ bl u) j) =
      succPos bl u (j + 1) := by
  have hjw : j < (succWord δ bl u).length := by rw [length_succWord]; omega
  have ha₁ : rowMove (succWord δ bl u) j =
      .out (localRule δ (leftAt bl u j) (cellAt bl u j) (cellAt bl u (j + 1))) := by
    rw [rowMove, dite_eq_left hjw, succWord_getElem δ bl u hjw]
  rw [ha₁]
  clear hjw ha₁
  rcases Nat.lt_or_ge (j + 1) u.length with h1 | h1
  · have hc : cnt u j = 0 := by rw [cnt, ite_eq_left (by omega)]
    have hr : rowMove u (j + 1) = .out (cellAt bl u (j + 1)) := by
      rw [rowMove, dite_eq_left h1, cellAt, List.getD_eq_getElem _ _ h1]
    have hc' : cnt u (j + 1) = 0 := by rw [cnt, ite_eq_left h1]
    rw [succPos, hc, hr, chk_succ_out, ite_eq_left rfl, succPos, hc']
    simp [leftAt]
  · rcases Nat.lt_or_ge j u.length with h2 | h2
    · have hc : cnt u j = 0 := by rw [cnt, ite_eq_left h2]
      have hju : j + 1 = u.length := by omega
      have hr : rowMove u (j + 1) = .fin := by
        rw [rowMove, dite_eq_right (by omega), ite_eq_left hju]
      have hb : cellAt bl u (j + 1) = .plain bl := by
        rw [cellAt, List.getD_eq_default _ _ (by omega)]
      have hc' : cnt u (j + 1) = 1 := by rw [cnt, ite_eq_right (by omega), ite_eq_left hju]
      rw [succPos, hc, hr, chk_succ_fin, hb, ite_eq_left rfl, succPos, hc', hb]
      simp [leftAt]
    · have hju : j = u.length := by omega
      subst hju
      have hc : cnt u u.length = 1 := by rw [cnt, ite_eq_right (by omega), ite_eq_left rfl]
      have hb : cellAt bl u (u.length + 1) = .plain bl := by
        rw [cellAt, List.getD_eq_default _ _ (by omega)]
      have hb' : cellAt bl u u.length = .plain bl := by
        rw [cellAt, List.getD_eq_default _ _ le_rfl]
      have hc' : cnt u (u.length + 1) = 2 := by
        rw [cnt, ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [succPos, hc, chk_succ_one, hb, hb', ite_eq_left rfl, succPos, hc', hb]
      simp [leftAt, hb']

/-- **The Succ check passes** when player 0 outputs `u` and player 1, one round later, outputs the
row after it, and, in the safety variant, no move is a halting head. -/
theorem chkRun_succ_ok {u : List (Cell Q Γ)} {A₁ : ℕ → Move Q Γ}
    (hA : ∀ j, A₁ (j + 1) = rowMove (succWord δ bl u) j)
    (hn : ∀ t, NoHalt δ var (rowMove u t) (A₁ t)) :
    chkRun δ bl c₀ var .succ₀ (rowMove u) A₁ (u.length + 3) = .ok := by
  have hno : ∀ t, (var = .safety && (haltMove δ (rowMove u t) || haltMove δ (A₁ t))) = false := by
    intro t
    rcases hv : var with _ | _
    · obtain ⟨h1, h2⟩ := hn t hv
      simp [h1, h2]
    · rfl
  have hpos : ∀ j ≤ u.length + 1, chkRun δ bl c₀ var .succ₀ (rowMove u) A₁ (j + 1) =
      succPos bl u j := by
    intro j
    induction j with
    | zero =>
      intro
      rw [chkRun, chkRun, stepC]
      simp only [isSink, hno, Bool.false_eq_true, ↓reduceIte]
      rcases Nat.eq_zero_or_pos u.length with h0 | h0
      · have hr : rowMove u 0 = .fin := by simp [rowMove, h0]
        rw [hr, chk_succ₀_fin]
        simp [succPos, leftAt, cnt, cellAt, h0]
      · have hr : rowMove u 0 = .out (cellAt bl u 0) := by
          simp [rowMove, h0, cellAt]
        rw [hr, chk_succ₀_out]
        simp [succPos, leftAt, cnt, h0]
    | succ j ih =>
      intro hj
      rw [chkRun, ih (by omega), stepC]
      simp only [isSink, succPos, hno, Bool.false_eq_true, ↓reduceIte]
      rw [hA j, ← succPos]
      exact chk_succPos δ bl c₀ (by omega)
  rw [chkRun, hpos _ le_rfl, stepC]
  simp only [isSink, succPos, hno, Bool.false_eq_true, ↓reduceIte]
  have hc : cnt u (u.length + 1) = 2 := by simp [cnt]
  rw [hc, chk_succ_two, hA (u.length + 1)]
  simp [rowMove]

/-- A step of the Succ check that neither fails nor reaches `hlt` is the step of `chk`. -/
theorem stepC_of_ne {p : Pos Q Γ} {a₀ a₁ : Move Q Γ} (hp : isSink p = false)
    (h : stepC δ bl c₀ var p a₀ a₁ ≠ .hlt) : stepC δ bl c₀ var p a₀ a₁ = chk δ bl c₀ p a₀ a₁ := by
  unfold stepC at h ⊢
  simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
  split_ifs at h ⊢
  · exact absurd rfl h
  · rfl

/-- **The Succ check, read backwards**: if it never fails and player 0 outputs `u`, player 1
outputs the row after `u`, one round later. -/
theorem succ_of_chkRun {u : List (Cell Q Γ)} {A₀ A₁ : ℕ → Move Q Γ}
    (h : ∀ j, chkRun δ bl c₀ var .succ₀ A₀ A₁ j ≠ .err ∧ chkRun δ bl c₀ var .succ₀ A₀ A₁ j ≠ .hlt)
    (hA₀ : ∀ j ≤ u.length, A₀ j = rowMove u j) :
    ∀ j ≤ u.length + 1, A₁ (j + 1) = rowMove (succWord δ bl u) j := by
  have hstep : ∀ t, chkRun δ bl c₀ var .succ₀ A₀ A₁ (t + 1) =
      chk δ bl c₀ (chkRun δ bl c₀ var .succ₀ A₀ A₁ t) (A₀ t) (A₁ t) ∨
      isSink (chkRun δ bl c₀ var .succ₀ A₀ A₁ t) = true := by
    intro t
    by_cases hs : isSink (chkRun δ bl c₀ var .succ₀ A₀ A₁ t) = true
    · exact Or.inr hs
    · exact Or.inl (stepC_of_ne δ bl c₀ var (by simpa using hs) (h (t + 1)).2)
  have hpos : ∀ j ≤ u.length + 1, chkRun δ bl c₀ var .succ₀ A₀ A₁ (j + 1) = succPos bl u j ∧
      ∀ i < j, A₁ (i + 1) = rowMove (succWord δ bl u) i := by
    intro j
    induction j with
    | zero =>
      intro
      refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      rcases hstep 0 with h0 | h0
      · rw [h0, chkRun, hA₀ 0 (Nat.zero_le _)]
        rcases Nat.eq_zero_or_pos u.length with hu | hu
        · have hr : rowMove u 0 = .fin := by simp [rowMove, hu]
          rw [hr, chk_succ₀_fin]
          simp [succPos, leftAt, cnt, cellAt, hu]
        · have hr : rowMove u 0 = .out (cellAt bl u 0) := by simp [rowMove, hu, cellAt]
          rw [hr, chk_succ₀_out]
          simp [succPos, leftAt, cnt, hu]
      · simp [chkRun, isSink] at h0
    | succ j ih =>
      intro hj
      obtain ⟨hp, hprev⟩ := ih (by omega)
      have hne := h (j + 2)
      rcases hstep (j + 1) with hs | hs
      · rw [hp] at hs
        have hjw : j < (succWord δ bl u).length := by rw [length_succWord]; omega
        have hreq : rowMove (succWord δ bl u) j =
            .out (localRule δ (leftAt bl u j) (cellAt bl u j) (cellAt bl u (j + 1))) := by
          rw [rowMove, dite_eq_left hjw, succWord_getElem δ bl u hjw]
        -- the step from player 1's cell `j` is `chk` applied to the required move
        have hchk : ∀ a₀, (j + 1 ≤ u.length → a₀ = rowMove u (j + 1)) → ∀ a₁,
            chk δ bl c₀ (succPos bl u j) a₀ a₁ =
              if a₁ = rowMove (succWord δ bl u) j then succPos bl u (j + 1) else .err := by
          intro a₀ ha₀ a₁
          split_ifs with ha₁
          · rw [ha₁]
            rcases Nat.lt_or_ge j u.length with h2 | h2
            · rw [ha₀ (by omega)]
              exact chk_succPos δ bl c₀ (by omega)
            · have hju : j = u.length := by omega
              subst hju
              have hc : cnt u u.length = 1 := by rw [cnt, ite_eq_right (by omega), ite_eq_left rfl]
              rw [← chk_succPos δ bl c₀ (le_refl u.length), succPos, hc, chk_succ_one,
                chk_succ_one]
          · rw [hreq] at ha₁
            rcases Nat.lt_or_ge (j + 1) u.length with h1 | h1
            · have hc : cnt u j = 0 := by rw [cnt, ite_eq_left (by omega)]
              have hr : rowMove u (j + 1) = .out (cellAt bl u (j + 1)) := by
                rw [rowMove, dite_eq_left h1, cellAt, List.getD_eq_getElem _ _ h1]
              rw [succPos, hc, ha₀ (by omega), hr, chk_succ_out, ite_eq_right ha₁]
            · rcases Nat.lt_or_ge j u.length with h2 | h2
              · have hc : cnt u j = 0 := by rw [cnt, ite_eq_left h2]
                have hr : rowMove u (j + 1) = .fin := by
                  rw [rowMove, dite_eq_right (by omega), ite_eq_left (by omega)]
                have hb : cellAt bl u (j + 1) = .plain bl := by
                  rw [cellAt, List.getD_eq_default _ _ (by omega)]
                rw [succPos, hc, ha₀ (by omega), hr, chk_succ_fin, ← hb, ite_eq_right ha₁]
              · have hju : j = u.length := by omega
                subst hju
                have hc : cnt u u.length = 1 := by
                  rw [cnt, ite_eq_right (by omega), ite_eq_left rfl]
                have hb : cellAt bl u (u.length + 1) = .plain bl := by
                  rw [cellAt, List.getD_eq_default _ _ (by omega)]
                rw [succPos, hc, chk_succ_one, ← hb, ite_eq_right ha₁]
        rw [hchk (A₀ (j + 1)) (fun h' => hA₀ _ h') (A₁ (j + 1))] at hs
        split_ifs at hs with ha₁
        · refine ⟨hs, fun i hi => ?_⟩
          rcases Nat.lt_or_ge i j with hij | hij
          · exact hprev i hij
          · rw [show i = j by omega, ha₁]
        · exact absurd hs hne.1
      · rw [hp] at hs
        simp [succPos, isSink] at hs
  intro j hj
  rcases Nat.lt_or_ge j (u.length + 1) with h1 | h1
  · exact (hpos (j + 1) (by omega)).2 j (by omega)
  · have hju : j = u.length + 1 := by omega
    subst hju
    have hp := (hpos (u.length + 1) le_rfl).1
    have hne := h (u.length + 3)
    by_contra hne'
    rcases hstep (u.length + 2) with hs | hs
    · apply hne.1
      rw [hs, hp]
      have hc : cnt u (u.length + 1) = 2 := by
        rw [cnt, ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [succPos, hc, chk_succ_two, ite_eq_right]
      simpa [rowMove] using hne'
    · rw [hp] at hs
      simp [succPos, isSink] at hs

/-- A check depends only on the moves made so far. -/
theorem chkRun_congr {p : Pos Q Γ} {A₀ A₁ B₀ B₁ : ℕ → Move Q Γ} {j : ℕ}
    (h : ∀ i < j, A₀ i = B₀ i ∧ A₁ i = B₁ i) :
    chkRun δ bl c₀ var p A₀ A₁ j = chkRun δ bl c₀ var p B₀ B₁ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [chkRun, chkRun, ih fun i hi => h i (by omega), (h j (by omega)).1, (h j (by omega)).2]

/-- A check that passes never fails. -/
theorem ne_err_of_ok {p : Pos Q Γ} {A₀ A₁ : ℕ → Move Q Γ} {j₀ : ℕ}
    (hok : chkRun δ bl c₀ var p A₀ A₁ j₀ = .ok) (j : ℕ) :
    chkRun δ bl c₀ var p A₀ A₁ j ≠ .err ∧ chkRun δ bl c₀ var p A₀ A₁ j ≠ .hlt := by
  rcases Nat.le_total j j₀ with h | h
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
    constructor <;> intro he <;>
      · have := chkRun_sink δ bl c₀ var (p := p) (A₀ := A₀) (A₁ := A₁) (j := j)
          (by simp [he, isSink]) i
        rw [this, he] at hok
        exact absurd hok (by simp)
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [chkRun_sink δ bl c₀ var (p := p) (A₀ := A₀) (A₁ := A₁) (by simp [hok, isSink]) i, hok]
    simp

/-- If the Eq check never fails and player 1 outputs `w`, then player 0 outputs `w` too. -/
theorem agree_of_eq {w : List (Cell Q Γ)} {A₀ A₁ : ℕ → Move Q Γ} {s : Bool}
    (h : ∀ j, chkRun δ bl c₀ var (.eq true s false) A₀ A₁ j ≠ .err ∧
      chkRun δ bl c₀ var (.eq true s false) A₀ A₁ j ≠ .hlt)
    (hA₁ : ∀ j ≤ w.length, A₁ j = rowMove w j) : ∀ j ≤ w.length, A₀ j = rowMove w j := by
  have hagree := eq_of_chkRun δ bl c₀ var h
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases hagree j fun i hi => by
        rw [ih i hi (by omega)]
        simp only [rowMove, dite_eq_left (show i < w.length by omega)]
        simp with ⟨x, hx₀, hx₁⟩ | ⟨hf₀, hf₁⟩
    · rw [hx₀, ← hx₁, hA₁ j hj]
    · rw [hf₀, ← hf₁, hA₁ j hj]

/-- **The stop check, read backwards**: if it never fails and player 1 outputs `w`, then `w` has a
halting head. -/
theorem hasHalt_of_stop {w : List (Cell Q Γ)} {A₀ A₁ : ℕ → Move Q Γ}
    (h : ∀ j, chkRun δ bl c₀ var (.eq true true false) A₀ A₁ j ≠ .err ∧
      chkRun δ bl c₀ var (.eq true true false) A₀ A₁ j ≠ .hlt)
    (hA₁ : ∀ j ≤ w.length, A₁ j = rowMove w j) (hv : var = .reach) : hasHalt δ w = true := by
  have hA := agree_of_eq δ bl c₀ var h hA₁
  have hrun := h (w.length + 1)
  rw [chkRun_congr δ bl c₀ var (B₀ := rowMove w) (B₁ := rowMove w) fun i hi =>
    ⟨hA i (by omega), hA₁ i (by omega)⟩] at hrun
  by_contra hno
  apply hrun.1
  rw [chkRun, chkRun_eq_prefix δ bl c₀ var le_rfl (fun hs => by simp [hv] at hs),
    List.take_length, stepC]
  have hf : rowMove w w.length = (.fin : Move Q Γ) := by simp [rowMove]
  simp only [isSink, hf, haltMove, Bool.or_false, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte, chk_eq_fin]
  simp [hno]

/-- **The Eq check in the safety variant, read backwards**: if it never fails and never reaches
`hlt` and player 1 outputs `w`, then `w` has no halting head. -/
theorem noHalt_of_eq {w : List (Cell Q Γ)} {A₀ A₁ : ℕ → Move Q Γ} {s : Bool}
    (h : ∀ j, chkRun δ bl c₀ var (.eq true s false) A₀ A₁ j ≠ .err ∧
      chkRun δ bl c₀ var (.eq true s false) A₀ A₁ j ≠ .hlt)
    (hA₁ : ∀ j ≤ w.length, A₁ j = rowMove w j) (hv : var = .safety) : hasHalt δ w = false := by
  have hA := agree_of_eq δ bl c₀ var h hA₁
  have key : ∀ j ≤ w.length, hasHalt δ (w.take j) = false := by
    intro j
    induction j with
    | zero => intro; simp [hasHalt]
    | succ j ih =>
      intro hj
      have hjw : j < w.length := by omega
      have hpre := ih (by omega)
      rw [hasHalt_take_succ δ hjw, hpre, Bool.false_or]
      by_contra hc
      have hrun := (h (j + 1)).2
      rw [chkRun_congr δ bl c₀ var (B₀ := rowMove w) (B₁ := rowMove w) fun i hi =>
        ⟨hA i (by omega), hA₁ i (by omega)⟩] at hrun
      apply hrun
      rw [chkRun, chkRun_eq_prefix δ bl c₀ var (by omega) fun _ => hpre, stepC]
      have hm : rowMove w j = .out w[j] := by simp [rowMove, hjw]
      simp [isSink, hv, hm, haltMove, hc]
  simpa using key w.length le_rfl

/-- From a non-waiting position, the only successor is the step of the check. -/
theorem succs_of_not_waiting {p : Pos Q Γ} (hp : isWaiting p = false) (a₀ a₁ : Move Q Γ) :
    succs δ bl c₀ var p a₀ a₁ = [stepC δ bl c₀ var p a₀ a₁] := by
  unfold succs stepC
  split_ifs <;> simp_all

/-- A check never moves to a waiting position. -/
theorem isWaiting_chk (p : Pos Q Γ) (a₀ a₁ : Move Q Γ) :
    isWaiting (chk δ bl c₀ p a₀ a₁) = false := by
  unfold chk
  split <;> (try split_ifs) <;> rfl

/-- A check step never moves to a waiting position. -/
theorem isWaiting_stepC {p : Pos Q Γ} (a₀ a₁ : Move Q Γ) (hp : isWaiting p = false) :
    isWaiting (stepC δ bl c₀ var p a₀ a₁) = false := by
  unfold stepC
  split_ifs
  · exact hp
  · rfl
  · exact isWaiting_chk δ bl c₀ p a₀ a₁

/-- After a check step, player 0 sees no trigger. -/
theorem observe_stepC_fst (p : Pos Q Γ) (a₀ a₁ : Move Q Γ) :
    (observe (stepC δ bl c₀ var p a₀ a₁)).1 = false := by
  unfold stepC
  split_ifs with h
  · rcases p <;> simp_all [isSink, observe]
  · rfl
  · unfold chk; split <;> (try split_ifs) <;> rfl

/-- After a check step from a position other than player 0's Succ trigger, player 1 sees no
trigger. -/
theorem observe_stepC_snd {p : Pos Q Γ} (hp : p ≠ .succ₀) (a₀ a₁ : Move Q Γ) :
    (observe (stepC δ bl c₀ var p a₀ a₁)).2 = false := by
  unfold stepC
  split_ifs with h
  · rcases p <;> simp_all [isSink, observe]
  · rfl
  · unfold chk; split <;> (try split_ifs) <;> simp_all [observe]

end Checks

/-! ### Plays and checks -/

section PlayChecks

variable {δ : Q → Γ → Act Q Γ} {bl : Γ} {c₀ : List (Cell Q Γ)} {var : Variant}
  {σ₀ σ₁ : List Bool → Move Q Γ} {f : ℕ → Pos Q Γ}

/-- **From a non-waiting position, a play is the run of the check on the players' moves.** -/
theorem play_eq_chkRun (hf : IsPlayA δ bl c₀ var σ₀ σ₁ f) {m : ℕ} (hm : isWaiting (f m) = false)
    (j : ℕ) : f (m + j) = chkRun δ bl c₀ var (f m) (fun i => σ₀ (hist₀ f (m + i)))
      (fun i => σ₁ (hist₁ f (m + i))) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hw : isWaiting (f (m + j)) = false := by
      rw [ih]
      clear ih
      induction j with
      | zero => exact hm
      | succ j ih' => exact isWaiting_stepC δ bl c₀ var _ _ ih'
    have h := hf.2 (m + j)
    rw [succs_of_not_waiting δ bl c₀ var hw, List.mem_singleton] at h
    rw [← Nat.add_assoc, h, ih]
    rfl

omit [DecidableEq Q] [DecidableEq Γ] in
/-- Before any trigger, both players see nothing. -/
theorem observe_waiting {p : Pos Q Γ} (hp : isWaiting p = true) : observe p = (false, false) := by
  rcases p <;> simp_all [isWaiting, observe]

/-- The history of player 0 triggered at round `m`, when it saw no trigger before and the check
starts at `m`. -/
theorem hist₀_trig (hf : IsPlayA δ bl c₀ var σ₀ σ₁ f) {m : ℕ}
    (hb : ∀ i < m, (observe (f i)).1 = false) (hm : isWaiting (f m) = false)
    (ht : (observe (f m)).1 = true) (j : ℕ) : hist₀ f (m + j) = trig m j := by
  refine range_map_eq_trig hb ht fun i h1 h2 => ?_
  obtain ⟨k, rfl⟩ : ∃ k, i = m + (k + 1) := ⟨i - m - 1, by omega⟩
  rw [play_eq_chkRun hf hm, chkRun]
  exact observe_stepC_fst δ bl c₀ var _ _ _

/-- The history of player 1 triggered at round `m`, when it saw no trigger before and the check
runs from `m`. -/
theorem hist₁_trig (hf : IsPlayA δ bl c₀ var σ₀ σ₁ f) {m : ℕ}
    (hb : ∀ i < m, (observe (f i)).2 = false) (hm : isWaiting (f m) = false)
    (ht : (observe (f m)).2 = true) (j : ℕ) : hist₁ f (m + j) = trig m j := by
  refine range_map_eq_trig hb ht fun i h1 h2 => ?_
  obtain ⟨k, rfl⟩ : ∃ k, i = m + (k + 1) := ⟨i - m - 1, by omega⟩
  rw [play_eq_chkRun hf hm, chkRun]
  refine observe_stepC_snd δ bl c₀ var ?_ _ _
  intro hs
  induction k with
  | zero => simp [chkRun] at hs; rw [hs] at ht; simp [observe] at ht
  | succ k ih =>
    rw [chkRun] at hs
    have := observe_stepC_fst δ bl c₀ var (chkRun δ bl c₀ var (f m) (fun i => σ₀ (hist₀ f (m + i)))
      (fun i => σ₁ (hist₁ f (m + i))) k) (σ₀ (hist₀ f (m + k))) (σ₁ (hist₁ f (m + k)))
    rw [hs] at this
    simp [observe] at this

end PlayChecks

/-! ### The rows of the tableau as outputs -/

section Rows

variable (δ : Q → Γ → Act Q Γ) (bl : Γ) (k₀ : Cfg Q Γ)

/-- The output for row `t` of the tableau: its first `n + t` cells, `n` the number of cells of the
initial configuration. -/
def rowWord (t : ℕ) : List (Cell Q Γ) :=
  (List.range ((cells k₀).length + t)).map (tab δ bl k₀ t)

omit [DecidableEq Q] [DecidableEq Γ] in
/-- The output for row `t` has `n + t` cells, `n` the number of cells of the initial
configuration. -/
@[simp]
theorem length_rowWord (t : ℕ) : (rowWord δ bl k₀ t).length = (cells k₀).length + t := by
  simp [rowWord]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- The output for row 0 is the initial configuration. -/
theorem rowWord_zero : rowWord δ bl k₀ 0 = cells k₀ := by
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp [rowWord, tab, row, List.getElem?_eq_getElem h₂]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- Cell `j` of the output for row `t`, with blanks beyond its end, is cell `j` of the row. -/
theorem cellAt_rowWord (t j : ℕ) : cellAt bl (rowWord δ bl k₀ t) j = tab δ bl k₀ t j := by
  by_cases hj : j < (cells k₀).length + t
  · simp [cellAt, rowWord, List.getElem?_range hj]
  · rw [cellAt, List.getD_eq_default _ _ (by simp; omega), tab_blank (by omega)]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- **The row after an output row is the next output row.** -/
theorem succWord_rowWord (t : ℕ) : succWord δ bl (rowWord δ bl k₀ t) = rowWord δ bl k₀ (t + 1) := by
  refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
  rw [succWord_getElem δ bl _ h₁]
  simp only [leftAt, cellAt_rowWord]
  simp [rowWord, tab, stepRow, leftOf]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- `isHaltCellB` tests for a halting head. -/
theorem isHaltCellB_iff {x : Cell Q Γ} : isHaltCellB δ x = true ↔ IsHaltCell δ x := by
  rcases x with c | ⟨q, c⟩
  · simp [isHaltCellB, IsHaltCell]
  · simp only [isHaltCellB, IsHaltCell]
    cases δ q c <;> simp

omit [DecidableEq Q] [DecidableEq Γ] in
/-- An output row has a halting head iff its row in the tableau does. -/
theorem hasHalt_rowWord (t : ℕ) :
    hasHalt δ (rowWord δ bl k₀ t) = true ↔ ∃ j, IsHaltCell δ (tab δ bl k₀ t j) := by
  simp only [hasHalt, List.any_eq_true, rowWord, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨j, -, rfl⟩, h⟩
    exact ⟨j, (isHaltCellB_iff δ).1 h⟩
  · rintro ⟨j, hj⟩
    refine ⟨_, ⟨j, ?_, rfl⟩, (isHaltCellB_iff δ).2 hj⟩
    by_contra hge
    rw [tab_blank (by omega)] at hj
    exact hj

omit [DecidableEq Q] [DecidableEq Γ] in
/-- A halting head stays in the next row. -/
theorem tab_halt_succ {t j : ℕ} (h : IsHaltCell δ (tab δ bl k₀ t j)) :
    IsHaltCell δ (tab δ bl k₀ (t + 1) j) := by
  simp only [tab, stepRow, localRule]
  revert h
  cases tab δ bl k₀ t j with
  | plain d => simp [IsHaltCell]
  | head q c =>
    intro h
    simp only [IsHaltCell] at h
    simp [afterHead, h, IsHaltCell]

end Rows

/-! ### Scenarios -/

section Scenarios

variable {δ : Q → Γ → Act Q Γ} {bl : Γ} {c₀ : List (Cell Q Γ)} {var : Variant}
  {σ₀ σ₁ : List Bool → Move Q Γ}

/-- The waiting moves of the players are harmless before round `m`: no halting head in the safety
variant, and no `stop` by player 0 from round 1 on in the reachability variant. -/
def QuietBefore (δ : Q → Γ → Act Q Γ) (var : Variant) (σ₀ σ₁ : List Bool → Move Q Γ) (m : ℕ) :
    Prop :=
  ∀ k < m, (var = .safety → haltMove δ (σ₀ (List.replicate (k + 1) false)) = false ∧
      haltMove δ (σ₁ (List.replicate (k + 1) false)) = false) ∧
    (var = .reach → 1 ≤ k → σ₀ (List.replicate (k + 1) false) ≠ .stop)

/-- A play built from a policy follows it while the policy proposes successors. -/
theorem buildPlay_follow (pol : ℕ → Pos Q Γ → Pos Q Γ) (k : ℕ)
    (h : pol k (buildPlay δ bl c₀ var σ₀ σ₁ pol k) ∈ succs δ bl c₀ var
      (buildPlay δ bl c₀ var σ₀ σ₁ pol k)
      (σ₀ (hist₀ (buildPlay δ bl c₀ var σ₀ σ₁ pol) k))
      (σ₁ (hist₁ (buildPlay δ bl c₀ var σ₀ σ₁ pol) k))) :
    buildPlay δ bl c₀ var σ₀ σ₁ pol (k + 1) = pol k (buildPlay δ bl c₀ var σ₀ σ₁ pol k) := by
  rw [buildPlay_succ, ite_eq_left h]

/-- The waiting policy: wait in the given mode, then move to `p` at round `m`. -/
def waitPol (b : Bool) (m : ℕ) (p : Pos Q Γ) : ℕ → Pos Q Γ → Pos Q Γ :=
  fun k q => if k + 1 < m then .wait b else if k + 1 = m then p else q

omit [DecidableEq Q] [DecidableEq Γ] in
/-- The waiting moves of the players are harmless before an earlier round too. -/
theorem QuietBefore.mono {m m' : ℕ} (h : QuietBefore δ var σ₀ σ₁ m) (hm : m' ≤ m) :
    QuietBefore δ var σ₀ σ₁ m' := fun k hk => h k (by omega)

/-- At a waiting position with harmless moves, Nature may move to any of its moves. -/
theorem succs_waiting {p : Pos Q Γ} {a₀ a₁ : Move Q Γ} (hp : isWaiting p = true)
    (hs : var = .safety → haltMove δ a₀ = false ∧ haltMove δ a₁ = false)
    (hr : var = .reach → p ≠ .start → a₀ ≠ .stop) :
    succs δ bl c₀ var p a₀ a₁ = natureMoves p := by
  have hns : isSink p = false := by rcases p <;> simp_all [isWaiting, isSink]
  unfold succs
  simp only [hns, Bool.false_eq_true, ↓reduceIte, hp]
  rcases hv : var with _ | _
  · obtain ⟨h1, h2⟩ := hs hv
    simp [h1, h2]
  · by_cases hst : p = .start
    · simp [hst]
    · simp [hr hv hst]

/-- **Waiting plays exist**: when the waiting moves are harmless before round `m - 1` and `p` is a
successor at round `m - 1`, the play of `waitPol b m p` starts, waits in mode `b` until `m - 1`,
and is at `p` at round `m`. -/
theorem waitPol_play {b : Bool} {m : ℕ} {p : Pos Q Γ} (hm : 1 ≤ m)
    (hq : QuietBefore δ var σ₀ σ₁ (m - 1))
    (hlast : p ∈ succs δ bl c₀ var (if m - 1 = 0 then .start else .wait b)
      (σ₀ (List.replicate m false)) (σ₁ (List.replicate m false))) :
    (∀ k < m, buildPlay δ bl c₀ var σ₀ σ₁ (waitPol b m p) k =
      if k = 0 then .start else .wait b) ∧ buildPlay δ bl c₀ var σ₀ σ₁ (waitPol b m p) m = p := by
  set f := buildPlay δ bl c₀ var σ₀ σ₁ (waitPol b m p) with hf
  have hwb : (.wait b : Pos Q Γ) ∈ natureMoves (.start : Pos Q Γ) := by
    cases b <;> simp [natureMoves]
  have hww : (.wait b : Pos Q Γ) ∈ natureMoves (.wait b : Pos Q Γ) := by
    cases b <;> simp [natureMoves]
  have hhist : ∀ k, (∀ i ≤ k, f i = if i = 0 then .start else .wait b) →
      hist₀ f k = List.replicate (k + 1) false ∧ hist₁ f k = List.replicate (k + 1) false := by
    intro k hall
    have hwait : ∀ i ≤ k, isWaiting (f i) = true := fun i hi => by
      rw [hall i hi]; split_ifs <;> rfl
    exact ⟨range_map_eq_replicate fun i hi => by rw [observe_waiting (hwait i hi)],
      range_map_eq_replicate fun i hi => by rw [observe_waiting (hwait i hi)]⟩
  have hstep : ∀ k < m - 1, (∀ i ≤ k, f i = if i = 0 then .start else .wait b) →
      succs δ bl c₀ var (f k) (σ₀ (hist₀ f k)) (σ₁ (hist₁ f k)) = natureMoves (f k) := by
    intro k hk hall
    obtain ⟨h₀, h₁⟩ := hhist k hall
    have hw : isWaiting (f k) = true := by rw [hall k le_rfl]; split_ifs <;> rfl
    refine succs_waiting hw (fun hv => ?_) (fun hv hne => ?_)
    · rw [h₀, h₁]; exact (hq k hk).1 hv
    · rw [h₀]
      refine (hq k hk).2 hv ?_
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exact absurd (hall 0 le_rfl) (by simpa using hne)
      · exact hpos
  have hpos : ∀ k < m, f k = if k = 0 then .start else .wait b := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases k with _ | k
      · rfl
      · have hall : ∀ i ≤ k, f i = if i = 0 then .start else .wait b :=
          fun i hi => ih i (by omega) (by omega)
        rw [hf, buildPlay_follow, ← hf]
        · simp [waitPol, show k + 1 < m from hk]
        · rw [← hf, hstep k (by omega) hall]
          simp only [waitPol, show k + 1 < m from hk, ↓reduceIte]
          rw [hall k le_rfl]
          split_ifs
          · exact hwb
          · exact hww
  refine ⟨hpos, ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hall : ∀ i ≤ m', f i = if i = 0 then .start else .wait b :=
    fun i hi => hpos i (by omega)
  obtain ⟨h₀, h₁⟩ := hhist m' hall
  rw [hf, buildPlay_follow, ← hf]
  · simp [waitPol]
  · rw [← hf, h₀, h₁, hall m' le_rfl]
    simp only [waitPol, lt_irrefl, ↓reduceIte]
    simpa using hlast

/-- When player 0 never stops and no waiting move is a halting head, the play of
`waitPol false 1 (.wait false)` waits in mode `false` forever. -/
theorem stay_play (hq : ∀ m, QuietBefore δ var σ₀ σ₁ m) (k : ℕ) :
    buildPlay δ bl c₀ var σ₀ σ₁ (waitPol false 1 (.wait false)) k =
      if k = 0 then .start else .wait false := by
  set f := buildPlay δ bl c₀ var σ₀ σ₁ (waitPol false 1 (.wait false)) with hf
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rfl
    · have hall : ∀ i ≤ k, f i = if i = 0 then .start else .wait false :=
        fun i hi => ih i (by omega)
      have hwait : ∀ i ≤ k, isWaiting (f i) = true := fun i hi => by
        rw [hall i hi]; split_ifs <;> rfl
      have h₀ : hist₀ f k = List.replicate (k + 1) false :=
        range_map_eq_replicate fun i hi => by rw [observe_waiting (hwait i hi)]
      have h₁ : hist₁ f k = List.replicate (k + 1) false :=
        range_map_eq_replicate fun i hi => by rw [observe_waiting (hwait i hi)]
      have hs : succs δ bl c₀ var (f k) (σ₀ (hist₀ f k)) (σ₁ (hist₁ f k)) = natureMoves (f k) := by
        refine succs_waiting (hwait k le_rfl) (fun hv => ?_) (fun hv hne => ?_)
        · rw [h₀, h₁]; exact (hq (k + 1) k (by omega)).1 hv
        · rw [h₀]
          refine (hq (k + 1) k (by omega)).2 hv ?_
          rcases Nat.eq_zero_or_pos k with rfl | hpos
          · exact absurd (hall 0 le_rfl) (by simpa using hne)
          · exact hpos
      have hprop : waitPol false 1 (.wait false) k (f k) = (.wait false : Pos Q Γ) := by
        rcases k with _ | k
        · simp [waitPol]
        · simp only [waitPol, show ¬ (k + 1 + 1 < 1) by omega, show ¬ (k + 1 + 1 = 1) by omega,
            ↓reduceIte]
          rw [hall (k + 1) le_rfl]
          simp
      rw [hf, buildPlay_follow, ← hf, hprop]
      · simp
      · rw [← hf, hs, hprop, hall k le_rfl]
        split_ifs <;> simp [natureMoves]

/-- In every play the team never reaches `err` or `hlt`. -/
def SafePlays (δ : Q → Γ → Act Q Γ) (bl : Γ) (c₀ : List (Cell Q Γ)) (var : Variant)
    (σ₀ σ₁ : List Bool → Move Q Γ) : Prop :=
  ∀ f, IsPlayA δ bl c₀ var σ₀ σ₁ f → ∀ k, f k ≠ .err ∧ f k ≠ .hlt

/-- When plays are safe, no check of a play fails. -/
theorem chkRun_safe (hs : SafePlays δ bl c₀ var σ₀ σ₁) {f : ℕ → Pos Q Γ}
    (hf : IsPlayA δ bl c₀ var σ₀ σ₁ f) {m : ℕ} (hm : isWaiting (f m) = false) (j : ℕ) :
    chkRun δ bl c₀ var (f m) (fun i => σ₀ (hist₀ f (m + i))) (fun i => σ₁ (hist₁ f (m + i))) j ≠
      .err ∧
    chkRun δ bl c₀ var (f m) (fun i => σ₀ (hist₀ f (m + i))) (fun i => σ₁ (hist₁ f (m + i))) j ≠
      .hlt := by
  rw [← play_eq_chkRun hf hm]
  exact hs f hf _

/-- A play stays at a sink. -/
theorem play_sink {f : ℕ → Pos Q Γ} (hf : IsPlayA δ bl c₀ var σ₀ σ₁ f) {n : ℕ}
    (hn : isSink (f n) = true) (i : ℕ) : f (n + i) = f n := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h := hf.2 (n + i)
    rw [ih] at h
    unfold succs at h
    rw [ite_eq_left hn, List.mem_singleton] at h
    rw [← Nat.add_assoc, h]

/-- If every play reaches `ok`, plays are safe. -/
theorem safePlays_of_reach (h : ∀ f, IsPlayA δ bl c₀ var σ₀ σ₁ f → ∃ k, f k = .ok) :
    SafePlays δ bl c₀ var σ₀ σ₁ := by
  intro f hf n
  obtain ⟨k, hk⟩ := h f hf
  rcases Nat.le_total n k with hnk | hkn
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hnk
    constructor <;> intro he <;>
      · have := play_sink hf (n := n) (by simp [he, isSink]) i
        rw [hk, he] at this
        exact absurd this (by simp)
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [play_sink hf (n := k) (by simp [hk, isSink]) i, hk]
    simp

omit [DecidableEq Q] [DecidableEq Γ] in
/-- The positions of a waiting play see no trigger. -/
theorem observe_waitPol {b : Bool} {m : ℕ} {f : ℕ → Pos Q Γ}
    (hw : ∀ k < m, f k = if k = 0 then .start else .wait b) :
    ∀ i < m, observe (f i) = (false, false) := fun i hi => by
  rw [hw i hi]; split_ifs <;> rfl

/-- **The Init claim**: when plays are safe, player 1 triggered at round 1 outputs the
initial row. -/
theorem claim_init (hs : SafePlays δ bl c₀ var σ₀ σ₁) (hq : QuietBefore δ var σ₀ σ₁ 1) :
    ∀ j ≤ c₀.length, σ₁ (trig 1 j) = rowMove c₀ j := by
  set f := buildPlay δ bl c₀ var σ₀ σ₁ (waitPol false 1 (.init 0 true)) with hf
  obtain ⟨hw, h1⟩ := waitPol_play (δ := δ) (bl := bl) (c₀ := c₀) (var := var) (σ₀ := σ₀)
    (σ₁ := σ₁) (b := false) (p := .init 0 true) le_rfl (hq.mono (by omega)) (by
      rw [succs_waiting rfl (fun hv => (hq 0 (by omega)).1 hv)
        (fun _ hne => absurd (by simp) hne)]
      simp [natureMoves])
  rw [← hf] at hw h1
  have hpl : IsPlayA δ bl c₀ var σ₀ σ₁ f := buildPlay_isPlay δ bl c₀ var σ₀ σ₁ _
  have hm : isWaiting (f 1) = false := by rw [h1]; rfl
  have hob := observe_waitPol hw
  have h₁ : ∀ j, hist₁ f (1 + j) = trig 1 j :=
    hist₁_trig hpl (fun i hi => by rw [hob i hi]) hm (by rw [h1]; rfl)
  have hrun := chkRun_safe hs hpl hm
  simp only [h1, h₁] at hrun
  exact init_of_chkRun δ bl c₀ var hrun

/-- **The Eq claim**: when plays are safe, the waiting moves are harmless before round `m`, and
player 1 triggered at round `m` outputs `w`, then player 0 triggered at round `m` outputs `w`, and
in the safety variant `w` has no halting head. -/
theorem claim_eq (hs : SafePlays δ bl c₀ var σ₀ σ₁) {m : ℕ} (hm1 : 1 ≤ m)
    (hq : QuietBefore δ var σ₀ σ₁ m) {w : List (Cell Q Γ)}
    (hA₁ : ∀ j ≤ w.length, σ₁ (trig m j) = rowMove w j) :
    (∀ j ≤ w.length, σ₀ (trig m j) = rowMove w j) ∧ (var = .safety → hasHalt δ w = false) := by
  set f := buildPlay δ bl c₀ var σ₀ σ₁ (waitPol false m (.eq true false false)) with hf
  obtain ⟨hw, h1⟩ := waitPol_play (δ := δ) (bl := bl) (c₀ := c₀) (var := var) (σ₀ := σ₀)
    (σ₁ := σ₁) (b := false) (p := .eq true false false) hm1 (hq.mono (by omega)) (by
      rw [succs_waiting (by split_ifs <;> rfl)
        (fun hv => (hq (m - 1) (by omega)).1 (by simpa using hv) |> fun h => by
          simpa [show m - 1 + 1 = m by omega] using h)
        (fun hv hne => by
          have := (hq (m - 1) (by omega)).2 hv
          rw [show m - 1 + 1 = m by omega] at this
          refine this ?_
          by_contra h0
          exact hne (by simp [show m - 1 = 0 by omega]))]
      split_ifs <;> simp [natureMoves])
  rw [← hf] at hw h1
  have hpl : IsPlayA δ bl c₀ var σ₀ σ₁ f := buildPlay_isPlay δ bl c₀ var σ₀ σ₁ _
  have hm : isWaiting (f m) = false := by rw [h1]; rfl
  have hob := observe_waitPol hw
  have h₀ : ∀ j, hist₀ f (m + j) = trig m j :=
    hist₀_trig hpl (fun i hi => by rw [hob i hi]) hm (by rw [h1]; rfl)
  have h₁ : ∀ j, hist₁ f (m + j) = trig m j :=
    hist₁_trig hpl (fun i hi => by rw [hob i hi]) hm (by rw [h1]; rfl)
  have hrun := chkRun_safe hs hpl hm
  simp only [h1, h₀, h₁] at hrun
  exact ⟨agree_of_eq δ bl c₀ var hrun hA₁, noHalt_of_eq δ bl c₀ var hrun hA₁⟩

/-- After an output of player 0, the Succ check triggers player 1. -/
theorem observe_chk_succ₀ {a₀ a₁ : Move Q Γ} (h : chk δ bl c₀ .succ₀ a₀ a₁ ≠ .err) :
    (observe (chk δ bl c₀ .succ₀ a₀ a₁)).2 = true := by
  rcases a₀ with x | _ | _ | _ <;> simp_all [chk, observe]

/-- **The Succ claim**: when plays are safe, the waiting moves are harmless before round `m`, and
player 0 triggered at round `m` outputs `u`, then player 1 triggered at round `m + 1` outputs the
row after `u`. -/
theorem claim_succ (hs : SafePlays δ bl c₀ var σ₀ σ₁) {m : ℕ} (hm1 : 1 ≤ m)
    (hq : QuietBefore δ var σ₀ σ₁ m) {u : List (Cell Q Γ)}
    (hA₀ : ∀ j ≤ u.length, σ₀ (trig m j) = rowMove u j) :
    ∀ j ≤ u.length + 1, σ₁ (trig (m + 1) j) = rowMove (succWord δ bl u) j := by
  set f := buildPlay δ bl c₀ var σ₀ σ₁ (waitPol true m .succ₀) with hf
  obtain ⟨hw, h1⟩ := waitPol_play (δ := δ) (bl := bl) (c₀ := c₀) (var := var) (σ₀ := σ₀)
    (σ₁ := σ₁) (b := true) (p := .succ₀) hm1 (hq.mono (by omega)) (by
      rw [succs_waiting (by split_ifs <;> rfl)
        (fun hv => (hq (m - 1) (by omega)).1 (by simpa using hv) |> fun h => by
          simpa [show m - 1 + 1 = m by omega] using h)
        (fun hv hne => by
          have := (hq (m - 1) (by omega)).2 hv
          rw [show m - 1 + 1 = m by omega] at this
          refine this ?_
          by_contra h0
          exact hne (by simp [show m - 1 = 0 by omega]))]
      split_ifs <;> simp [natureMoves])
  rw [← hf] at hw h1
  have hpl : IsPlayA δ bl c₀ var σ₀ σ₁ f := buildPlay_isPlay δ bl c₀ var σ₀ σ₁ _
  have hm : isWaiting (f m) = false := by rw [h1]; rfl
  have hob := observe_waitPol hw
  have h₀ : ∀ j, hist₀ f (m + j) = trig m j :=
    hist₀_trig hpl (fun i hi => by rw [hob i hi]) hm (by rw [h1]; rfl)
  have hrun := chkRun_safe hs hpl hm
  have hf1 : f (m + 1) = chk δ bl c₀ .succ₀ (σ₀ (hist₀ f m)) (σ₁ (hist₁ f m)) := by
    rw [play_eq_chkRun hpl hm 1, h1]
    exact stepC_of_ne δ bl c₀ var rfl (by simpa [h1, chkRun] using (hrun 1).2)
  have hm' : isWaiting (f (m + 1)) = false := by
    rw [play_eq_chkRun hpl hm 1]
    exact isWaiting_stepC δ bl c₀ var _ _ hm
  have h₁ : ∀ j, hist₁ f (m + 1 + j) = trig (m + 1) j := by
    refine hist₁_trig hpl (fun i hi => ?_) hm' ?_
    · rcases Nat.lt_or_ge i m with him | him
      · rw [hob i him]
      · rw [show i = m by omega, h1]; rfl
    · rw [hf1]
      refine observe_chk_succ₀ ?_
      rw [← hf1, play_eq_chkRun hpl hm 1]
      exact (hrun 1).1
  simp only [h1] at hrun
  have key := succ_of_chkRun δ bl c₀ var hrun (u := u) fun j hj => by
    simp only [h₀]; exact hA₀ j hj
  intro j hj
  have := key j hj
  simp only [show m + (j + 1) = m + 1 + j by omega, h₁] at this
  exact this

/-- **The stop claim**: in the reachability variant, when plays are safe, player 0 stops at
round `n ≥ 1` after harmless waiting moves, and player 1 triggered at round `n + 1` outputs `w`,
then `w` has a halting head. -/
theorem claim_stop (hs : SafePlays δ bl c₀ .reach σ₀ σ₁) {n : ℕ} (hn1 : 1 ≤ n)
    (hq : QuietBefore δ .reach σ₀ σ₁ n) (hstop : σ₀ (List.replicate (n + 1) false) = .stop)
    {w : List (Cell Q Γ)} (hA₁ : ∀ j ≤ w.length, σ₁ (trig (n + 1) j) = rowMove w j) :
    hasHalt δ w = true := by
  set f := buildPlay δ bl c₀ .reach σ₀ σ₁ (waitPol false (n + 1) (.eq true true false)) with hf
  obtain ⟨hw, h1⟩ := waitPol_play (δ := δ) (bl := bl) (c₀ := c₀) (var := .reach) (σ₀ := σ₀)
    (σ₁ := σ₁) (b := false) (m := n + 1) (p := .eq true true false) (by omega) (by simpa using hq)
    (by
      simp only [Nat.add_sub_cancel, show n ≠ 0 by omega, ↓reduceIte, hstop]
      simp [succs, isSink, isWaiting])
  rw [← hf] at hw h1
  have hpl : IsPlayA δ bl c₀ .reach σ₀ σ₁ f := buildPlay_isPlay δ bl c₀ .reach σ₀ σ₁ _
  have hm : isWaiting (f (n + 1)) = false := by rw [h1]; rfl
  have hob := observe_waitPol hw
  have h₀ : ∀ j, hist₀ f (n + 1 + j) = trig (n + 1) j :=
    hist₀_trig hpl (fun i hi => by rw [hob i hi]) hm (by rw [h1]; rfl)
  have h₁ : ∀ j, hist₁ f (n + 1 + j) = trig (n + 1) j :=
    hist₁_trig hpl (fun i hi => by rw [hob i hi]) hm (by rw [h1]; rfl)
  have hrun := chkRun_safe hs hpl hm
  simp only [h1, h₀, h₁] at hrun
  exact hasHalt_of_stop δ bl c₀ .reach hrun hA₁ rfl

end Scenarios


end DiagonaLean.TeamGame
