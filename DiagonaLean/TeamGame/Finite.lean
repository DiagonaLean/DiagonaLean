/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.TeamGame.Construction

@[expose] public section

/-! # The positions and actions of the game of a list machine, as finite lists

From complete lists of states and tape symbols, `allCells`, `allMoves` and `allPos` list the cells,
the actions, and the positions of the game whose Init counter is at most `n`
(`mem_allCells`, `mem_allMoves`, `mem_allPos`). For `n` the length of the initial row, the
successors of a listed position are listed (`succs_closed`).
-/

namespace DiagonaLean.TeamGame

open DiagonaLean.Foundations.Computability.ListMachine

variable {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-- The cells with states from `qs` and symbols from `cs`. -/
def allCells (qs : List Q) (cs : List Γ) : List (Cell Q Γ) :=
  cs.map .plain ++ qs.flatMap fun q => cs.map (.head q)

/-- The actions with cells from `allCells qs cs`. -/
def allMoves (qs : List Q) (cs : List Γ) : List (Move Q Γ) :=
  (allCells qs cs).map .out ++ [.fin, .stop, .idle]

/-- The positions with cells from `allCells qs cs` and Init counter at most `n`. -/
def allPos (qs : List Q) (cs : List Γ) (n : ℕ) : List (Pos Q Γ) :=
  [.start, .wait false, .wait true, .succ₀, .ok, .err, .hlt] ++
    (List.range (n + 1)).flatMap (fun i => [.init i true, .init i false]) ++
    [false, true].flatMap (fun a => [false, true].flatMap fun b =>
      [false, true].map fun c => .eq a b c) ++
    [false, true].flatMap fun b => (none :: (allCells qs cs).map some).flatMap fun l =>
      (allCells qs cs).flatMap fun m => (List.range 3).map fun c => .succ b l m c

/-- A position with Init counter at most `n` and Succ counter at most `2`. -/
def Bounded (n : ℕ) : Pos Q Γ → Prop
  | .init i _ => i ≤ n
  | .succ _ _ _ c => c ≤ 2
  | _ => True

section Lists

variable {qs : List Q} {cs : List Γ} (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs)
include hqs hcs

omit [DecidableEq Q] [DecidableEq Γ] in
/-- Every cell is listed. -/
theorem mem_allCells (x : Cell Q Γ) : x ∈ allCells qs cs := by
  rcases x with c | ⟨q, c⟩ <;> simp [allCells, hqs, hcs]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- Every action is listed. -/
theorem mem_allMoves (a : Move Q Γ) : a ∈ allMoves qs cs := by
  rcases a with x | _ | _ | _ <;> simp [allMoves, mem_allCells hqs hcs]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- The listed positions are the bounded ones. -/
theorem mem_allPos {n : ℕ} (p : Pos Q Γ) : p ∈ allPos qs cs n ↔ Bounded n p := by
  rcases p with _ | b | ⟨i, b⟩ | ⟨a, b, c⟩ | _ | ⟨b, l, m, c⟩ | _ | _ | _ <;>
    simp [allPos, Bounded, mem_allCells hqs hcs]
  · constructor
    · rintro ⟨a, ha, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ <;> exact ha
    · intro hi; cases b <;> simp [hi]
  · cases a <;> cases b <;> cases c <;> simp
  · rcases l with _ | l <;> cases b <;> simp <;> omega

end Lists

/-- A step of a check keeps positions bounded by the length of the initial row. -/
theorem bounded_chk (δ : Q → Γ → Act Q Γ) (bl : Γ) (c₀ : List (Cell Q Γ)) {p : Pos Q Γ}
    (hp : Bounded c₀.length p) (a₀ a₁ : Move Q Γ) : Bounded c₀.length (chk δ bl c₀ p a₀ a₁) := by
  unfold chk
  split <;> (try split_ifs) <;> simp_all [Bounded]

/-- The successors of a bounded position are bounded. -/
theorem bounded_succs (δ : Q → Γ → Act Q Γ) (bl : Γ) (c₀ : List (Cell Q Γ)) (var : Variant)
    {p p' : Pos Q Γ} (hp : Bounded c₀.length p) {a₀ a₁ : Move Q Γ}
    (h : p' ∈ succs δ bl c₀ var p a₀ a₁) : Bounded c₀.length p' := by
  unfold succs at h
  split_ifs at h
  · rw [List.mem_singleton] at h; rw [h]; exact hp
  · rw [List.mem_singleton] at h; rw [h]; trivial
  · rw [List.mem_singleton] at h; rw [h]; trivial
  · rcases p with _ | b <;> simp [natureMoves] at h
    · rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [Bounded]
    · cases b <;> simp at h <;> rcases h with rfl | rfl <;> trivial
  · rw [List.mem_singleton] at h; rw [h]; exact bounded_chk δ bl c₀ hp a₀ a₁

/-- **The listed positions are closed under successors**, for the length of the initial row. -/
theorem succs_closed {qs : List Q} {cs : List Γ} (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs)
    (δ : Q → Γ → Act Q Γ) (bl : Γ) (c₀ : List (Cell Q Γ)) (var : Variant) :
    ∀ p ∈ allPos qs cs c₀.length, ∀ a₀ a₁, ∀ p' ∈ succs δ bl c₀ var p a₀ a₁,
      p' ∈ allPos qs cs c₀.length := fun _ hp _ _ _ h =>
  (mem_allPos hqs hcs _).2 (bounded_succs δ bl c₀ var ((mem_allPos hqs hcs _).1 hp) h)

end DiagonaLean.TeamGame
