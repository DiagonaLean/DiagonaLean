/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.TeamGame.Machine

@[expose] public section

/-! # The game of a list machine

Two players and Nature play on the rows of a list machine, after D. Berwanger and Ł. Kaiser.
Nature picks a check in secret and waits; when it triggers a player, the player outputs a row,
one cell per round, then `fin`. The positions of the game check the outputs against each other
(`chk`): in the Init check player 1 outputs the initial row; in the Eq check both players output
the same row; in the Succ check player 0 starts one round before player 1, and player 1 outputs
the row after player 0's by the local rule. A player cannot tell which check is running, so a
winning pair of strategies outputs the rows of the tableau.

The game has two variants (`Variant`). In the safety variant, an output halting head is losing.
In the reachability variant, player 0 can stop the waiting with `stop`; this triggers both players
for an Eq check that also needs a halting head, and every passed check is winning.

## References

* D. Berwanger, Ł. Kaiser, *Information tracking in distributed games*, talk at ACTS 2010 (slides)
-/

namespace DiagonaLean.TeamGame

open DiagonaLean.Foundations.Computability.ListMachine

variable {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-- An action: output a cell, end the output, stop the waiting, or nothing. -/
inductive Move (Q Γ : Type) where
  /-- Output a cell. -/
  | out (x : Cell Q Γ)
  /-- End the output. -/
  | fin
  /-- Stop the waiting (player 0, reachability variant). -/
  | stop
  /-- No action. -/
  | idle
  deriving DecidableEq, Encodable

/-- A position of the game. -/
inductive Pos (Q Γ : Type) where
  /-- The start, where Nature picks the check. -/
  | start
  /-- Waiting before an Eq check (`false`) or a Succ check (`true`). -/
  | wait (succ : Bool)
  /-- The Init check: player 1 must output cell `i` of the initial row next; `first` marks its
  trigger round. -/
  | init (i : ℕ) (first : Bool)
  /-- The Eq check; `stopMode` also needs a halting head, and `seen` records one. -/
  | eq (first stopMode seen : Bool)
  /-- The Succ check, at player 0's trigger round. -/
  | succ₀
  /-- The Succ check at player 1's cell `j`: `l` and `m` are player 0's cells `j - 1` (`none` at
  the border) and `j`; `c` counts the rounds since player 0's `fin` (`0`: not yet). -/
  | succ (first : Bool) (l : Option (Cell Q Γ)) (m : Cell Q Γ) (c : ℕ)
  /-- A passed check. -/
  | ok
  /-- A failed check. -/
  | err
  /-- An output halting head (safety variant). -/
  | hlt
  deriving DecidableEq, Encodable

/-- The default action is `idle`. -/
instance : Inhabited (Move Q Γ) := ⟨.idle⟩

/-- The default position is the start. -/
instance : Inhabited (Pos Q Γ) := ⟨.start⟩

/-- The two variants of the game. -/
inductive Variant where
  /-- The team must avoid failed checks and halting heads. -/
  | safety
  /-- The team must pass a check; player 0 can stop the waiting. -/
  | reach
  deriving DecidableEq

/-- The observations of the two players at a position: `true` at the player's trigger round. -/
def observe : Pos Q Γ → Bool × Bool
  | .eq true _ _ => (true, true)
  | .succ₀ => (true, false)
  | .succ true _ _ _ => (false, true)
  | .init _ true => (false, true)
  | _ => (false, false)

/-- A cell is a halting head, as a test. -/
def isHaltCellB (δ : Q → Γ → Act Q Γ) : Cell Q Γ → Bool
  | .head q c =>
    match δ q c with
    | .halt => true
    | _ => false
  | .plain _ => false

/-- The deterministic step of a checking position, for the moves `a₀` and `a₁` of the two players.
`c₀` is the initial row, as a list of cells. -/
def chk (δ : Q → Γ → Act Q Γ) (bl : Γ) (c₀ : List (Cell Q Γ)) :
    Pos Q Γ → Move Q Γ → Move Q Γ → Pos Q Γ
  | .init i _, _, a₁ =>
    if h : i < c₀.length then
      (if a₁ = .out c₀[i] then .init (i + 1) false else .err)
    else (if a₁ = .fin then .ok else .err)
  | .eq _ s seen, .out x, .out y =>
    if x = y then .eq false s (seen || isHaltCellB δ x) else .err
  | .eq _ s seen, .fin, .fin => if s && !seen then .err else .ok
  | .eq _ _ _, _, _ => .err
  | .succ₀, .out x, _ => .succ true none x 0
  | .succ₀, .fin, _ => .succ true none (.plain bl) 1
  | .succ₀, _, _ => .err
  | .succ _ l m 0, .out x, .out y =>
    if y = localRule δ l m x then .succ false (some m) x 0 else .err
  | .succ _ l m 0, .fin, .out y =>
    if y = localRule δ l m (.plain bl) then .succ false (some m) (.plain bl) 1 else .err
  | .succ _ l m 1, _, .out y =>
    if y = localRule δ l m (.plain bl) then .succ false (some m) (.plain bl) 2 else .err
  | .succ _ _ _ 2, _, .fin => .ok
  | p, _, _ => if p = .ok then .ok else .err

/-- A position where Nature waits. -/
def isWaiting : Pos Q Γ → Bool
  | .start | .wait _ => true
  | _ => false

/-- A sink position. -/
def isSink : Pos Q Γ → Bool
  | .ok | .err | .hlt => true
  | _ => false

/-- A move outputs a halting head, as a test. -/
def haltMove (δ : Q → Γ → Act Q Γ) : Move Q Γ → Bool
  | .out x => isHaltCellB δ x
  | _ => false

/-- The positions Nature may move to from a waiting position when player 0 does not stop. -/
def natureMoves : Pos Q Γ → List (Pos Q Γ)
  | .start => [.wait false, .wait true, .init 0 true, .eq true false false, .succ₀]
  | .wait false => [.wait false, .eq true false false]
  | .wait true => [.wait true, .succ₀]
  | _ => []

/-- The successors of a position for the moves `a₀` and `a₁`: Nature's choices while waiting, the
deterministic check, or the sink itself. In the safety variant an output halting head leads to
`hlt`; in the reachability variant player 0's `stop` at a waiting position other than the start
triggers the stop check, so the Init check stays available at round 1. -/
def succs (δ : Q → Γ → Act Q Γ) (bl : Γ) (c₀ : List (Cell Q Γ)) (var : Variant)
    (p : Pos Q Γ) (a₀ a₁ : Move Q Γ) : List (Pos Q Γ) :=
  if isSink p then [p]
  else if var = .safety && (haltMove δ a₀ || haltMove δ a₁) then [.hlt]
  else if isWaiting p then
    (if var = .reach && a₀ = .stop && p != .start then [.eq true true false] else natureMoves p)
  else [chk δ bl c₀ p a₀ a₁]

/-! ### Plays -/

section Plays

variable (δ : Q → Γ → Act Q Γ) (bl : Γ) (c₀ : List (Cell Q Γ)) (var : Variant)

/-- The observations of player 0 at the first `k + 1` positions of a play. -/
def hist₀ (f : ℕ → Pos Q Γ) (k : ℕ) : List Bool :=
  (List.range (k + 1)).map fun j => (observe (f j)).1

/-- The observations of player 1 at the first `k + 1` positions of a play. -/
def hist₁ (f : ℕ → Pos Q Γ) (k : ℕ) : List Bool :=
  (List.range (k + 1)).map fun j => (observe (f j)).2

/-- `f` is a play in which player 0 follows `σ₀` and player 1 follows `σ₁`. -/
def IsPlayA (σ₀ σ₁ : List Bool → Move Q Γ) (f : ℕ → Pos Q Γ) : Prop :=
  f 0 = .start ∧ ∀ k, f (k + 1) ∈ succs δ bl c₀ var (f k) (σ₀ (hist₀ f k)) (σ₁ (hist₁ f k))

/-- The team wins the reachability variant: it has strategies making every play pass a check. -/
def WinReach : Prop :=
  ∃ σ₀ σ₁ : List Bool → Move Q Γ, ∀ f, IsPlayA δ bl c₀ .reach σ₀ σ₁ f → ∃ k, f k = .ok

/-- The team wins the safety variant: it has strategies making every play avoid failed checks and
halting heads. -/
def WinSafety : Prop :=
  ∃ σ₀ σ₁ : List Bool → Move Q Γ, ∀ f, IsPlayA δ bl c₀ .safety σ₀ σ₁ f →
    ∀ k, f k ≠ .err ∧ f k ≠ .hlt

/-- The successors of every position are non-empty. -/
theorem succs_ne_nil (p : Pos Q Γ) (a₀ a₁ : Move Q Γ) : succs δ bl c₀ var p a₀ a₁ ≠ [] := by
  unfold succs
  split_ifs <;> try simp
  rcases p with _ | ⟨_ | _⟩ | _ <;> simp_all [isWaiting, natureMoves]

/-- The positions of the play built from the policy `pol` of Nature, up to round `k`: at each
round Nature moves to the position `pol` proposes if it is a successor, and otherwise to the first
successor. -/
def buildPrefix (σ₀ σ₁ : List Bool → Move Q Γ) (pol : ℕ → Pos Q Γ → Pos Q Γ) :
    ℕ → List (Pos Q Γ)
  | 0 => [.start]
  | k + 1 =>
    let ps := buildPrefix σ₀ σ₁ pol k
    let p := ps.getLast?.getD .start
    let cs := succs δ bl c₀ var p (σ₀ (ps.map fun x => (observe x).1))
      (σ₁ (ps.map fun x => (observe x).2))
    ps ++ [if pol k p ∈ cs then pol k p else cs.headD p]

/-- The play built from the policy `pol` of Nature. -/
def buildPlay (σ₀ σ₁ : List Bool → Move Q Γ) (pol : ℕ → Pos Q Γ → Pos Q Γ) (k : ℕ) : Pos Q Γ :=
  (buildPrefix δ bl c₀ var σ₀ σ₁ pol k).getLast?.getD .start

/-- The prefix of a built play lists its positions. -/
theorem buildPrefix_eq (σ₀ σ₁ : List Bool → Move Q Γ) (pol : ℕ → Pos Q Γ → Pos Q Γ) (k : ℕ) :
    buildPrefix δ bl c₀ var σ₀ σ₁ pol k =
      (List.range (k + 1)).map (buildPlay δ bl c₀ var σ₀ σ₁ pol) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, ← ih]
    simp [buildPlay, buildPrefix]

/-- A built play moves to the position Nature's policy proposes when it is a successor. -/
theorem buildPlay_succ (σ₀ σ₁ : List Bool → Move Q Γ) (pol : ℕ → Pos Q Γ → Pos Q Γ) (k : ℕ) :
    let f := buildPlay δ bl c₀ var σ₀ σ₁ pol
    let cs := succs δ bl c₀ var (f k) (σ₀ (hist₀ f k)) (σ₁ (hist₁ f k))
    f (k + 1) = if pol k (f k) ∈ cs then pol k (f k) else cs.headD (f k) := by
  intro f cs
  have hk := buildPrefix_eq δ bl c₀ var σ₀ σ₁ pol k
  show (buildPrefix δ bl c₀ var σ₀ σ₁ pol (k + 1)).getLast?.getD .start = _
  simp only [buildPrefix, hk, List.map_map]
  simp [List.getLast?_map, List.getLast?_range, f, cs, hist₀, hist₁, Function.comp_def]

/-- A built play is a play. -/
theorem buildPlay_isPlay (σ₀ σ₁ : List Bool → Move Q Γ) (pol : ℕ → Pos Q Γ → Pos Q Γ) :
    IsPlayA δ bl c₀ var σ₀ σ₁ (buildPlay δ bl c₀ var σ₀ σ₁ pol) := by
  refine ⟨rfl, fun k => ?_⟩
  rw [buildPlay_succ]
  split_ifs with h
  · exact h
  · have hne := succs_ne_nil δ bl c₀ var (buildPlay δ bl c₀ var σ₀ σ₁ pol k)
      (σ₀ (hist₀ (buildPlay δ bl c₀ var σ₀ σ₁ pol) k))
      (σ₁ (hist₁ (buildPlay δ bl c₀ var σ₀ σ₁ pol) k))
    revert hne
    cases succs δ bl c₀ var _ _ _ <;> simp

end Plays

end DiagonaLean.TeamGame
