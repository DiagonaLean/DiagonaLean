/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Computability.RegularExpressions

@[expose] public section

/-! # Active context-free games

A context-free game over `α` is a finite list of rules `a → b :: x` (`Rules`), whose right sides are
non-empty, and a regular target language, given by a regular expression (`Game`). A letter is a
non-terminal if it is the left side of a rule. Two players, Juliet and Romeo, play on a word. In
each round Juliet picks a position holding a non-terminal `a`, and Romeo replaces it by the right
side of a rule for `a`. Juliet wins when the word enters the target language after some round;
a play that never does is won by Romeo. The game is a reachability game whose positions are the
words, so Juliet has a winning strategy from `w` exactly when one move of hers leads into the least
set of words that contains the target and is closed under her moves (`Reach`, `Wins`). The problem
asks, for a game and a word given together, whether Juliet wins from the word (`DecisionProblem`).
Juliet must move at least once: the word itself does not count, even when it is in the target.
Renaming letters injectively does not change the winner (`wins_map_iff`).

To audit the definition, read `Reach`, `Wins` and `decisionProblem_mk`; the last is pinned in
`scripts/HeadlineTest.lean`.

## Main definitions

* `Game`, `Reach G w`, `Wins G w`: games, the words from which Juliet reaches the target, and the
  words from which she wins.
* `DecisionProblem`: the problem on an instance `(G, w)`.

## References

* [A. Muscholl, T. Schwentick, L. Segoufin,
  *Active Context-Free Games*][MuschollSchwentickSegoufin2006], Section 2.1
-/

namespace DiagonaLean.CFGame

variable {α : Type}

/-- The rules of a game: a triple `(a, b, x)` is the rule `a → b :: x`. -/
abbrev Rules (α : Type) := List (α × α × List α)

/-- A context-free game: its rules and a regular expression for its target language. -/
abbrev Game (α : Type) := Rules α × RegularExpression α

/-- `a` is a non-terminal of the rules `R`: some rule of `R` has left side `a`. -/
def IsNonterminal (R : Rules α) (a : α) : Prop := ∃ r ∈ R, r.1 = a

/-- The word `w` is in the target of `G`, or Juliet can pick a position holding a non-terminal `a`
such that, whatever rule `a → b :: x` Romeo applies there, this holds again for the word reached. -/
inductive Reach (G : Game α) : List α → Prop
  /-- The word is in the target. -/
  | target {w : List α} (h : w ∈ G.2.matches') : Reach G w
  /-- Juliet picks the non-terminal `a` between `u` and `v`. -/
  | move {w : List α} (u v : List α) (a : α) (hw : w = u ++ a :: v)
      (ha : IsNonterminal G.1 a)
      (h : ∀ b x, (a, b, x) ∈ G.1 → Reach G (u ++ b :: x ++ v)) : Reach G w

/-- Juliet wins the game `G` from the word `w`: she can pick a position holding a non-terminal `a`
such that, whatever rule `a → b :: x` Romeo applies there, the word reached is in the target or
Juliet wins from it. The word `w` itself need not be in the target: Juliet wins only after a
round. -/
def Wins (G : Game α) (w : List α) : Prop :=
  ∃ u v a, w = u ++ a :: v ∧ IsNonterminal G.1 a ∧
    ∀ b x, (a, b, x) ∈ G.1 → Reach G (u ++ b :: x ++ v)

/-! ### The problem on instances, for the reductions and the computability statements -/

/-- **Active context-free games on an instance `(G, w)`**: `Wins G w`. Read it curried,
`decisionProblem_mk`. -/
def DecisionProblem (x : Game α × List α) : Prop := Wins x.1 x.2

/-- The problem on an instance `(G, w)` is the curried problem. -/
@[simp] theorem decisionProblem_mk (G : Game α) (w : List α) :
    DecisionProblem (G, w) ↔ Wins G w := Iff.rfl

/-! ### Renaming letters -/

section Map

variable {β : Type}

/-- The game with its letters renamed by `f`. -/
def Game.map (f : α → β) (G : Game α) : Game β :=
  (G.1.map fun r => (f r.1, f r.2.1, r.2.2.map f), G.2.map f)

variable {f : α → β} {G : Game α}

/-- A rule of the renamed game for a renamed letter `f a` is the renaming of a rule for `a`, when
`f` is injective. -/
theorem mem_map_rules (hf : Function.Injective f) {a : α} {b' : β} {x' : List β} :
    (f a, b', x') ∈ (G.map f).1 ↔ ∃ b x, (a, b, x) ∈ G.1 ∧ b' = f b ∧ x' = x.map f := by
  simp only [Game.map, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a₀, b, x⟩, hr, ha, rfl, rfl⟩
    obtain rfl := hf ha
    exact ⟨b, x, hr, rfl, rfl⟩
  · rintro ⟨b, x, hr, rfl, rfl⟩
    exact ⟨(a, b, x), hr, rfl, rfl, rfl⟩

/-- A renamed letter is a non-terminal of the renamed game iff the letter is one of the game, when
`f` is injective. -/
theorem isNonterminal_map (hf : Function.Injective f) {a : α} :
    IsNonterminal (G.map f).1 (f a) ↔ IsNonterminal G.1 a := by
  constructor
  · rintro ⟨⟨a', b', x'⟩, hr, rfl⟩
    obtain ⟨b, x, hr', -, -⟩ := (mem_map_rules hf).1 hr
    exact ⟨(a, b, x), hr', rfl⟩
  · rintro ⟨⟨a', b, x⟩, hr, rfl⟩
    exact ⟨(f a', f b, x.map f), (mem_map_rules hf).2 ⟨b, x, hr, rfl, rfl⟩, rfl⟩

/-- Renaming keeps winning words winning. -/
theorem reach_map (hf : Function.Injective f) {w : List α} (h : Reach G w) :
    Reach (G.map f) (w.map f) := by
  induction h with
  | target hw =>
    refine .target ?_
    rw [Game.map, RegularExpression.matches'_map]
    exact ⟨_, hw, rfl⟩
  | move u v a hw ha _ ih =>
    subst hw
    refine .move (u.map f) (v.map f) (f a) (by simp) ((isNonterminal_map hf).2 ha) ?_
    intro b' x' hr
    obtain ⟨b, x, hr', rfl, rfl⟩ := (mem_map_rules hf).1 hr
    simpa using ih b x hr'

/-- Renaming reflects winning words, when `f` is injective. -/
theorem reach_of_reach_map (hf : Function.Injective f) {w' : List β}
    (h : Reach (G.map f) w') : ∀ w : List α, w' = w.map f → Reach G w := by
  induction h with
  | target hw =>
    intro w rfl
    rw [Game.map, RegularExpression.matches'_map] at hw
    obtain ⟨w₀, hw₀, he⟩ := hw
    obtain rfl := (List.map_injective_iff.2 hf) he
    exact .target hw₀
  | move u' v' a' hw ha _ ih =>
    intro w hw'
    rw [hw'] at hw
    obtain ⟨u, r, rfl, rfl, hr⟩ := List.map_eq_append_iff.1 hw
    obtain ⟨a, v, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hr
    refine .move u v a rfl ((isNonterminal_map hf).1 ha) fun b x hbx => ?_
    exact ih (f b) (x.map f) ((mem_map_rules hf).2 ⟨b, x, hbx, rfl, rfl⟩) _ (by simp)

/-- **Juliet wins a renamed game iff she wins the game**, when the renaming is injective. -/
theorem wins_map_iff (hf : Function.Injective f) {w : List α} :
    Wins (G.map f) (w.map f) ↔ Wins G w := by
  constructor
  · rintro ⟨u', v', a', hw, ha, h⟩
    obtain ⟨u, r, rfl, rfl, hr⟩ := List.map_eq_append_iff.1 hw
    obtain ⟨a, v, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hr
    refine ⟨u, v, a, rfl, (isNonterminal_map hf).1 ha, fun b x hbx => ?_⟩
    exact reach_of_reach_map hf (h (f b) (x.map f) ((mem_map_rules hf).2 ⟨b, x, hbx, rfl, rfl⟩))
      _ (by simp)
  · rintro ⟨u, v, a, rfl, ha, h⟩
    refine ⟨u.map f, v.map f, f a, by simp, (isNonterminal_map hf).2 ha, fun b' x' hr => ?_⟩
    obtain ⟨b, x, hr', rfl, rfl⟩ := (mem_map_rules hf).1 hr
    simpa using reach_map hf (h b x hr')

end Map

end DiagonaLean.CFGame
