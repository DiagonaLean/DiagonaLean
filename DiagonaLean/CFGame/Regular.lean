/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.Computability.RegularExpression
import DiagonaLean.Foundations.Computability.DerivePrimrec

@[expose] public section

/-! # Regular expressions for finite unions and fixed words

The sum of a list of regular expressions matches the union of their languages (`mem_sumRE`).
`anyOf l` matches one letter of the list `l` (`mem_anyOf`), and its star matches the words whose
letters are all in `l` (`mem_star_anyOf`). `wordRE m` matches the word `m` alone (`mem_wordRE`),
and `pattern l m` matches the words `u ++ m ++ v` whose letters outside `m` are in `l`
(`mem_pattern`). Renaming letters commutes with the four constructions (`sumRE_map`,
`wordRE_map`, `pattern_map`), and they are primitive recursive (`derive_primrec`).
-/

namespace DiagonaLean.CFGame

open RegularExpression DiagonaLean.Foundations.Computability

variable {α : Type}

/-- The sum of a list of regular expressions. -/
def sumRE (l : List (RegularExpression α)) : RegularExpression α := l.foldr (· + ·) 0

/-- A word matches a sum iff it matches one of its terms. -/
theorem mem_sumRE {l : List (RegularExpression α)} {w : List α} :
    w ∈ (sumRE l).matches' ↔ ∃ e ∈ l, w ∈ e.matches' := by
  induction l with
  | nil => simp [sumRE, matches'_zero]
  | cons e l ih =>
    simp only [sumRE, List.foldr_cons, matches'_add, Language.mem_add] at ih ⊢
    rw [ih]
    simp

/-- The regular expression for one letter of a list. -/
def anyOf (l : List α) : RegularExpression α := sumRE (l.map char)

/-- A word matches `anyOf l` iff it is one letter of `l`. -/
theorem mem_anyOf {l : List α} {w : List α} : w ∈ (anyOf l).matches' ↔ ∃ x ∈ l, w = [x] := by
  simp only [anyOf, mem_sumRE, List.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hw⟩
    exact ⟨x, hx, hw⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨char x, ⟨x, hx, rfl⟩, rfl⟩

/-- The regular expression for a fixed word. -/
def wordRE (m : List α) : RegularExpression α := m.foldr (fun x e => char x * e) 1

/-- Only the word itself matches `wordRE m`. -/
theorem mem_wordRE {m w : List α} : w ∈ (wordRE m).matches' ↔ w = m := by
  induction m generalizing w with
  | nil => simp [wordRE, matches'_epsilon, Language.mem_one]
  | cons x m ih =>
    simp only [wordRE, List.foldr_cons, matches'_mul, matches'_char, Language.mem_mul] at ih ⊢
    constructor
    · rintro ⟨a, rfl, b, hb, rfl⟩
      rw [ih.1 hb]
      rfl
    · rintro rfl
      exact ⟨[x], rfl, m, ih.2 rfl, rfl⟩

/-- A word matches the star of `anyOf l` iff all its letters are in `l`. -/
theorem mem_star_anyOf {l : List α} {w : List α} :
    w ∈ (anyOf l).star.matches' ↔ ∀ x ∈ w, x ∈ l := by
  rw [matches'_star, Language.mem_kstar]
  constructor
  · rintro ⟨L, rfl, hL⟩ x hx
    obtain ⟨y, hy, hxy⟩ := List.mem_flatten.1 hx
    obtain ⟨z, hz, rfl⟩ := mem_anyOf.1 (hL y hy)
    simp only [List.mem_singleton] at hxy
    exact hxy ▸ hz
  · intro h
    refine ⟨w.map fun x => [x], ?_, ?_⟩
    · induction w with
      | nil => rfl
      | cons a w ih => simpa using ih fun x hx => h x (List.mem_cons_of_mem a hx)
    rintro _ hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact mem_anyOf.2 ⟨x, h x hx, rfl⟩

/-- The regular expression for the words `u ++ m ++ v` with all letters of `u` and `v` in `l`. -/
def pattern (l m : List α) : RegularExpression α :=
  (anyOf l).star * wordRE m * (anyOf l).star

/-- A word matches `pattern l m` iff it is `u ++ m ++ v` with all letters of `u` and `v` in `l`. -/
theorem mem_pattern {l m w : List α} :
    w ∈ (pattern l m).matches' ↔
      ∃ u v, w = u ++ m ++ v ∧ (∀ x ∈ u, x ∈ l) ∧ ∀ x ∈ v, x ∈ l := by
  simp only [pattern, matches'_mul, Language.mem_mul]
  constructor
  · rintro ⟨_, ⟨u, hu, m', hm', rfl⟩, v, hv, rfl⟩
    rw [mem_wordRE.1 hm']
    exact ⟨u, v, rfl, mem_star_anyOf.1 hu, mem_star_anyOf.1 hv⟩
  · rintro ⟨u, v, rfl, hu, hv⟩
    exact ⟨u ++ m, ⟨u, mem_star_anyOf.2 hu, m, mem_wordRE.2 rfl, rfl⟩, v,
      mem_star_anyOf.2 hv, rfl⟩

/-- A sum of renamed expressions is the renamed sum. -/
theorem sumRE_map {β : Type} (g : α → β) (l : List (RegularExpression α)) :
    (sumRE l).map g = sumRE (l.map (·.map g)) := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [sumRE, RegularExpression.map] at ih ⊢; rw [ih]

/-- The renamed expression of a word is the expression of the renamed word. -/
theorem wordRE_map {β : Type} (g : α → β) (m : List α) : (wordRE m).map g = wordRE (m.map g) := by
  induction m with
  | nil => rfl
  | cons x m ih => simp [wordRE, RegularExpression.map] at ih ⊢; rw [ih]

/-- A renamed pattern is the pattern of the renamed lists. -/
theorem pattern_map {β : Type} (g : α → β) (l m : List α) :
    (pattern l m).map g = pattern (l.map g) (m.map g) := by
  simp [pattern, anyOf, RegularExpression.map, sumRE_map, wordRE_map, List.map_map,
    Function.comp_def]

derive_primrec sumRE [Primcodable α]

derive_primrec anyOf [Primcodable α]

derive_primrec wordRE [Primcodable α]

derive_primrec pattern [Primcodable α]

end DiagonaLean.CFGame
