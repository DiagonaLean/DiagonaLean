/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CFGame.Target

@[expose] public section

/-! # Renaming the states of the simulation game

Renaming the states of a machine by `f` renames the letters of its simulation game
(`Letter.mapQ`). The rules of the game for the renamed machine are the renamed rules
(`rules_mapQ`), the target for the renamed states is the renamed target when `f` is injective
(`target_mapQ`), and the word of a renamed configuration is the renamed word (`cfgWord_mapQ`). So a
game built on a finite type of states can be read on the states it is renamed to.

## Main statements

* `rules_mapQ`, `target_mapQ`, `cfgWord_mapQ`: renaming commutes with the construction.
-/

namespace DiagonaLean.CFGame.Simulation

open DiagonaLean.Foundations.Computability.ListMachine RegularExpression

variable {Q Q' Γ : Type} (f : Q → Q')

/-- The letter with its state renamed by `f`. -/
def Letter.mapQ : Letter Q Γ → Letter Q' Γ
  | .dollar => .dollar
  | .endm => .endm
  | .tape c => .tape c
  | .head q c => .head (f q) c
  | .rmark q c => .rmark (f q) c
  | .lmark q c => .lmark (f q) c
  | .halt => .halt
  | .objTape => .objTape
  | .objHead => .objHead
  | .objR => .objR
  | .objL => .objL

/-- The letter of a renamed transition is the renamed letter. -/
theorem actLetter_mapAct (a : Act Q Γ) : actLetter (mapAct f a) = (actLetter a).mapQ f := by
  cases a <;> rfl

/-- **The rules of the game for a renamed machine are the renamed rules.** -/
theorem rules_mapQ {δ : Q → Γ → Act Q Γ} {δ' : Q' → Γ → Act Q' Γ}
    (hδ : ∀ q c, δ' (f q) c = mapAct f (δ q c)) (qs : List Q) (cs : List Γ) (bl : Γ) :
    (rules δ qs cs bl).map (fun r => (r.1.mapQ f, r.2.1.mapQ f, r.2.2.map (Letter.mapQ f))) =
      rules δ' (qs.map f) cs bl := by
  simp [rules, List.map_flatMap, List.flatMap_map, hδ, actLetter_mapAct, Letter.mapQ,
    Function.comp_def]

/-- The renamed letters are the letters of the renamed states. -/
theorem letters_mapQ (qs : List Q) (cs : List Γ) :
    (letters qs cs).map (Letter.mapQ f) = letters (qs.map f) cs := by
  simp [letters, List.map_flatMap, List.flatMap_map, Letter.mapQ, Function.comp_def]

/-- Renaming keeps a letter an objection. -/
theorem isObjB_mapQ (x : Letter Q Γ) : isObjB (x.mapQ f) = isObjB x := by
  cases x <;> rfl

/-- Renaming keeps a letter a head, a marker or neither. -/
theorem isActiveB_mapQ (x : Letter Q Γ) : isActiveB (x.mapQ f) = isActiveB x := by
  cases x <;> rfl

/-- Renaming keeps a letter a head or not. -/
theorem isHeadB_mapQ (x : Letter Q Γ) : isHeadB (x.mapQ f) = isHeadB x := by
  cases x <;> rfl

/-- A sum of renamed expressions is the renamed sum. -/
theorem sumRE_map {α β : Type} (g : α → β) (l : List (RegularExpression α)) :
    (sumRE l).map g = sumRE (l.map (·.map g)) := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [sumRE, RegularExpression.map] at ih ⊢; rw [ih]

/-- A renamed pattern is the pattern of the renamed lists. -/
theorem pattern_map {α β : Type} (g : α → β) (l m : List α) :
    (pattern l m).map g = pattern (l.map g) (m.map g) := by
  have hw : ∀ m : List α, (wordRE m).map g = wordRE (m.map g) := by
    intro m
    induction m with
    | nil => rfl
    | cons x m ih => simp [wordRE, RegularExpression.map] at ih ⊢; rw [ih]
  simp [pattern, anyOf, RegularExpression.map, sumRE_map, hw, List.map_map, Function.comp_def]

variable {f}

/-- **The target for injectively renamed states is the renamed target.** -/
theorem target_mapQ [DecidableEq Q] [DecidableEq Q'] (hf : Function.Injective f) (qs : List Q)
    (cs : List Γ) : (target qs cs).map (Letter.mapQ f) = target (qs.map f) cs := by
  have hn : (nonObj qs cs).map (Letter.mapQ f) = nonObj (qs.map f) cs := by
    simp only [nonObj, ← letters_mapQ f, List.filter_map, Function.comp_def, isObjB_mapQ]
  have hq : (quiet qs cs).map (Letter.mapQ f) = quiet (qs.map f) cs := by
    simp only [quiet, ← letters_mapQ f, List.filter_map, Function.comp_def, isObjB_mapQ,
      isActiveB_mapQ]
  have hh : (headless qs cs).map (Letter.mapQ f) = headless (qs.map f) cs := by
    simp only [headless, ← letters_mapQ f, List.filter_map, Function.comp_def, isObjB_mapQ,
      isHeadB_mapQ]
  simp only [target, sumRE_map, pattern_map, hn, hq, hh, List.map_cons, List.map_append,
    List.map_flatMap, List.flatMap_map, hf.eq_iff, apply_ite, List.map_nil, Letter.mapQ]

/-- The word of a renamed configuration is the renamed word. -/
theorem cfgWord_mapQ (k : Cfg Q Γ) : cfgWord (mapCfg f k) = (cfgWord k).map (Letter.mapQ f) := by
  simp [cfgWord, frame, mapCfg, Letter.mapQ, List.map_reverse, Function.comp_def]

end DiagonaLean.CFGame.Simulation
