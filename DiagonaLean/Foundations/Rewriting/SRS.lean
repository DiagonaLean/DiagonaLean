/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic

@[expose] public section

/-! # String rewriting systems

A word over `T` is a list of letters (`Word T`), as in Mathlib's `Language`. A rule `l ⟶ r` has a
left side and a right side (`Rule`), and a string rewriting system, or semi-Thue system, is a finite
list of rules (`SRS`). One step replaces one occurrence of a left side, in context, by its right
side (`SRS.Step`):
```
  (l ⟶ r) ∈ R
  ─────────────────────────────────
  p ++ l ++ q  ⭢[R]  p ++ r ++ q
```
and derivability is the reflexive–transitive closure of a step (`SRS.Derives`, written `↠[R]`),
Mathlib's `Relation.ReflTransGen`. The step is an inductive relation with one constructor, as
Mathlib's `ContextFreeRule.Rewrites` and Cslib's `SKI.Red` are; `SRS.step_iff` is the same relation
as an existential, which proofs use when a word is not a variable.

A system is a list, so that reductions can build and read it as a program; derivability depends
only on its set of rules (`SRS.derives_congr`).

The notations `u ⭢[R] v` and `u ↠[R] v` are scoped: `open DiagonaLean.Foundations.Rewriting`.

## Main definitions

* `Word`, `Rule`, `SRS`, `SRS.Step`, `SRS.Derives`.

## Main statements

* `SRS.step_iff`: a step, as an existential.
* `SRS.Derives.append`, `SRS.derives_mono`, `SRS.derives_congr`: derivations concatenate, and
  depend only on the set of rules.
* `SRS.derives_start`: a fresh start symbol is used once, at the start of a derivation.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace DiagonaLean.Foundations.Rewriting

open Relation

/-- A word over the alphabet `T`: a finite list of letters. -/
abbrev Word (T : Type) := List T

/-- A rewriting rule `lhs ⟶ rhs` between words. -/
structure Rule (T : Type) where
  /-- The left side, which a step replaces. -/
  lhs : Word T
  /-- The right side, which a step puts in its place. -/
  rhs : Word T
  deriving DecidableEq, Repr

/-- A rule as the pair of its sides. -/
def Rule.toPair {T : Type} (ρ : Rule T) : Word T × Word T := (ρ.lhs, ρ.rhs)

/-- A string rewriting system (semi-Thue system): a finite list of rules. -/
abbrev SRS (T : Type) := List (Rule T)

variable {T : Type}

/-- **One rewriting step**: one occurrence of the left side of a rule, in a context `p`, `q`, is
replaced by its right side. -/
inductive SRS.Step (R : SRS T) : Word T → Word T → Prop
  /-- `p ++ l ++ q` rewrites to `p ++ r ++ q`, for a rule `l ⟶ r` of `R`. -/
  | rule {ρ : Rule T} (h : ρ ∈ R) (p q : Word T) : SRS.Step R (p ++ ρ.lhs ++ q) (p ++ ρ.rhs ++ q)

/-- **Derivability**: the reflexive–transitive closure of a step. -/
abbrev SRS.Derives (R : SRS T) : Word T → Word T → Prop := ReflTransGen R.Step

/-- `u ⭢[R] v`: `u` rewrites to `v` in one step of `R`. -/
scoped notation:50 u:51 " ⭢[" R "] " v:51 => SRS.Step R u v

/-- `u ↠[R] v`: `u` rewrites to `v` in finitely many steps of `R`. -/
scoped notation:50 u:51 " ↠[" R "] " v:51 => SRS.Derives R u v

namespace SRS

variable {R : SRS T}

/-- **A step, as an existential**: some rule of `R` applies to `u` in some context and gives `v`. -/
theorem step_iff {u v : Word T} :
    u ⭢[R] v ↔ ∃ ρ ∈ R, ∃ p q, u = p ++ ρ.lhs ++ q ∧ v = p ++ ρ.rhs ++ q := by
  constructor
  · rintro ⟨h, p, q⟩
    exact ⟨_, h, p, q, rfl, rfl⟩
  · rintro ⟨ρ, h, p, q, rfl, rfl⟩
    exact .rule h p q

/-- A step stays a step with a word added on the left. -/
theorem Step.append_left {u v : Word T} (h : u ⭢[R] v) (w : Word T) : w ++ u ⭢[R] w ++ v := by
  obtain ⟨h, p, q⟩ := h
  simpa using Step.rule h (w ++ p) q

/-- A step stays a step with a word added on the right. -/
theorem Step.append_right {u v : Word T} (h : u ⭢[R] v) (w : Word T) : u ++ w ⭢[R] v ++ w := by
  obtain ⟨h, p, q⟩ := h
  simpa using Step.rule h p (q ++ w)

/-- Derivations of two words concatenate to a derivation of their concatenation. -/
theorem Derives.append {u v u' v' : Word T} (h : u ↠[R] v) (h' : u' ↠[R] v') :
    u ++ u' ↠[R] v ++ v' := by
  have h₁ : u ++ u' ↠[R] v ++ u' := by
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail (hs.append_right u')
  have h₂ : v ++ u' ↠[R] v ++ v' := by
    induction h' with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail (hs.append_left v)
  exact h₁.trans h₂

/-- The left side of a rule derives its right side. -/
theorem Derives.rule {ρ : Rule T} (h : ρ ∈ R) : ρ.lhs ↠[R] ρ.rhs :=
  .single (by simpa using Step.rule h [] [])

/-- A derivation stays a derivation in a system with more rules. -/
theorem derives_mono {R' : SRS T} (h : ∀ ρ ∈ R, ρ ∈ R') {u v : Word T} (hd : u ↠[R] v) :
    u ↠[R'] v := by
  induction hd with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨hρ, p, q⟩ := hs
    exact ih.tail (.rule (h _ hρ) p q)

/-- **Derivability depends only on the set of rules.** -/
theorem derives_congr {R' : SRS T} (h : ∀ ρ, ρ ∈ R ↔ ρ ∈ R') (u v : Word T) :
    u ↠[R] v ↔ u ↠[R'] v :=
  ⟨derives_mono fun ρ => (h ρ).1, derives_mono fun ρ => (h ρ).2⟩

/-- **A fresh start symbol.** If `S` occurs in no rule of `R`, and every left side of `R` is
non-empty, then `[S]` rewrites under `[S] ⟶ rhs` and `R` to a word without `S` iff `rhs` rewrites
to it under `R`. -/
theorem derives_start {S : T} (hS : ∀ ρ ∈ R, S ∉ ρ.lhs ∧ S ∉ ρ.rhs)
    (hne : ∀ ρ ∈ R, ρ.lhs ≠ []) {rhs : Word T} (hrhs : S ∉ rhs) {v : Word T} (hv : S ∉ v) :
    [S] ↠[⟨[S], rhs⟩ :: R] v ↔ rhs ↠[R] v := by
  constructor
  · intro h
    -- away from `S`, a step of the larger system is a step of `R`
    have inv : ∀ {u u'}, S ∉ u → u ⭢[⟨[S], rhs⟩ :: R] u' → u ⭢[R] u' ∧ S ∉ u' := by
      intro u u' hu hs
      obtain ⟨hρ, p, q⟩ := hs
      rcases List.mem_cons.1 hρ with rfl | hρ
      · simp at hu
      · refine ⟨.rule hρ p q, ?_⟩
        simp only [List.mem_append, not_or] at hu ⊢
        exact ⟨⟨hu.1.1, (hS _ hρ).2⟩, hu.2⟩
    have run : ∀ {u}, S ∉ u → u ↠[⟨[S], rhs⟩ :: R] v → u ↠[R] v := by
      intro u hu hd
      induction hd using Relation.ReflTransGen.head_induction_on with
      | refl => exact .refl
      | head hstep _ ih =>
        obtain ⟨hR, hc⟩ := inv hu hstep
        exact (ih hc).head hR
    rcases h.cases_head with heq | ⟨s₁, hs, hrest⟩
    · exact absurd (heq ▸ List.mem_singleton_self S) hv
    obtain ⟨ρ, hρ, p, q, h₁, rfl⟩ := step_iff.1 hs
    rcases List.mem_cons.1 hρ with rfl | hρ
    · have : p = [] ∧ q = [] := by
        have hl := congrArg List.length h₁
        simp only [List.length_append, List.length_singleton] at hl
        exact ⟨List.length_eq_zero_iff.1 (by omega), List.length_eq_zero_iff.1 (by omega)⟩
      obtain ⟨rfl, rfl⟩ := this
      exact run hrhs (by simpa using hrest)
    · exfalso
      have hl := congrArg List.length h₁
      simp only [List.length_append, List.length_singleton] at hl
      have hp : p = [] := List.length_eq_zero_iff.1 (by
        have := List.length_pos_of_ne_nil (hne ρ hρ); omega)
      have hq : q = [] := List.length_eq_zero_iff.1 (by
        have := List.length_pos_of_ne_nil (hne ρ hρ); omega)
      subst hp hq
      simp only [List.nil_append, List.append_nil] at h₁
      exact (hS ρ hρ).1 (h₁ ▸ List.mem_singleton_self S)
  · intro h
    exact (derives_mono (fun ρ hρ => List.mem_cons_of_mem _ hρ) h).head
      (by simpa using Step.rule (R := ⟨[S], rhs⟩ :: R) List.mem_cons_self [] [])

/-- Renaming the letters of the rules by `f`. -/
def mapRules {T' : Type} (f : T → T') (R : SRS T) : SRS T' :=
  R.map fun ρ => ⟨ρ.lhs.map f, ρ.rhs.map f⟩

end SRS

end DiagonaLean.Foundations.Rewriting
