/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import Mathlib.Data.List.Basic

@[expose] public section

/-! # Codes: changing the alphabet of a problem

A letterwise code `c : α → List β` extends to the monoid homomorphism `encode c = List.flatMap c`
from words over `α` to words over `β`. A problem about words can be moved to a smaller alphabet by
applying `encode c` to its instances, when the problem is preserved and reflected by `encode c`:

The codes form a category, and `encode` is a functor on it (`encode_unit`, `encode_kcomp`).

* `IsCode c`: `encode c` is injective. Problems about equality of concatenations, such as PCP and
  MPCP, are preserved and reflected (`Codes/Correspondence.lean`).
* `IsSync c`: moreover every occurrence of an encoded non-empty word inside an encoded word is
  aligned with the blocks of the code. Problems about rewriting substrings, such as the word problem
  for string rewriting systems, are preserved and reflected (`Codes/Rewriting.lean`); without
  alignment, an encoded left side could match across the boundary of two blocks.

`Codes/Unary.lean` gives a synchronizing code from any countable alphabet into two letters.
-/

namespace DiagonaLean.Foundations.Codes

variable {α β γ : Type}

/-- The homomorphism of a letterwise code: each letter is replaced by its code word. -/
def encode (c : α → List β) (w : List α) : List β := w.flatMap c

@[simp] theorem encode_nil (c : α → List β) : encode c [] = [] := rfl

@[simp] theorem encode_cons (c : α → List β) (a : α) (w : List α) :
    encode c (a :: w) = c a ++ encode c w := rfl

@[simp] theorem encode_append (c : α → List β) (u v : List α) :
    encode c (u ++ v) = encode c u ++ encode c v := by
  simp [encode]

/-! ### The category of codes

The identity of an alphabet is the code of one-letter words (`unit`), and codes compose by
substitution (`kcomp`): this is the Kleisli category of `List`. `encode` is a functor from it to
functions between words (`encode_unit`, `encode_kcomp`). -/

/-- The identity code: every letter is its own one-letter word. -/
def unit (a : α) : List α := [a]

/-- Composition of codes: substitute the code words of `c₂` into those of `c₁`. -/
def kcomp (c₂ : β → List γ) (c₁ : α → List β) (a : α) : List γ := encode c₂ (c₁ a)

@[simp] theorem encode_unit (w : List α) : encode unit w = w := by
  induction w <;> simp_all [unit]

theorem encode_kcomp (c₂ : β → List γ) (c₁ : α → List β) (w : List α) :
    encode c₂ (encode c₁ w) = encode (kcomp c₂ c₁) w := by
  induction w <;> simp_all [kcomp]

/-- `c` is a code: its homomorphism is injective. -/
def IsCode (c : α → List β) : Prop := Function.Injective (encode c)

/-- `c` is a synchronizing code: it is a code, and every occurrence of the encoding of a non-empty
word inside the encoding of a word starts and ends at block boundaries. -/
structure IsSync (c : α → List β) : Prop where
  /-- The homomorphism is injective. -/
  isCode : IsCode c
  /-- Occurrences of encoded non-empty words are aligned. -/
  aligned : ∀ (w l : List α) (p q : List β), l ≠ [] → encode c w = p ++ encode c l ++ q →
    ∃ w₁ w₂, w = w₁ ++ l ++ w₂ ∧ p = encode c w₁ ∧ q = encode c w₂

/-- Following a code by an injective renaming of letters gives a code. -/
theorem IsCode.map {c : α → List β} (hc : IsCode c) {g : β → γ} (hg : Function.Injective g) :
    IsCode fun a => (c a).map g := fun u v h => by
  have e : ∀ w, encode (fun a => (c a).map g) w = (encode c w).map g := fun w => by
    induction w <;> simp_all
  rw [e, e] at h
  exact hc (List.map_injective_iff.2 hg h)

/-- Following a synchronizing code by an injective renaming of letters gives a synchronizing
code. -/
theorem IsSync.map {c : α → List β} (hc : IsSync c) {g : β → γ} (hg : Function.Injective g) :
    IsSync fun a => (c a).map g := by
  have e : ∀ w, encode (fun a => (c a).map g) w = (encode c w).map g := fun w => by
    induction w <;> simp_all
  refine ⟨hc.isCode.map hg, fun w l p q hl h => ?_⟩
  rw [e, e, List.append_assoc] at h
  obtain ⟨p', rest, hw, rfl, hrest⟩ := List.map_eq_append_iff.1 h
  obtain ⟨m, q', rfl, hm, rfl⟩ := List.map_eq_append_iff.1 hrest
  obtain rfl := List.map_injective_iff.2 hg hm
  obtain ⟨w₁, w₂, rfl, rfl, rfl⟩ := hc.aligned w l p' q' hl (by rw [hw, List.append_assoc])
  exact ⟨w₁, w₂, rfl, (e w₁).symm, (e w₂).symm⟩

end DiagonaLean.Foundations.Codes
