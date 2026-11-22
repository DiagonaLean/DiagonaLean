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

* `IsCode c`: `encode c` is injective. Problems about equality of concatenations, such as PCP and
  MPCP, are preserved and reflected (`Codes/Correspondence.lean`).
* `IsSync c`: moreover every occurrence of an encoded non-empty word inside an encoded word is
  aligned with the blocks of the code. Problems about rewriting substrings, such as the word problem
  for string rewriting systems, are preserved and reflected (`Codes/Rewriting.lean`); without
  alignment, an encoded left side could match across the boundary of two blocks.

The codes form a category, and `encode` is a functor on it (`encode_unit`, `encode_kcomp`).

`Codes/Unary.lean` gives a synchronizing code from any countable alphabet into two letters.
-/

namespace DiagonaLean.Foundations.Codes

variable {α β γ : Type}

/-- The homomorphism of a letterwise code: each letter is replaced by its code word. -/
def encode (c : α → List β) (w : List α) : List β := w.flatMap c

/-- The empty word encodes to the empty word. -/
@[simp] theorem encode_nil (c : α → List β) : encode c [] = [] := rfl

/-- The encoding of `a :: w` is the code word of `a` followed by the encoding of `w`. -/
@[simp] theorem encode_cons (c : α → List β) (a : α) (w : List α) :
    encode c (a :: w) = c a ++ encode c w := rfl

/-- Encoding is a monoid homomorphism: it sends concatenation to concatenation. -/
@[simp] theorem encode_append (c : α → List β) (u v : List α) :
    encode c (u ++ v) = encode c u ++ encode c v := by
  simp [encode]

/-- Codes that agree on the letters of a word encode it alike. -/
theorem encode_congr {c c' : α → List β} {w : List α} (h : ∀ a ∈ w, c a = c' a) :
    encode c w = encode c' w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [h a (by simp), ih fun b hb => h b (by simp [hb])]

/-- Encoding by `c ∘ f` is renaming the letters by `f`, then encoding by `c`. -/
theorem encode_comp (c : β → List γ) (f : α → β) (w : List α) :
    encode (c ∘ f) w = encode c (w.map f) := by
  induction w <;> simp_all

/-- Encoding by `c` followed by the renaming `g` of every code word is encoding by `c`, then
renaming the letters by `g`. -/
theorem encode_map_letters (c : α → List β) (g : β → γ) (w : List α) :
    encode (fun a => (c a).map g) w = (encode c w).map g := by
  induction w <;> simp_all

/-- The letters occurring in a list of pairs of words. -/
def letters (P : List (List α × List α)) : List α := P.flatMap fun t => t.1 ++ t.2

/-! ### The category of codes

The identity of an alphabet is the code of one-letter words (`unit`), and codes compose by
substitution (`kcomp`): this is the Kleisli category of `List`. `encode` is a functor from it to
functions between words (`encode_unit`, `encode_kcomp`). -/

/-- The identity code: every letter is its own one-letter word. -/
def unit (a : α) : List α := [a]

/-- Composition of codes: substitute the code words of `c₂` into those of `c₁`. -/
def kcomp (c₂ : β → List γ) (c₁ : α → List β) (a : α) : List γ := encode c₂ (c₁ a)

/-- The identity code encodes every word as itself. -/
@[simp] theorem encode_unit (w : List α) : encode unit w = w := by
  induction w <;> simp_all [unit]

/-- Encoding by `c₁`, then by `c₂`, is encoding by the composite code `kcomp c₂ c₁`. -/
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

/-- The identity code is a code. -/
theorem isCode_unit : IsCode (unit (α := α)) := fun u v h => by simpa using h

/-- Precomposing a code with an injective renaming of letters gives a code. -/
theorem IsCode.comp {c : β → List γ} (hc : IsCode c) {f : α → β} (hf : Function.Injective f) :
    IsCode (c ∘ f) := fun u v h => by
  rw [encode_comp, encode_comp] at h
  exact List.map_injective_iff.2 hf (hc h)

/-- Following a code by an injective renaming of letters gives a code. -/
theorem IsCode.map {c : α → List β} (hc : IsCode c) {g : β → γ} (hg : Function.Injective g) :
    IsCode fun a => (c a).map g := fun u v h => by
  rw [encode_map_letters, encode_map_letters] at h
  exact hc (List.map_injective_iff.2 hg h)

/-- Following a synchronizing code by an injective renaming of letters gives a synchronizing
code. -/
theorem IsSync.map {c : α → List β} (hc : IsSync c) {g : β → γ} (hg : Function.Injective g) :
    IsSync fun a => (c a).map g := by
  refine ⟨hc.isCode.map hg, fun w l p q hl h => ?_⟩
  rw [encode_map_letters, encode_map_letters, List.append_assoc] at h
  obtain ⟨p', rest, hw, rfl, hrest⟩ := List.map_eq_append_iff.1 h
  obtain ⟨m, q', rfl, hm, rfl⟩ := List.map_eq_append_iff.1 hrest
  obtain rfl := List.map_injective_iff.2 hg hm
  obtain ⟨w₁, w₂, rfl, rfl, rfl⟩ := hc.aligned w l p' q' hl (by rw [hw, List.append_assoc])
  exact ⟨w₁, w₂, rfl, (encode_map_letters c g w₁).symm, (encode_map_letters c g w₂).symm⟩

/-- Precomposing a synchronizing code with an injective renaming of letters gives a synchronizing
code. -/
theorem IsSync.comp {c : β → List γ} (hc : IsSync c) {f : α → β} (hf : Function.Injective f) :
    IsSync (c ∘ f) := by
  refine ⟨hc.isCode.comp hf, fun w l p q hl h => ?_⟩
  rw [encode_comp, encode_comp] at h
  obtain ⟨w₁, w₂, hw, rfl, rfl⟩ := hc.aligned _ _ p q (by simpa using hl) h
  obtain ⟨u₁, rest, rfl, rfl, hrest⟩ := List.map_eq_append_iff.1 (hw.trans (List.append_assoc ..))
  obtain ⟨u₂, u₃, rfl, hu₂, rfl⟩ := List.map_eq_append_iff.1 hrest
  obtain rfl := List.map_injective_iff.2 hf hu₂
  exact ⟨u₁, u₃, by simp, (encode_comp c f u₁).symm, (encode_comp c f u₃).symm⟩

end DiagonaLean.Foundations.Codes
