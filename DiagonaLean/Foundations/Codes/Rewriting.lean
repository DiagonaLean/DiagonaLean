/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Codes.Unary
import DiagonaLean.Foundations.Grammar.Rewriting

@[expose] public section

/-! # Changing the alphabet of a string rewriting system

Encoding the rules of a string rewriting system `R` by a code `c` gives a system `R.encode c` over
the code alphabet. A step of `R` maps to a step of `R.encode c`. Conversely, when `c` is
synchronizing and every left side of `R` is non-empty, every occurrence of an encoded left side in
an encoded word is aligned with the blocks, so every step from an encoded word is the image of a
step of `R` (`step_encode_inv`). Hence derivability is preserved and reflected
(`derives_encode_iff`).

Both hypotheses are needed. With a code that is not synchronizing, an encoded left side can occur
across the boundary of two blocks; with an empty left side, the encoded right side can be inserted
inside a block.
-/

namespace DiagonaLean.Foundations.Codes

open DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Rewriting Relation

variable {α β : Type}

/-- The letters of a system: the letters of its rules as pairs of words, as for the tiles of a PCP
instance (`PCP.Stack.letters`). -/
def SRS.letters (R : SRS α) : List α := Codes.letters (R.map Rule.toPair)

/-- The system whose rules are the encoded rules of `R`. -/
def SRS.encode (c : α → List β) (R : SRS α) : SRS β :=
  R.map fun ρ => ⟨Codes.encode c ρ.lhs, Codes.encode c ρ.rhs⟩

/-- Codes that agree on the letters of a system encode it alike. -/
theorem SRS.encode_congr {c c' : α → List β} {R : SRS α} (h : ∀ a ∈ SRS.letters R, c a = c' a) :
    SRS.encode c R = SRS.encode c' R :=
  List.map_congr_left fun ρ hρ => by
    have h' : ∀ a ∈ ρ.lhs ++ ρ.rhs, c a = c' a := fun a ha =>
      h a (List.mem_flatMap.2 ⟨ρ.toPair, List.mem_map_of_mem hρ, ha⟩)
    rw [Codes.encode_congr fun a ha => h' a (List.mem_append_left _ ha),
      Codes.encode_congr fun a ha => h' a (List.mem_append_right _ ha)]

/-- The identity code encodes every system as itself. -/
@[simp] theorem SRS.encode_unit (R : SRS α) : SRS.encode unit R = R := by
  simp [SRS.encode]

/-- Encoding a system by `c₁`, then by `c₂`, is encoding it by `kcomp c₂ c₁`. -/
theorem SRS.encode_kcomp {γ : Type} (c₁ : α → List β) (c₂ : β → List γ) (R : SRS α) :
    SRS.encode c₂ (SRS.encode c₁ R) = SRS.encode (kcomp c₂ c₁) R := by
  simp only [SRS.encode, List.map_map]
  refine List.map_congr_left fun ρ _ => ?_
  simp only [Function.comp_apply, _root_.DiagonaLean.Foundations.Codes.encode_kcomp]

/-- A step of `R` maps to a step of the encoded system between the encoded words. -/
theorem step_encode {c : α → List β} {R : SRS α} {u v : Word α} (h : u ⭢[R] v) :
    encode c u ⭢[SRS.encode c R] encode c v := by
  obtain ⟨hρ, p, q⟩ := h
  exact SRS.step_iff.2 ⟨_, List.mem_map_of_mem hρ, encode c p, encode c q, by simp, by simp⟩

/-- Every step from an encoded word is the image of a step. -/
theorem step_encode_inv {c : α → List β} (hc : IsSync c) {R : SRS α}
    (hR : ∀ ρ ∈ R, ρ.lhs ≠ []) {u : Word α} {y : Word β}
    (h : encode c u ⭢[SRS.encode c R] y) : ∃ v, u ⭢[R] v ∧ y = encode c v := by
  obtain ⟨_, hρ', p, q, hu, rfl⟩ := SRS.step_iff.1 h
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hρ'
  obtain ⟨w₁, w₂, rfl, rfl, rfl⟩ := hc.aligned u ρ.lhs p q (hR ρ hρ) hu
  exact ⟨w₁ ++ ρ.rhs ++ w₂, .rule hρ w₁ w₂, by simp⟩

/-- Every word derived from an encoded word is the encoding of a word derived from it. -/
theorem derives_encode_inv {c : α → List β} (hc : IsSync c) {R : SRS α}
    (hR : ∀ ρ ∈ R, ρ.lhs ≠ []) {u : Word α} {y : Word β}
    (h : encode c u ↠[SRS.encode c R] y) : ∃ v, u ↠[R] v ∧ y = encode c v := by
  induction h with
  | refl => exact ⟨u, .refl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨v, hv, rfl⟩ := ih
    obtain ⟨v', hv', rfl⟩ := step_encode_inv hc hR hs
    exact ⟨v', hv.tail hv', rfl⟩

/-- A synchronizing code preserves and reflects derivability in a system whose left sides are
non-empty. -/
theorem derives_encode_iff {c : α → List β} (hc : IsSync c) {R : SRS α}
    (hR : ∀ ρ ∈ R, ρ.lhs ≠ []) {u v : Word α} :
    encode c u ↠[SRS.encode c R] encode c v ↔ u ↠[R] v := by
  constructor
  · intro h
    obtain ⟨v', hv', hv⟩ := derives_encode_inv hc hR h
    rwa [hc.isCode hv]
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail (step_encode hs)

/-- A code sends exactly the empty word to the empty word. -/
theorem IsCode.encode_ne_nil_iff {c : α → List β} (hc : IsCode c) {l : List α} :
    encode c l ≠ [] ↔ l ≠ [] :=
  ⟨fun h hl => h (by rw [hl]; rfl), fun h he => h (hc (he.trans (encode_nil c).symm))⟩

/-- A code keeps every left side non-empty, and only then. -/
theorem lhs_ne_encode_iff {c : α → List β} (hc : IsCode c) {R : SRS α} :
    (∀ ρ ∈ SRS.encode c R, ρ.lhs ≠ []) ↔ ∀ ρ ∈ R, ρ.lhs ≠ [] := by
  simp only [SRS.encode, List.forall_mem_map, hc.encode_ne_nil_iff]

/-- Encoding a system by `unit ∘ g` renames its letters by `g`. -/
@[simp] theorem SRS.encode_unit_comp (g : α → β) (R : SRS α) :
    SRS.encode (unit ∘ g) R = R.mapRules g := by
  simp [SRS.encode, SRS.mapRules, encode_comp]

/-- **Renaming letters injectively keeps derivability**, in a system whose left sides are
non-empty: `derives_encode_iff` for the synchronizing code `unit ∘ g`. -/
theorem derives_mapRules_iff {g : α → β} (hg : Function.Injective g) {R : SRS α}
    (hR : ∀ ρ ∈ R, ρ.lhs ≠ []) (u v : Word α) :
    u.map g ↠[R.mapRules g] v.map g ↔ u ↠[R] v := by
  simpa [encode_comp] using derives_encode_iff (isSync_unit.comp hg) hR (u := u) (v := v)

end DiagonaLean.Foundations.Codes
