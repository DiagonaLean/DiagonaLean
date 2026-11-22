/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Codes.Basic
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

open DiagonaLean.Foundations.Grammar Relation

variable {α β : Type}

/-- The system whose rules are the encoded rules of `R`. -/
def SRS.encode (c : α → List β) (R : SRS α) : SRS β :=
  R.map fun lr => (Codes.encode c lr.1, Codes.encode c lr.2)

@[simp] theorem SRS.encode_unit (R : SRS α) : SRS.encode unit R = R := by
  simp [SRS.encode]

theorem SRS.encode_kcomp {γ : Type} (c₁ : α → List β) (c₂ : β → List γ) (R : SRS α) :
    SRS.encode c₂ (SRS.encode c₁ R) = SRS.encode (kcomp c₂ c₁) R := by
  simp only [SRS.encode, List.map_map]
  refine List.map_congr_left fun lr _ => ?_
  simp only [Function.comp_apply, _root_.DiagonaLean.Foundations.Codes.encode_kcomp]

theorem step_encode {c : α → List β} {R : SRS α} {u v : List α} (h : R.Step u v) :
    (SRS.encode c R).Step (encode c u) (encode c v) := by
  obtain ⟨lr, hlr, p, q, rfl, rfl⟩ := h
  exact ⟨_, List.mem_map_of_mem hlr, encode c p, encode c q, by simp, by simp⟩

/-- Every step from an encoded word is the image of a step. -/
theorem step_encode_inv {c : α → List β} (hc : IsSync c) {R : SRS α}
    (hR : ∀ lr ∈ R, lr.1 ≠ []) {u : List α} {y : List β}
    (h : (SRS.encode c R).Step (encode c u) y) : ∃ v, R.Step u v ∧ y = encode c v := by
  obtain ⟨_, hlr', p, q, hu, rfl⟩ := h
  obtain ⟨lr, hlr, rfl⟩ := List.mem_map.1 hlr'
  obtain ⟨w₁, w₂, rfl, rfl, rfl⟩ := hc.aligned u lr.1 p q (hR lr hlr) hu
  exact ⟨w₁ ++ lr.2 ++ w₂, ⟨lr, hlr, w₁, w₂, rfl, rfl⟩, by simp⟩

/-- Every word derived from an encoded word is the encoding of a word derived from it. -/
theorem derives_encode_inv {c : α → List β} (hc : IsSync c) {R : SRS α}
    (hR : ∀ lr ∈ R, lr.1 ≠ []) {u : List α} {y : List β}
    (h : (SRS.encode c R).Derives (encode c u) y) : ∃ v, R.Derives u v ∧ y = encode c v := by
  induction h with
  | refl => exact ⟨u, .refl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨v, hv, rfl⟩ := ih
    obtain ⟨v', hv', rfl⟩ := step_encode_inv hc hR hs
    exact ⟨v', hv.tail hv', rfl⟩

/-- A synchronizing code preserves and reflects derivability in a system whose left sides are
non-empty. -/
theorem derives_encode_iff {c : α → List β} (hc : IsSync c) {R : SRS α}
    (hR : ∀ lr ∈ R, lr.1 ≠ []) {u v : List α} :
    (SRS.encode c R).Derives (encode c u) (encode c v) ↔ R.Derives u v := by
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
    (∀ lr ∈ SRS.encode c R, lr.1 ≠ []) ↔ ∀ lr ∈ R, lr.1 ≠ [] := by
  simp only [SRS.encode, List.forall_mem_map, hc.encode_ne_nil_iff]

end DiagonaLean.Foundations.Codes
