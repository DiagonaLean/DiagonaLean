/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Codes.Basic

@[expose] public section

/-! # Changing the alphabet of a correspondence problem

PCP and MPCP ask for a sequence `A` of pairs of words, drawn from an instance `P` and following a
start pair `s` (empty for PCP, the start tile for MPCP), whose top and bottom concatenations agree:
`IsCorr P s A`. They are stated here on pairs of words, so that `PCP/` and `MPCP/` instantiate them
with their tiles.

Encoding every word by a letterwise code `c` maps correspondences to correspondences
(`IsCorr.encode`). Conversely, when `c` is a code, every correspondence of the encoded instance is
the image of a correspondence (`IsCorr.of_encode`). A code that is injective only on the letters
of one instance, such as the `localCode` of `PCP.AlphabetLift`, is handled by
`Foundations.Codes.CodeFunctor.natural_on`, which moves the instance to the subtype of its letters.
-/

namespace DiagonaLean.Foundations.Codes

variable {α β : Type}

/-- Encoding both words of a pair. -/
def encodePair (c : α → List β) (t : List α × List α) : List β × List β :=
  (encode c t.1, encode c t.2)

/-- The concatenation of the top words of a sequence of pairs. -/
def tops (A : List (List α × List α)) : List α := (A.map Prod.fst).flatten

/-- The concatenation of the bottom words of a sequence of pairs. -/
def bots (A : List (List α × List α)) : List α := (A.map Prod.snd).flatten

/-- `A` is drawn from `P` and, after the start pair `s`, its tops and bottoms agree. -/
def IsCorr (P : List (List α × List α)) (s : List α × List α) (A : List (List α × List α)) :
    Prop :=
  (∀ t ∈ A, t ∈ P) ∧ s.1 ++ tops A = s.2 ++ bots A

/-- Encoding a concatenation of words is concatenating their encodings. -/
theorem encode_flatten (c : α → List β) (L : List (List α)) :
    encode c L.flatten = (L.map (encode c)).flatten := by
  induction L <;> simp_all

/-- The tops of an encoded sequence are the encoding of its tops. -/
@[simp] theorem tops_map_encodePair (c : α → List β) (A : List (List α × List α)) :
    tops (A.map (encodePair c)) = encode c (tops A) := by
  simp [tops, encode_flatten, encodePair, Function.comp_def]

/-- The bottoms of an encoded sequence are the encoding of its bottoms. -/
@[simp] theorem bots_map_encodePair (c : α → List β) (A : List (List α × List α)) :
    bots (A.map (encodePair c)) = encode c (bots A) := by
  simp [bots, encode_flatten, encodePair, Function.comp_def]

/-- Encoding maps correspondences to correspondences. -/
theorem IsCorr.encode {c : α → List β} {P A : List (List α × List α)} {s : List α × List α}
    (h : IsCorr P s A) : IsCorr (P.map (encodePair c)) (encodePair c s) (A.map (encodePair c)) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨t, ht', rfl⟩ := List.mem_map.1 ht
    exact List.mem_map_of_mem (h.1 t ht')
  · simp only [tops_map_encodePair, bots_map_encodePair, encodePair, ← encode_append, h.2]

/-- A sequence drawn from the image of `P` is the image of a sequence drawn from `P`. -/
theorem exists_map_eq_of_forall_mem_map {X Y : Type} {f : X → Y} {P : List X} {B : List Y}
    (h : ∀ y ∈ B, y ∈ P.map f) : ∃ A : List X, (∀ x ∈ A, x ∈ P) ∧ B = A.map f := by
  induction B with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons y B ih =>
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (h y (by simp))
    obtain ⟨A, hA, rfl⟩ := ih fun y hy => h y (by simp [hy])
    exact ⟨x :: A, by simp_all, rfl⟩

/-- If `c` is a code, every correspondence of the encoded instance is the image of a
correspondence. -/
theorem IsCorr.of_encode {c : α → List β} (hc : IsCode c) {P : List (List α × List α)}
    {s : List α × List α} {B : List (List β × List β)}
    (h : IsCorr (P.map (encodePair c)) (encodePair c s) B) :
    ∃ A : List (List α × List α), B = A.map (encodePair c) ∧ IsCorr P s A := by
  obtain ⟨A, hA, rfl⟩ := exists_map_eq_of_forall_mem_map h.1
  refine ⟨A, rfl, hA, hc ?_⟩
  have := h.2
  simp only [tops_map_encodePair, bots_map_encodePair, encodePair, ← encode_append] at this
  exact this

end DiagonaLean.Foundations.Codes
