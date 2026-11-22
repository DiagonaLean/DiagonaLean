/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Codes.Basic
import Mathlib.Data.Set.Function

@[expose] public section

/-! # Changing the alphabet of a correspondence problem

PCP and MPCP ask for a sequence `A` of pairs of words, drawn from an instance `P` and following a
start pair `s` (empty for PCP, the start tile for MPCP), whose top and bottom concatenations agree:
`IsCorr P s A`. They are stated here on pairs of words, so that `PCP/` and `MPCP/` instantiate them
with their tiles.

Encoding every word by a code `c` maps correspondences to correspondences (`IsCorr.encode`).
Conversely, every correspondence of the encoded instance is the image of a correspondence
(`IsCorr.of_encode`), as soon as `encode c` is injective on the words over the letters of the
instance (`InjOnLetters`). A code is injective on all words; `PCP.AlphabetLift`'s fixed-width
code is injective only on the letters of the instance it was built for.
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

/-- The letters occurring in a list of pairs. -/
def letters (P : List (List α × List α)) : List α := P.flatMap fun t => t.1 ++ t.2

/-- `A` is drawn from `P` and, after the start pair `s`, its tops and bottoms agree. -/
def IsCorr (P : List (List α × List α)) (s : List α × List α) (A : List (List α × List α)) :
    Prop :=
  (∀ t ∈ A, t ∈ P) ∧ s.1 ++ tops A = s.2 ++ bots A

/-- `encode c` is injective on the words over the letters of `P`. -/
def InjOnLetters (c : α → List β) (P : List (List α × List α)) : Prop :=
  Set.InjOn (encode c) {w | ∀ a ∈ w, a ∈ letters P}

theorem IsCode.injOnLetters {c : α → List β} (hc : IsCode c) (P : List (List α × List α)) :
    InjOnLetters c P :=
  hc.injOn

theorem encode_flatten (c : α → List β) (L : List (List α)) :
    encode c L.flatten = (L.map (encode c)).flatten := by
  induction L <;> simp_all

@[simp] theorem tops_map_encodePair (c : α → List β) (A : List (List α × List α)) :
    tops (A.map (encodePair c)) = encode c (tops A) := by
  simp [tops, encode_flatten, encodePair, Function.comp_def]

@[simp] theorem bots_map_encodePair (c : α → List β) (A : List (List α × List α)) :
    bots (A.map (encodePair c)) = encode c (bots A) := by
  simp [bots, encode_flatten, encodePair, Function.comp_def]

/-- The letters of the tops of a sequence drawn from `P` are letters of `P`. -/
theorem mem_letters_of_mem_tops {P A : List (List α × List α)} (hA : ∀ t ∈ A, t ∈ P) {a : α}
    (ha : a ∈ tops A) : a ∈ letters P := by
  obtain ⟨l, hl, hal⟩ := List.mem_flatten.1 ha
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl
  exact List.mem_flatMap.2 ⟨t, hA t ht, List.mem_append_left _ hal⟩

/-- The letters of the bottoms of a sequence drawn from `P` are letters of `P`. -/
theorem mem_letters_of_mem_bots {P A : List (List α × List α)} (hA : ∀ t ∈ A, t ∈ P) {a : α}
    (ha : a ∈ bots A) : a ∈ letters P := by
  obtain ⟨l, hl, hal⟩ := List.mem_flatten.1 ha
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl
  exact List.mem_flatMap.2 ⟨t, hA t ht, List.mem_append_right _ hal⟩

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

/-- Every correspondence of the encoded instance is the image of a correspondence, when the code
is injective on the words over the letters of the instance and its start pair. -/
theorem IsCorr.of_encode {c : α → List β} {P : List (List α × List α)} {s : List α × List α}
    (hc : InjOnLetters c (s :: P)) {B : List (List β × List β)}
    (h : IsCorr (P.map (encodePair c)) (encodePair c s) B) :
    ∃ A : List (List α × List α), B = A.map (encodePair c) ∧ IsCorr P s A := by
  obtain ⟨A, hA, rfl⟩ := exists_map_eq_of_forall_mem_map h.1
  have hA' : ∀ t ∈ A, t ∈ s :: P := fun t ht => List.mem_cons_of_mem _ (hA t ht)
  have hs : ∀ t ∈ [s], t ∈ s :: P := by simp
  refine ⟨A, rfl, hA, hc ?_ ?_ ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact mem_letters_of_mem_tops hs (by simpa [tops] using ha)
    · exact mem_letters_of_mem_tops hA' ha
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact mem_letters_of_mem_bots hs (by simpa [bots] using ha)
    · exact mem_letters_of_mem_bots hA' ha
  · have := h.2
    simp only [tops_map_encodePair, bots_map_encodePair, encodePair, ← encode_append] at this
    exact this

end DiagonaLean.Foundations.Codes
