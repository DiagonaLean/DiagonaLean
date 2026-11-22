/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga
-/

import DiagonaLean.PCP.Basic
import DiagonaLean.Synthetic.Definitions
import DiagonaLean.Foundations.Codes.Correspondence
import DiagonaLean.Foundations.Codes.Functor

@[expose] public section

/-! # Transporting PCP across alphabets

A PCP instance is a list of pairs of words, so `Foundations.Codes.Correspondence` applies:
encoding every tile by a code `c` (`Stack.encode`) preserves and reflects solvability
(`decisionProblem_encode_iff`). An injective renaming of letters is such a code (`pcp_map_iff`).

PCP is a functor on codes (`pcpFunctor`), with the letters of an instance as its support, so the
lift of `Foundations.Codes.Functor` (`Foundations.Codes.CodeFunctor.lift`) applies: each symbol
of the instance is encoded by the unary code of its position among the symbols of the instance,
over two distinct letters of any target alphabet. The source alphabet needs only
decidable equality, countable or not. `AlphabetLift.liftInstance` is this encoding,
`decisionProblem_lifts` its correctness and `pcpAlphabetLift` the many-one reduction; downstream
reductions use them to build the encoded instance and transport equivalences.
-/

namespace DiagonaLean.PCP

open Foundations.Codes

variable {α β : Type}

/-- A tile as a pair of words. -/
def Tile.toPair (t : Tile α) : List α × List α := (t.top, t.bot)

/-- `Tile.toPair` is injective. -/
theorem Tile.toPair_injective : Function.Injective (Tile.toPair (α := α)) := by
  rintro ⟨_, _⟩ ⟨_, _⟩ h
  simpa [Tile.toPair] using h

/-- Encoding both words of a tile. -/
def Tile.encode (c : α → List β) (t : Tile α) : Tile β :=
  ⟨Foundations.Codes.encode c t.top, Foundations.Codes.encode c t.bot⟩

/-- The pair of an encoded tile is the encoded pair of the tile. -/
theorem Tile.toPair_encode (c : α → List β) (t : Tile α) :
    (t.encode c).toPair = encodePair c t.toPair := rfl

/-- Encoding every tile of an instance. -/
def Stack.encode (c : α → List β) (P : Stack α) : Stack β := P.map (Tile.encode c)

/-- The identity code encodes every tile as itself. -/
@[simp] theorem Tile.encode_unit (t : Tile α) : t.encode unit = t := by
  cases t; simp [Tile.encode]

/-- Encoding a tile by `c₁`, then by `c₂`, is encoding it by `kcomp c₂ c₁`. -/
theorem Tile.encode_kcomp {γ : Type} (c₁ : α → List β) (c₂ : β → List γ) (t : Tile α) :
    (t.encode c₁).encode c₂ = t.encode (kcomp c₂ c₁) := by
  simp only [Tile.encode, Foundations.Codes.encode_kcomp]

/-- The identity code encodes every instance as itself. -/
@[simp] theorem Stack.encode_unit (P : Stack α) : P.encode unit = P := by
  have : Tile.encode (unit (α := α)) = id := funext Tile.encode_unit
  simp [Stack.encode, this]

/-- Encoding an instance by `c₁`, then by `c₂`, is encoding it by `kcomp c₂ c₁`. -/
theorem Stack.encode_kcomp {γ : Type} (c₁ : α → List β) (c₂ : β → List γ) (P : Stack α) :
    (P.encode c₁).encode c₂ = P.encode (kcomp c₂ c₁) := by
  simp only [Stack.encode, List.map_map]
  exact List.map_congr_left fun t _ => Tile.encode_kcomp c₁ c₂ t

/-- Renaming the letters of a tile by `g`. -/
def Tile.map (g : α → β) (t : Tile α) : Tile β := ⟨t.top.map g, t.bot.map g⟩

/-- Encoding a tile by `unit ∘ g` is renaming its letters by `g`. -/
theorem Tile.encode_unit_comp (g : α → β) : Tile.encode (unit ∘ g) = Tile.map g :=
  funext fun t => by simp [Tile.encode, Tile.map, encode_comp]

/-- The top concatenation of a stack is the concatenation of the tops of its pairs. -/
theorem τ1_eq_tops (A : Stack α) : τ1 A = tops (A.map Tile.toPair) := by
  simp [τ1, tops, Function.comp_def, Tile.toPair]

/-- The bottom concatenation of a stack is the concatenation of the bottoms of its pairs. -/
theorem τ2_eq_bots (A : Stack α) : τ2 A = bots (A.map Tile.toPair) := by
  simp [τ2, bots, Function.comp_def, Tile.toPair]

/-- The correspondences of an instance, as sequences of pairs, are the images of its stacks. -/
theorem isCorr_map_toPair_iff {P : Stack α} {s : List α × List α} {B : List (List α × List α)} :
    IsCorr (P.map Tile.toPair) s B ↔
      ∃ A : Stack α, B = A.map Tile.toPair ∧ (∀ t ∈ A, t ∈ P) ∧ s.1 ++ τ1 A = s.2 ++ τ2 A := by
  constructor
  · rintro ⟨hB, h⟩
    obtain ⟨A, hA, rfl⟩ := exists_map_eq_of_forall_mem_map hB
    exact ⟨A, rfl, hA, by rwa [τ1_eq_tops, τ2_eq_bots]⟩
  · rintro ⟨A, rfl, hA, h⟩
    refine ⟨fun t ht => ?_, by rwa [← τ1_eq_tops, ← τ2_eq_bots]⟩
    obtain ⟨t, ht', rfl⟩ := List.mem_map.1 ht
    exact List.mem_map_of_mem (hA t ht')

/-- PCP solvability as a non-empty correspondence of pairs, with empty start pair. -/
theorem decisionProblem_iff_isCorr (P : Stack α) :
    DecisionProblem P ↔ ∃ B, B ≠ [] ∧ IsCorr (P.map Tile.toPair) ([], []) B := by
  constructor
  · rintro ⟨A, hne, hA, h⟩
    exact ⟨_, by simpa using hne, isCorr_map_toPair_iff.2 ⟨A, rfl, hA, h⟩⟩
  · rintro ⟨B, hne, h⟩
    obtain ⟨A, rfl, hA, h⟩ := isCorr_map_toPair_iff.1 h
    exact ⟨A, by simpa using hne, hA, h⟩

/-- **Changing the alphabet of PCP.** Encoding the tiles by a code preserves and reflects
solvability. -/
theorem decisionProblem_encode_iff {c : α → List β} (hc : IsCode c) (P : Stack α) :
    DecisionProblem (P.encode c) ↔ DecisionProblem P := by
  have e : (P.encode c).map Tile.toPair = (P.map Tile.toPair).map (encodePair c) := by
    simp [Stack.encode, Tile.toPair_encode]
  rw [decisionProblem_iff_isCorr, decisionProblem_iff_isCorr, e]
  constructor
  · rintro ⟨B, hne, h⟩
    obtain ⟨A, rfl, hA⟩ := IsCorr.of_encode (s := ([], [])) hc h
    exact ⟨A, by simpa using hne, hA⟩
  · rintro ⟨A, hne, h⟩
    exact ⟨_, by simpa using hne, h.encode⟩

/-- Renaming the letters of the tiles injectively preserves and reflects PCP solvability. -/
theorem pcp_map_iff (g : α → β) (hg : Function.Injective g) (P : Stack α) :
    DecisionProblem P ↔ DecisionProblem (P.map (Tile.map g)) := by
  rw [← Tile.encode_unit_comp]
  exact (decisionProblem_encode_iff (isCode_unit.comp hg) P).symm

/-- Codes that agree on the letters of a tile encode it alike. -/
theorem Tile.encode_congr {c c' : α → List β} {t : Tile α} (h : ∀ a ∈ t.top ++ t.bot, c a = c' a) :
    t.encode c = t.encode c' := by
  simp only [Tile.encode,
    Foundations.Codes.encode_congr fun a ha => h a (List.mem_append_left t.bot ha),
    Foundations.Codes.encode_congr fun a ha => h a (List.mem_append_right t.top ha)]

/-- The letters of an instance: the letters of its tiles as pairs of words. -/
def Stack.letters (P : Stack α) : List α := Foundations.Codes.letters (P.map Tile.toPair)

/-- Codes that agree on the letters of an instance encode it alike. -/
theorem Stack.encode_congr {c c' : α → List β} {P : Stack α} (h : ∀ a ∈ P.letters, c a = c' a) :
    P.encode c = P.encode c' :=
  List.map_congr_left fun t ht => Tile.encode_congr fun a ha =>
    h a (List.mem_flatMap.2 ⟨t.toPair, List.mem_map_of_mem ht, ha⟩)

/-- **PCP as a functor on codes**: a code encodes every tile, and codes preserve and reflect
solvability. -/
abbrev pcpFunctor : CodeFunctor IsCode where
  Inst α := Stack α
  map c P := P.encode c
  Prob P := DecisionProblem P
  map_unit := Stack.encode_unit
  map_kcomp := Stack.encode_kcomp
  natural hc P := decisionProblem_encode_iff hc P
  supp := Stack.letters
  map_congr _ h := Stack.encode_congr h

end DiagonaLean.PCP

namespace DiagonaLean.PCP.AlphabetLift

open DiagonaLean.PCP Foundations.Codes

variable {γ₁ γ₂ : Type} [DecidableEq γ₁] (b0 b1 : γ₂)

/-- Lifts a PCP instance to the letters `b0`, `b1`: each symbol becomes the unary code of its
position among the letters of the instance. -/
def liftInstance (P : Stack γ₁) : Stack γ₂ := P.encode (localCode b0 b1 P.letters)

/-- A PCP instance is solvable if and only if its lifted instance is solvable. -/
theorem decisionProblem_lifts (P : Stack γ₁) (hne : b0 ≠ b1) :
    DecisionProblem P ↔ DecisionProblem (liftInstance b0 b1 P) :=
  (pcpFunctor.natural_on P (good_localCode hne _)).symm

/-- `liftInstance b0 b1` witnesses the many-one reduction from PCP over an arbitrary alphabet
to PCP over a target alphabet. -/
theorem pcp_alphabet_lift_spec (hne : b0 ≠ b1) :
    (@DiagonaLean.PCP.DecisionProblem γ₁) ⪯ₘ[liftInstance b0 b1]
      (@DiagonaLean.PCP.DecisionProblem γ₂) :=
  fun P => decisionProblem_lifts b0 b1 P hne

/-- Many-one reduction from PCP over an arbitrary alphabet to PCP over a target alphabet:
`pcpFunctor.lift`. -/
def pcpAlphabetLift (hne : b0 ≠ b1) :
    (@DiagonaLean.PCP.DecisionProblem γ₁) ⪯ₘ (@DiagonaLean.PCP.DecisionProblem γ₂) :=
  pcpFunctor.lift b0 b1 hne

end DiagonaLean.PCP.AlphabetLift
