/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga
-/

import Mathlib.Order.SuccPred.Nat
import DiagonaLean.PCP.Basic
import DiagonaLean.Synthetic.Definitions
import DiagonaLean.Foundations.Codes.Correspondence

@[expose] public section

/-! # Transporting PCP across alphabets

A PCP instance is a list of pairs of words, so `Foundations.Codes.Correspondence` applies:
encoding every tile by a code `c` (`Stack.encode`) preserves and reflects solvability, as soon as
`encode c` is injective on the words over the letters of the instance
(`decisionProblem_encode_iff`).

`AlphabetLift` builds such a code into any alphabet `γ₂` with at least two distinct elements, for
any alphabet with decidable equality, countable or not: each symbol of the instance is encoded by a
fixed-width binary word over `γ₂`, through its position among the symbols of the instance
(`decisionProblem_lifts`). `pcpAlphabetLift` packages this as a many-one reduction; the concrete
data (`liftInstance`, `symbolBits`) is exported so downstream reductions can build the encoded
instance and transport equivalences back and forth.
-/

namespace DiagonaLean.PCP

open Foundations.Codes

variable {α β : Type}

/-- A tile as a pair of words. -/
def Tile.toPair (t : Tile α) : List α × List α := (t.top, t.bot)

theorem Tile.toPair_injective : Function.Injective (Tile.toPair (α := α)) := by
  rintro ⟨_, _⟩ ⟨_, _⟩ h
  simpa [Tile.toPair] using h

/-- Encoding both words of a tile. -/
def Tile.encode (c : α → List β) (t : Tile α) : Tile β :=
  ⟨Foundations.Codes.encode c t.top, Foundations.Codes.encode c t.bot⟩

theorem Tile.toPair_encode (c : α → List β) (t : Tile α) :
    (t.encode c).toPair = encodePair c t.toPair := rfl

/-- Encoding every tile of an instance. -/
def Stack.encode (c : α → List β) (P : Stack α) : Stack β := P.map (Tile.encode c)

@[simp] theorem Tile.encode_unit (t : Tile α) : t.encode unit = t := by
  cases t; simp [Tile.encode]

theorem Tile.encode_kcomp {γ : Type} (c₁ : α → List β) (c₂ : β → List γ) (t : Tile α) :
    (t.encode c₁).encode c₂ = t.encode (kcomp c₂ c₁) := by
  simp only [Tile.encode, Foundations.Codes.encode_kcomp]

@[simp] theorem Stack.encode_unit (P : Stack α) : P.encode unit = P := by
  have : Tile.encode (unit (α := α)) = id := funext Tile.encode_unit
  simp [Stack.encode, this]

theorem Stack.encode_kcomp {γ : Type} (c₁ : α → List β) (c₂ : β → List γ) (P : Stack α) :
    (P.encode c₁).encode c₂ = P.encode (kcomp c₂ c₁) := by
  simp only [Stack.encode, List.map_map]
  exact List.map_congr_left fun t _ => Tile.encode_kcomp c₁ c₂ t

theorem τ1_eq_tops (A : Stack α) : τ1 A = tops (A.map Tile.toPair) := by
  simp [τ1, tops, Function.comp_def, Tile.toPair]

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

/-- **Changing the alphabet of PCP.** Encoding the tiles preserves and reflects solvability when
`encode c` is injective on the words over the letters of the instance. -/
theorem decisionProblem_encode_iff {c : α → List β} {P : Stack α}
    (hc : InjOnLetters c (([], []) :: P.map Tile.toPair)) :
    DecisionProblem (P.encode c) ↔ DecisionProblem P := by
  have e : (P.encode c).map Tile.toPair = (P.map Tile.toPair).map (encodePair c) := by
    simp [Stack.encode, Tile.toPair_encode]
  rw [decisionProblem_iff_isCorr, decisionProblem_iff_isCorr, e]
  constructor
  · rintro ⟨B, hne, h⟩
    obtain ⟨A, rfl, hA⟩ := IsCorr.of_encode hc h
    exact ⟨A, by simpa using hne, hA⟩
  · rintro ⟨A, hne, h⟩
    exact ⟨_, by simpa using hne, h.encode⟩

/-- PCP solvability is preserved and reflected by a code. -/
theorem decisionProblem_encode_iff_of_isCode {c : α → List β} (hc : IsCode c) (P : Stack α) :
    DecisionProblem (P.encode c) ↔ DecisionProblem P :=
  decisionProblem_encode_iff (hc.injOnLetters _)

end DiagonaLean.PCP

namespace DiagonaLean.PCP.AlphabetLift

variable {γ₁ γ₂ : Type} [DecidableEq γ₁]

/-- Returns a deduplicated list of all symbols appearing in a PCP stack. -/
def symbolsUsed (P : DiagonaLean.PCP.Stack γ₁) : List γ₁ :=
  (P.flatMap (fun t => t.top ++ t.bot)).dedup

/-- Fixed-width little-endian bits of `n`, padded/truncated to `len`. -/
def natToBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | len + 1, n => decide (n % 2 = 1) :: natToBits len (n / 2)

/-- Width sufficient to distinguish `n` elements. -/
def widthFor (n : ℕ) : ℕ := Nat.log2 n + 1

/-- A symbol's fixed-width bit-encoding, via its position in `symbolsUsed P`. -/
def symbolBits (P : DiagonaLean.PCP.Stack γ₁) (a : γ₁) : List Bool :=
  natToBits (widthFor (symbolsUsed P).length) ((symbolsUsed P).idxOf a)

variable (b0 b1 : γ₂)

/-- Lifts one bit to a distinguished target symbol. -/
def bitTo (b : Bool) : γ₂ := if b then b1 else b0

/-- A symbol's fixed-width word over `γ₂`. -/
def symbolWord (P :  DiagonaLean.PCP.Stack γ₁) (a : γ₁) : List γ₂ :=
  (symbolBits P a).map (bitTo b0 b1)

/-- Lifts a word over `γ₁` to a word over `γ₂`, symbol by symbol. -/
def liftWord (P :  DiagonaLean.PCP.Stack γ₁) (w : List γ₁) : List γ₂ :=
  w.flatMap (symbolWord b0 b1 P)

/-- Lifts a single tile. -/
def liftTile (P : DiagonaLean.PCP.Stack γ₁) (t : DiagonaLean.PCP.Tile γ₁) :
    DiagonaLean.PCP.Tile γ₂ :=
  ⟨liftWord b0 b1 P t.top, liftWord b0 b1 P t.bot⟩

/-- Lifts a whole PCP instance. -/
def liftInstance (P : DiagonaLean.PCP.Stack γ₁) : DiagonaLean.PCP.Stack γ₂ :=
  P.map (liftTile b0 b1 P)

/-- `liftWord` is a homomorphism with respect to concatenation, by
    `List.flatMap_append`. -/
theorem liftWord_append (P : DiagonaLean.PCP.Stack γ₁) (u v : List γ₁) :
    liftWord b0 b1 P (u ++ v) = liftWord b0 b1 P u ++ liftWord b0 b1 P v := by
  simp [liftWord, List.flatMap_append]

/-- If the tile projections `proj` and `proj'` commute with lifting, then so do their `foldr`
concatenations over a stack. -/
theorem tau_lift (proj : DiagonaLean.PCP.Tile γ₁ → List γ₁)
    (proj' : DiagonaLean.PCP.Tile γ₂ → List γ₂)
    (hproj : ∀ P t, proj' (liftTile b0 b1 P t) = liftWord b0 b1 P (proj t))
    (P : DiagonaLean.PCP.Stack γ₁) (A : DiagonaLean.PCP.Stack γ₁) :
    (A.map (liftTile b0 b1 P)).foldr (fun t acc => proj' t ++ acc) [] =
      liftWord b0 b1 P (A.foldr (fun t acc => proj t ++ acc) []) := by
  induction A with
  | nil => simp [liftWord]
  | cons t A ih => simp [liftWord_append, hproj, ih]

/-- Every `natToBits len n` has length `len`. -/
theorem natToBits_length (len n : ℕ) : (natToBits len n).length = len := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih => simp [natToBits, ih]

/-- The length of a symbol's encoded word equals the calculated fixed width. -/
theorem symbolWord_length (P : DiagonaLean.PCP.Stack γ₁) (a : γ₁) :
    (symbolWord b0 b1 P a).length = widthFor (symbolsUsed P).length := by
  simp [symbolWord, symbolBits, natToBits_length]


/-- `bitTo b0 b1` is injective whenever `b0 ≠ b1`: two bits map to the same
    target symbol only if they are the same bit. -/
theorem bitTo_injective (hne : b0 ≠ b1) : Function.Injective (bitTo b0 b1) := by
  intro x y h
  cases x <;> cases y <;> simp only [bitTo] at h
  · rfl
  · exact absurd h hne
  · exact absurd h.symm hne
  · rfl

/-- `natToBits len` is injective on naturals below `2^len`: fixed-width binary
    decoding, by induction on the width, peeling one bit at a time. -/
theorem natToBits_injective (len : ℕ) {m n : ℕ} (hm : m < 2 ^ len) (hn : n < 2 ^ len) :
    natToBits len m = natToBits len n → m = n := by
  induction len generalizing m n with
  | zero =>
    intro _
    simp only [pow_zero, Nat.lt_one_iff] at hm hn
    omega
  | succ len ih =>
    intro h
    simp only [natToBits] at h
    injection h with hbit hrest
    have hm2 : m / 2 < 2 ^ len := by
      have h2 : m < 2 * 2 ^ len := by
        have := hm; simp only [pow_succ] at this; omega
      omega
    have hn2 : n / 2 < 2 ^ len := by
      have h2 : n < 2 * 2 ^ len := by
        have := hn; simp only [pow_succ] at this; omega
      omega
    have hdiv : m / 2 = n / 2 := ih hm2 hn2 hrest
    have hmod : m % 2 = n % 2 := by
      have hiff : m % 2 = 1 ↔ n % 2 = 1 := by simpa using hbit
      omega
    omega

/-- `widthFor n` is a covering width: any `n` fits in `widthFor n` bits. -/
theorem widthFor_covers (n : ℕ) : n < 2 ^ widthFor n := by
  unfold widthFor
  exact Nat.lt_log2_self

/-- The index of an element in a list is strictly less than the list's length. -/
theorem idxOf_lt_length_of_mem {a : γ₁} {l : List γ₁} (h : a ∈ l) :
    l.idxOf a < l.length := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hb : b = a
    · simp [hb]
    · have h' : a ∈ l := (List.mem_cons.mp h).resolve_left (Ne.symm hb)
      simp only [List.idxOf_cons, List.length_cons]
      refine lt_add_of_le_of_pos ?_ ?_
      simp [hb]
      simp_all
      simp

/-- Strict inequalities between powers of two imply specific bounds on their exponents. -/
theorem pow_two_lt (n m : ℕ) (h1: 2^n < 2^m) (h2: 2^m < 2^(n+1)) : False := by
  by_cases h: m < n
  have two_pow: 2^m < 2^n := by
    refine (Nat.pow_lt_pow_iff_right (by simp)).mpr h
  · grind
  · simp at h
    by_cases h_m: m = n
    · grind
    · have two_ineq: n  + 1 < m := by
       grind
      have two_pow_le: 2^(n + 1) < 2^m := by
        refine (Nat.pow_lt_pow_iff_right (by simp)).mpr two_ineq
      grind

/-- The base-2 logarithm is monotonic for positive natural numbers. -/
theorem log2_le_log2_of_lt_pos (m n : ℕ) (h : m < n) (h_neq_zero : m ≠ 0) : m.log2 ≤ n.log2 := by
  by_contra hcon
  have hn_ne : n ≠ 0 := by omega
  -- lower bound: 2 ^ m.log2 ≤ m, the contrapositive of `Nat.log2_lt` at k := m.log2
  have ha : (2 ^ (m.log2)) ≤ m ∧ m < (2 ^ (m.log2 + 1)) := by
    simp [(Nat.log2_eq_iff h_neq_zero).mp rfl]
  have hb : (2 ^ (n.log2)) ≤ n ∧ n < (2 ^ (n.log2 + 1)) := by
    simp [(Nat.log2_eq_iff hn_ne).mp rfl]
  have hc: (2 ^ (m.log2)) < (2 ^ (n.log2 + 1)) := by
   calc
     (2 ^ (m.log2)) ≤ m := by simp [ha]
     _ < n := h
     _ < (2 ^ (n.log2 + 1)) := by simp [hb]
  simp only [not_le] at hcon
  apply pow_two_lt n.log2 m.log2
  apply (Nat.pow_lt_pow_iff_right (by simp)).mpr hcon
  exact hc

/-- Distinct symbols from the PCP stack map to distinct fixed-width encoded words. -/
theorem symbolWord_injective (P : DiagonaLean.PCP.Stack γ₁) (hne : b0 ≠ b1)
    {a a' : γ₁} (ha : a ∈ symbolsUsed P) (ha' : a' ∈ symbolsUsed P) :
    symbolWord b0 b1 P a = symbolWord b0 b1 P a' → a = a' := by
  intro h
  have hbits : symbolBits P a = symbolBits P a' :=
    List.map_injective_iff.mpr (bitTo_injective b0 b1 hne) h
  have hNodup : (symbolsUsed P).Nodup := List.nodup_dedup _
  have hidxlt : (symbolsUsed P).idxOf a < 2 ^ widthFor (symbolsUsed P).length := by
    by_cases h : List.idxOf a (symbolsUsed P) = 0
    · rw [h]
      grind
    · refine (Nat.log2_lt ?_).mp ?_
      simp [h]
      calc
        (List.idxOf a (symbolsUsed P)).log2 ≤ (symbolsUsed P).length.log2 := by
          apply log2_le_log2_of_lt_pos
          exact (idxOf_lt_length_of_mem ha)
          exact h
        _ < widthFor (symbolsUsed P).length :=  by
          exact Nat.lt_add_one (symbolsUsed P).length.log2
  have hidxlt' : (symbolsUsed P).idxOf a' < 2 ^ widthFor (symbolsUsed P).length := by
    by_cases h : List.idxOf a' (symbolsUsed P) = 0
    · rw [h]
      grind
    · refine (Nat.log2_lt ?_).mp ?_
      simp [h]
      calc
        (List.idxOf a' (symbolsUsed P)).log2 ≤ (symbolsUsed P).length.log2 := by
          apply log2_le_log2_of_lt_pos
          exact (idxOf_lt_length_of_mem ha')
          exact h
        _ < widthFor (symbolsUsed P).length :=  Nat.lt_add_one (symbolsUsed P).length.log2
  have hidx : (symbolsUsed P).idxOf a = (symbolsUsed P).idxOf a' :=
    natToBits_injective _ hidxlt hidxlt' hbits
  have hga : (symbolsUsed P).get ⟨(symbolsUsed P).idxOf a, List.idxOf_lt_length_of_mem ha⟩ = a := by
    exact List.idxOf_get (List.idxOf_lt_length_of_mem ha)
  have hga' :
      (symbolsUsed P).get ⟨(symbolsUsed P).idxOf a', List.idxOf_lt_length_of_mem ha'⟩ = a' := by
    exact List.idxOf_get (List.idxOf_lt_length_of_mem ha')
  rw [← hga, ← hga']
  simp [hidx]

/-- `liftWord` is injective on words built from the original PCP stack's alphabet. -/
theorem liftWord_injective (P : DiagonaLean.PCP.Stack γ₁) (hne : b0 ≠ b1)
    {u v : List γ₁} (hu : ∀ a ∈ u, a ∈ symbolsUsed P) (hv : ∀ a ∈ v, a ∈ symbolsUsed P) :
    liftWord b0 b1 P u = liftWord b0 b1 P v → u = v := by
  simp only [liftWord]
  induction u generalizing v with
  | nil =>
    intro h
    cases v with
    | nil => rfl
    | cons a' v' =>
      exfalso
      simp only [List.flatMap_nil, List.flatMap_cons] at h
      have hle : (symbolWord b0 b1 P a').length ≤
          (symbolWord b0 b1 P a' ++ List.flatMap (symbolWord b0 b1 P) v').length := by
        simp
      rw [← h] at hle
      simp only [List.length_nil] at hle
      have hw : (symbolWord b0 b1 P a').length = widthFor (symbolsUsed P).length :=
        symbolWord_length b0 b1 P a'
      have hwpos : 1 ≤ widthFor (symbolsUsed P).length := by simp [widthFor]
      omega
  | cons a u' ih =>
     intro h
     cases v with
      | nil =>
        exfalso
        simp only [List.flatMap_cons, List.flatMap_nil] at h
        have hle : (symbolWord b0 b1 P a).length ≤
          (symbolWord b0 b1 P a ++ List.flatMap (symbolWord b0 b1 P) u').length := by
         simp
        rw [h] at hle
        simp only [List.length_nil] at hle
        have hw : (symbolWord b0 b1 P a).length = widthFor (symbolsUsed P).length :=
          symbolWord_length b0 b1 P a
        have hwpos : 1 ≤ widthFor (symbolsUsed P).length := by simp [widthFor]
        omega
      | cons a' v' =>
        have hlen : (symbolWord b0 b1 P a).length = (symbolWord b0 b1 P a').length := by
           rw [symbolWord_length, symbolWord_length]
        obtain ⟨hsw, hlw⟩ := List.append_inj h hlen
        have haa' : a = a' := by
          apply symbolWord_injective b0 b1 P hne
          simp [hu]
          simp [hv]
          exact hsw
        have huu' : u' = v' := by
          specialize ih (v := v')
          apply ih
          grind
          grind
          grind
        rw [haa', huu']

open DiagonaLean.PCP Foundations.Codes

/-- The lifted instance encodes every tile with the code `symbolWord`. -/
theorem liftInstance_eq_encode (P : Stack γ₁) :
    liftInstance b0 b1 P = P.encode (symbolWord b0 b1 P) := rfl

theorem mem_symbolsUsed_of_mem_letters {P : Stack γ₁} {a : γ₁}
    (h : a ∈ letters (([], []) :: P.map Tile.toPair)) : a ∈ symbolsUsed P := by
  simpa [letters, symbolsUsed, Tile.toPair] using h

/-- A PCP instance is solvable if and only if its lifted instance is solvable: `symbolWord` is
injective on the words over the symbols of the instance (`liftWord_injective`). -/
theorem decisionProblem_lifts (P : Stack γ₁) (hne : b0 ≠ b1) :
    DecisionProblem P ↔ DecisionProblem (liftInstance b0 b1 P) :=
  (decisionProblem_encode_iff fun _ hu _ hv h => liftWord_injective b0 b1 P hne
    (fun _ ha => mem_symbolsUsed_of_mem_letters (hu _ ha))
    (fun _ ha => mem_symbolsUsed_of_mem_letters (hv _ ha)) h).symm

/-- `liftInstance b0 b1` witnesses the many-one reduction from PCP over an arbitrary alphabet
to PCP over a target alphabet. -/
theorem pcp_alphabet_lift_spec (hne : b0 ≠ b1) :
    (@DiagonaLean.PCP.DecisionProblem γ₁) ⪯ₘ[liftInstance b0 b1]
      (@DiagonaLean.PCP.DecisionProblem γ₂) :=
  fun P => decisionProblem_lifts b0 b1 P hne

/-- Many-one reduction from PCP over an arbitrary alphabet to PCP over a target alphabet. -/
def pcpAlphabetLift (hne : b0 ≠ b1) :
    (@DiagonaLean.PCP.DecisionProblem γ₁) ⪯ₘ (@DiagonaLean.PCP.DecisionProblem γ₂) :=
  ⟨liftInstance b0 b1, pcp_alphabet_lift_spec b0 b1 hne⟩

end DiagonaLean.PCP.AlphabetLift
