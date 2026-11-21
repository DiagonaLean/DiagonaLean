/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Codes.Basic
import Mathlib.Logic.Encodable.Basic

@[expose] public section

/-! # A synchronizing code into two letters

`unary n = 1 0ⁿ⁺¹ 1` (with `true` for `1`). Every `1` of an encoded word begins or ends a block,
and the end of a block is followed by the beginning of the next one or by the end of the word, so
the pair `1 0` occurs exactly at the beginnings of blocks (`split_of_eq_append_tf`). Hence an
encoded non-empty word, which begins with `1 0`, can only occur aligned with the blocks, and
`unary` is synchronizing (`isSync_unary`). Any countable alphabet is encoded through its numbering
(`isSync_ofEncodable`), and into any alphabet with two distinct letters (`isSync_bitCode`).

The shorter `n ↦ 1 0ⁿ 1` is not synchronizing: `unary' 0 = 1 1` occurs across the boundary of
`1 0 1` and `1 0 1`.
-/

namespace DiagonaLean.Foundations.Codes

variable {α : Type}

open List

/-- The code word of `n`: `1 0ⁿ⁺¹ 1`. -/
def unary (n : ℕ) : List Bool := true :: (replicate (n + 1) false ++ [true])

/-- The first `1` of `0ᵐ 1 x` is at position `m`: if `0ᵐ 1 x = p 1 y`, then either the displayed
`1`s coincide, or `p` extends past the first one. -/
theorem replicate_false_append_true {m : ℕ} {x p y : List Bool}
    (h : replicate m false ++ true :: x = p ++ true :: y) :
    (p = replicate m false ∧ x = y) ∨
      ∃ r, p = replicate m false ++ true :: r ∧ x = r ++ true :: y := by
  induction m generalizing p with
  | zero =>
    rcases p with _ | ⟨b, p⟩
    · exact .inl ⟨rfl, by simpa using h⟩
    · simp only [replicate_zero, nil_append, cons_append, cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inr ⟨p, rfl, rfl⟩
  | succ m ih =>
    rcases p with _ | ⟨b, p⟩
    · simp [replicate_succ] at h
    · simp only [replicate_succ, cons_append, cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rcases ih h with ⟨rfl, rfl⟩ | ⟨r, rfl, rfl⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨r, rfl, rfl⟩

/-- Two code words that begin the same word are equal. -/
theorem unary_append_inj {a b : ℕ} {u v : List Bool} (h : unary a ++ u = unary b ++ v) :
    a = b ∧ u = v := by
  simp only [unary, cons_append, cons.injEq, true_and, append_assoc] at h
  rcases replicate_false_append_true h with ⟨hr, rfl⟩ | ⟨r, hr, -⟩
  · exact ⟨by simpa using congrArg length hr.symm, rfl⟩
  · have : true ∈ replicate (b + 1) false := by rw [hr]; simp
    simp at this

/-- An encoded word is empty or begins with `1`. -/
theorem encode_unary_eq_nil_or {w : List ℕ} :
    encode unary w = [] ∨ ∃ s, encode unary w = true :: s := by
  rcases w with _ | ⟨a, w⟩
  · exact .inl rfl
  · exact .inr ⟨_, rfl⟩

/-- Prefix property: an encoded word that begins with `encode unary l` is the encoding of a word
that begins with `l`. -/
theorem encode_unary_eq_append {w l : List ℕ} {q : List Bool}
    (h : encode unary w = encode unary l ++ q) : ∃ w', w = l ++ w' ∧ q = encode unary w' := by
  induction l generalizing w with
  | nil => exact ⟨w, rfl, h.symm⟩
  | cons a l ih =>
    rcases w with _ | ⟨b, w⟩
    · simp [unary] at h
    · simp only [encode_cons, append_assoc] at h
      obtain ⟨rfl, h'⟩ := unary_append_inj h
      obtain ⟨w', rfl, rfl⟩ := ih h'
      exact ⟨w', rfl, rfl⟩

/-- The pair `1 0` occurs in an encoded word only at the beginning of a block. -/
theorem split_of_eq_append_tf {w : List ℕ} {p s : List Bool}
    (h : encode unary w = p ++ true :: false :: s) :
    ∃ w₁ w₂, w = w₁ ++ w₂ ∧ p = encode unary w₁ := by
  induction w generalizing p with
  | nil => simp at h
  | cons a w ih =>
    rcases p with _ | ⟨b, p⟩
    · exact ⟨[], a :: w, rfl, rfl⟩
    · simp only [encode_cons, unary, cons_append, cons.injEq, append_assoc] at h
      obtain ⟨rfl, h⟩ := h
      rcases replicate_false_append_true h with ⟨-, hw⟩ | ⟨r, rfl, hw⟩
      · rcases encode_unary_eq_nil_or (w := w) with h' | ⟨s', h'⟩ <;> simp [h'] at hw
      · obtain ⟨w₁, w₂, rfl, rfl⟩ := ih hw
        exact ⟨a :: w₁, w₂, rfl, by simp [unary]⟩

/-- `unary` is a code. -/
theorem isCode_unary : IsCode unary := fun u v h => by
  obtain ⟨w', rfl, hw'⟩ := encode_unary_eq_append (h.trans (append_nil _).symm)
  rcases w' with _ | ⟨a, w'⟩
  · simp
  · simp [unary] at hw'

/-- `unary` is synchronizing. -/
theorem isSync_unary : IsSync unary where
  isCode := isCode_unary
  aligned w l p q hl h := by
    obtain ⟨a, l, rfl⟩ := exists_cons_of_ne_nil hl
    obtain ⟨w₁, w₂, rfl, rfl⟩ :=
      split_of_eq_append_tf (p := p) (s := replicate a false ++ true :: (encode unary l ++ q))
        (h.trans (by simp [unary, replicate_succ]))
    rw [encode_append, append_assoc] at h
    obtain ⟨w₃, rfl, rfl⟩ := encode_unary_eq_append (append_cancel_left h)
    exact ⟨w₁, w₃, by simp, rfl, rfl⟩

/-- Precomposing a synchronizing code with an injective renaming of letters gives a synchronizing
code. -/
theorem IsSync.comp {β γ : Type} {c : β → List γ} (hc : IsSync c) {f : α → β}
    (hf : Function.Injective f) : IsSync (c ∘ f) := by
  have e : ∀ w, encode (c ∘ f) w = encode c (w.map f) := fun w => by
    induction w <;> simp_all
  refine ⟨fun u v h => ?_, fun w l p q hl h => ?_⟩
  · rw [e, e] at h
    exact (map_injective_iff.2 hf) (hc.isCode h)
  · rw [e, e] at h
    obtain ⟨w₁, w₂, hw, rfl, rfl⟩ := hc.aligned _ _ p q (by simpa using hl) h
    obtain ⟨u₁, rest, rfl, rfl, hrest⟩ := map_eq_append_iff.1 (hw.trans (append_assoc ..))
    obtain ⟨u₂, u₃, rfl, hu₂, rfl⟩ := map_eq_append_iff.1 hrest
    obtain rfl := map_injective_iff.2 hf hu₂
    exact ⟨u₁, u₃, by simp, (e u₁).symm, (e u₃).symm⟩

/-- A synchronizing code from any countable alphabet into two letters. -/
def ofEncodable [Encodable α] (a : α) : List Bool := unary (Encodable.encode a)

theorem isSync_ofEncodable [Encodable α] : IsSync (ofEncodable (α := α)) :=
  isSync_unary.comp Encodable.encode_injective

variable {β : Type}

/-- The letter for a bit, in an alphabet with letters `b0` and `b1`. -/
def bit (b0 b1 : β) (b : Bool) : β := if b then b1 else b0

theorem bit_injective {b0 b1 : β} (hne : b0 ≠ b1) : Function.Injective (bit b0 b1) := by
  intro x y h
  cases x <;> cases y <;> simp_all [bit, eq_comm]

/-- A synchronizing code from any countable alphabet into any alphabet with two distinct letters
`b0`, `b1`: `ofEncodable`, with `b0` for `0` and `b1` for `1`. -/
def bitCode [Encodable α] (b0 b1 : β) (a : α) : List β := (ofEncodable a).map (bit b0 b1)

theorem isSync_bitCode [Encodable α] {b0 b1 : β} (hne : b0 ≠ b1) :
    IsSync (bitCode (α := α) b0 b1) :=
  isSync_ofEncodable.map (bit_injective hne)

end DiagonaLean.Foundations.Codes
