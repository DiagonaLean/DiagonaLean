/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.Foundations.Computability.RunAfterWrite

@[expose] public section

/-! # A universal interpreter for Mathlib's program codes

`exists_base` gives finite constants `B : Base` such that, for every program `c : Code` and every
`m ∈ c.eval 0`, the machine `NM B.K (tapeOf B ⟨c⟩)` outputs whether `m ≠ 0` on the empty input.

The constants are obtained classically, once. Given them, `tapeOf B` and `NM B.K` are untagged, and
`tapeOf B` is primitive recursive (`tapeOf_prim`). So the machine for a program is an ordinary
function of the program's code, even though Mathlib's compiler is `noncomputable`.

Only the forward direction is proved: nothing is said about a program that diverges.

## Main statements

* `Base`, `tapeOf`: the constants and the input tape.
* `tape_eq`, `tapeOf_prim`: the tape agrees with `exists_machine`, and is primitive recursive.
* `Base.Good`, `exists_base`: correctness of the interpreter.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing Turing Nat.Partrec

/-- The finite constants of the interpreter. -/
structure Base where
  /-- The interpreter. -/
  K : UConst
  /-- The first block of the tape. -/
  e₀ : List Bool
  /-- The block for a `0` digit. -/
  e0 : List Bool
  /-- The block for a `1` digit. -/
  e1 : List Bool

/-- One step of writing the digits of a number, least significant first. -/
def bitsStep (x : ℕ × List Bool) : ℕ × List Bool :=
  if x.1 = 0 then x else (x.1 / 2, x.2 ++ [if x.1 % 2 = 1 then true else false])

/-- The binary digits of `n`, least significant first. -/
def bitsOf (n : ℕ) : List Bool := (bitsStep^[n] (n, [])).2

/-- The tape carrying the number `n`. -/
def tapeOf (B : Base) (n : ℕ) : List Bool :=
  B.e₀ ++ (bitsOf n).reverse.flatMap fun b => if b = true then B.e1 else B.e0

/-- The digit symbol of a bit. -/
def bitG (b : Bool) : PartrecToTM2.Γ' := if b = true then .bit1 else .bit0

theorem trNat_pos (p : PosNum) : PartrecToTM2.trNat (p : ℕ) = PartrecToTM2.trPosNum p := by
  have : (((p : ℕ) : ℕ) : Num) = Num.pos p := PosNum.of_to_nat p
  rw [PartrecToTM2.trNat, this]
  rfl

theorem trNat_step {n : ℕ} (hn : n ≠ 0) : PartrecToTM2.trNat n =
    bitG (if n % 2 = 1 then true else false) :: PartrecToTM2.trNat (n / 2) := by
  obtain ⟨p, rfl⟩ : ∃ p : PosNum, n = (p : ℕ) := by
    have hc := Num.to_of_nat n
    cases hx : (n : Num) with
    | zero =>
      rw [hx] at hc
      exact absurd hc.symm hn
    | pos p =>
      rw [hx] at hc
      exact ⟨p, hc.symm⟩
  cases p with
  | one =>
    have h1 : ((PosNum.one : PosNum) : ℕ) = 1 := rfl
    have h2 := trNat_pos PosNum.one
    rw [h1] at h2 ⊢
    rw [h2]
    simp [PartrecToTM2.trNat_zero, bitG, PartrecToTM2.trPosNum]
  | bit0 q =>
    have h2 : ((q.bit0 : PosNum) : ℕ) = q + q := PosNum.cast_bit0 q
    have h3 : ((q : ℕ) + q) % 2 ≠ 1 := by omega
    have h4 : ((q : ℕ) + q) / 2 = q := by omega
    rw [h2, ← h2, trNat_pos, h2, h4, trNat_pos, ite_cond_eq_false _ _ (eq_false h3)]
    rfl
  | bit1 q =>
    have h2 : ((q.bit1 : PosNum) : ℕ) = q + q + 1 := PosNum.cast_bit1 q
    have h3 : ((q : ℕ) + q + 1) % 2 = 1 := by omega
    have h4 : ((q : ℕ) + q + 1) / 2 = q := by omega
    rw [h2, ← h2, trNat_pos, h2, h4, trNat_pos, ite_cond_eq_true _ _ (eq_true h3)]
    rfl

theorem bits_iter (f m : ℕ) (acc : List Bool) (hm : m ≤ f) :
    ((bitsStep^[f] (m, acc)).2).map bitG = acc.map bitG ++ PartrecToTM2.trNat m := by
  induction f generalizing m acc with
  | zero =>
    obtain rfl : m = 0 := by omega
    simp [PartrecToTM2.trNat_zero]
  | succ f ih =>
    rw [Function.iterate_succ_apply]
    by_cases h0 : m = 0
    · subst h0
      have : bitsStep (0, acc) = (0, acc) := by simp [bitsStep]
      rw [this]
      exact ih 0 acc (Nat.zero_le _)
    · have : bitsStep (m, acc) =
          (m / 2, acc ++ [if m % 2 = 1 then true else false]) := by simp [bitsStep, h0]
      rw [this, ih _ _ (by omega), trNat_step h0]
      simp

theorem bitsOf_map (n : ℕ) : (bitsOf n).map bitG = PartrecToTM2.trNat n := by
  simpa [bitsOf] using bits_iter n n [] le_rfl

theorem tape_eq (B : Base) (e : PartrecToTM2.Γ' → List Bool) (h0 : e .bit0 = B.e0)
    (h1 : e .bit1 = B.e1) (n : ℕ) :
    B.e₀ ++ (PartrecToTM2.trNat n).reverse.flatMap e = tapeOf B n := by
  rw [tapeOf, ← bitsOf_map, ← List.map_reverse, List.flatMap_map]
  congr 2
  funext b
  cases b <;> simp [bitG, h0, h1]

theorem bitsStep_prim : Primrec bitsStep := by
  unfold bitsStep
  prim

theorem bitsOf_prim : Primrec bitsOf :=
  prim_snd (Primrec.nat_iterate Primrec.id (prim_pair Primrec.id (Primrec.const []))
    (Primrec₂.mk (bitsStep_prim.comp Primrec.snd)))

theorem tapeOf_prim (B : Base) : Primrec (tapeOf B) := by
  unfold tapeOf
  have h := bitsOf_prim
  refine prim_append (Primrec.const _) (prim_flatMap (prim_reverse h) ?_)
  prim

/-! ### The interpreter -/

/-- The interpreter is correct. -/
def Base.Good (B : Base) : Prop :=
  ∀ (c : Code) (m : ℕ), m ∈ c.eval 0 → (NM B.K (tapeOf B (Encodable.encode c))).Outputs [] [decide (m ≠ 0)]

theorem exists_base : ∃ B : Base, B.Good := by
  have hg : Partrec fun n : ℕ => Code.eval (Denumerable.ofNat Code n) 0 :=
    Code.eval_part.comp (Computable.ofNat Code) (Computable.const 0)
  obtain ⟨W, e₀, e, hW⟩ := exists_machine _ hg
  obtain ⟨K, hK⟩ := exists_uconst W
  refine ⟨⟨K, e₀, e .bit0, e .bit1⟩, fun c m hm => ?_⟩
  have h := hW (Encodable.encode c) m (by simpa [Denumerable.ofNat_encode] using hm)
  rw [tape_eq ⟨K, e₀, e .bit0, e .bit1⟩ e rfl rfl] at h
  exact hK _ _ h

end DiagonaLean.Foundations.Computability
