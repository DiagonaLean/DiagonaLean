/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Free
import DiagonaLean.KleeneAlgebra.SetStar
import Mathlib.Algebra.FreeMonoid.Basic

@[expose] public section

/-! # The doubled alphabet `Σ̈` and its language model

The completeness argument only uses `T Σ̈`, where `Σ̈ = Σ ⊕ Σ` has left copies `x_l = inl x` and
right copies `x_r = inr x`, with every left symbol commuting with every right symbol (Def 12 with
`Σ` discrete). Strings over `Σ̈` modulo this commutation are exactly pairs of words, so we take
`W A = FreeMonoid A × FreeMonoid A` as the string monoid `S Σ̈`. The left and right projections
`π_l`, `π_r` are `Prod.fst` and `Prod.snd`.

## Main definitions

* `DComm`: the commuting relation on `A ⊕ A` (left commutes with right).
* `TD A`: the free pre-Kleene algebra `T Σ̈`.
* `W A`: strings over `Σ̈`, i.e. pairs of words.
* `TD.ofPair s`: the string `s = (u, v)` as the term `u_l v_r`.
* `TD.pl`: the language interpretation `l : T Σ̈ → P(W A)`.

## Main statements

* `TD.ofPair_mul`: `ofPair` is multiplicative; this is where commutation is used.
* `TD.ofPair_le_iff_mem` (Theorem 5): `s ≤ e ↔ s ∈ l(e)`.
* `TD.eq_zero_of_pl_eq_zero`, `TD.exists_ofPair_le` (Corollary 8, proved directly, since the
  paper's proof goes through the false Corollary 7).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Def 12, Thm 5, Cor 8
-/

open scoped Computability

namespace DiagonaLean.KAComm

variable {A : Type*}

/-- Left symbols commute with right symbols. -/
def DComm : A ⊕ A → A ⊕ A → Prop
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | _, _ => False

/-- The free pre-Kleene algebra `T Σ̈` over the doubled alphabet. -/
abbrev TD (A : Type*) := FreePreKA (A ⊕ A) DComm

/-- Strings over `Σ̈`: pairs `(π_l s, π_r s)` of words. -/
abbrev W (A : Type*) := FreeMonoid A × FreeMonoid A

namespace TD

open FreePreKA RExp

/-- The left copy `u_l` of a word. -/
def L : FreeMonoid A →* TD A := FreeMonoid.lift fun a => of (Sum.inl a)

/-- The right copy `v_r` of a word. -/
def R : FreeMonoid A →* TD A := FreeMonoid.lift fun a => of (Sum.inr a)

@[simp] theorem L_of (a : A) : L (FreeMonoid.of a) = of (Sum.inl a) := FreeMonoid.lift_eval_of _ _
@[simp] theorem R_of (a : A) : R (FreeMonoid.of a) = of (Sum.inr a) := FreeMonoid.lift_eval_of _ _

theorem commute_R_L (u v : FreeMonoid A) : Commute (R v) (L u) := by
  induction v using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact Commute.one_left _
  | of_mul b v ih =>
    rw [map_mul, R_of]
    refine Commute.mul_left ?_ ih
    clear ih
    induction u using FreeMonoid.inductionOn' with
    | one => rw [map_one]; exact Commute.one_right _
    | of_mul a u ih' =>
      rw [map_mul, L_of]
      exact Commute.mul_right (of_comm (C := DComm) (x := Sum.inr b) (y := Sum.inl a) trivial) ih'

/-- The string `s = (u, v)` as the term `u_l v_r`. -/
def ofPair (s : W A) : TD A := L s.1 * R s.2

@[simp] theorem ofPair_one : ofPair (1 : W A) = 1 := by simp [ofPair]

/-- `ofPair` is multiplicative: `(u₁u₂)_l (v₁v₂)_r = u₁_l v₁_r u₂_l v₂_r`, using that right
symbols commute past left ones. -/
theorem ofPair_mul (s t : W A) : ofPair (s * t) = ofPair s * ofPair t := by
  simp only [ofPair, Prod.fst_mul, Prod.snd_mul, map_mul]
  rw [mul_assoc, mul_assoc, ← mul_assoc (L t.1), ← (commute_R_L t.1 s.2).eq, mul_assoc]

theorem ofPair_list_prod (l : List (W A)) : ofPair l.prod = (l.map ofPair).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.prod_cons, ofPair_mul, ih, List.map_cons, List.prod_cons]

/-! ### The language interpretation -/

/-- The singleton language `{s}`. -/
def single (s : W A) : _root_.SetSemiring (W A) := Set.up {s}

theorem mem_single (s t : W A) : SetSemiring.Mem t (single s) ↔ t = s := Iff.rfl

theorem single_mul (s t : W A) : single s * single t = single (s * t) :=
  SetSemiring.ext fun x => by
    rw [SetSemiring.mem_mul, mem_single]
    constructor
    · rintro ⟨a, rfl, b, rfl, rfl⟩; rfl
    · rintro rfl; exact ⟨s, rfl, t, rfl, rfl⟩

/-- The images of generators: `x_l ↦ {(x, ε)}`, `x_r ↦ {(ε, x)}`. -/
def gen : A ⊕ A → _root_.SetSemiring (W A)
  | .inl a => single (FreeMonoid.of a, 1)
  | .inr a => single (1, FreeMonoid.of a)

theorem gen_comm (x y : A ⊕ A) (h : DComm x y) : gen x * gen y = gen y * gen x := by
  rcases x with a | a <;> rcases y with b | b <;> simp only [DComm] at h <;>
    simp only [gen, single_mul] <;> congr 1

/-- The language interpretation `l : T Σ̈ → P(S Σ̈)`. -/
noncomputable def pl : TD A → _root_.SetSemiring (W A) := lift gen gen_comm

@[simp] theorem pl_zero : pl (0 : TD A) = 0 := rfl
@[simp] theorem pl_one : pl (1 : TD A) = 1 := rfl
@[simp] theorem pl_add (a b : TD A) : pl (a + b) = pl a + pl b := lift_add _ _ a b
@[simp] theorem pl_mul (a b : TD A) : pl (a * b) = pl a * pl b := lift_mul _ _ a b
@[simp] theorem pl_kstar (a : TD A) : pl a∗ = (pl a)∗ := lift_kstar _ _ a

theorem pl_mono {a b : TD A} (h : a ≤ b) : pl a ≤ pl b := lift_mono _ _ h

theorem pl_L (u : FreeMonoid A) : pl (L u) = single (u, 1) := by
  induction u using FreeMonoid.inductionOn' with
  | one => rw [map_one, pl_one]; rfl
  | of_mul a u ih =>
    rw [map_mul, pl_mul, ih, L_of]
    exact (single_mul _ _).trans (by simp)

theorem pl_R (v : FreeMonoid A) : pl (R v) = single (1, v) := by
  induction v using FreeMonoid.inductionOn' with
  | one => rw [map_one, pl_one]; rfl
  | of_mul a v ih =>
    rw [map_mul, pl_mul, ih, R_of]
    exact (single_mul _ _).trans (by simp)

theorem pl_ofPair (s : W A) : pl (ofPair s) = single s := by
  rw [ofPair, pl_mul, pl_L, pl_R, single_mul]; simp

/-- **Theorem 5.** For a string `s` and a term `e`, `s ≤ e` iff `s ∈ l(e)`. -/
theorem ofPair_le_iff_mem (s : W A) (e : TD A) : ofPair s ≤ e ↔ SetSemiring.Mem s (pl e) := by
  constructor
  · intro h
    have := pl_mono h
    rw [pl_ofPair] at this
    exact (SetSemiring.le_iff _ _).1 this s rfl
  · induction e using FreePreKA.ind generalizing s with
    | h r =>
    induction r generalizing s with
    | zero => exact fun h => absurd h (SetSemiring.mem_zero s)
    | one =>
      intro h; rw [show s = 1 from h, ofPair_one]; exact le_rfl
    | sym x =>
      intro h
      rcases x with a | a <;> rw [show s = _ from h] <;>
        simp only [ofPair, L_of, R_of, map_one, mul_one, one_mul] <;> exact le_rfl
    | plus e f ihe ihf =>
      intro h
      rw [mk_plus, pl_add, SetSemiring.mem_add] at h
      rcases h with h | h
      · exact (ihe s h).trans (by rw [mk_plus]; exact le_add_right le_rfl)
      · exact (ihf s h).trans (by rw [mk_plus]; exact le_add_left le_rfl)
    | mul e f ihe ihf =>
      intro h
      rw [mk_mul, pl_mul, SetSemiring.mem_mul] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      rw [ofPair_mul, mk_mul]
      exact mul_le_mul' (ihe a ha) (ihf b hb)
    | star e ihe =>
      intro h
      rw [mk_star, pl_kstar, SetSemiring.mem_kstar] at h
      obtain ⟨l, hl, rfl⟩ := h
      rw [mk_star, ofPair_list_prod]
      refine le_trans ?_ (pow_le_kstar' _ l.length)
      induction l with
      | nil => simp
      | cons a l ih =>
        rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
        exact mul_le_mul' (ihe a (hl a (by simp))) (ih fun y hy => hl y (by simp [hy]))

/-! ### Corollary 8 -/

/-- A term with empty language is `0`. This is the true special case of Corollary 7 that
Corollary 8 needs. It holds because star, `1` and generators always have nonempty languages. -/
theorem eq_zero_of_pl_eq_zero (e : TD A) (h : ∀ s, ¬ SetSemiring.Mem s (pl e)) : e = 0 := by
  induction e using FreePreKA.ind with
  | h r =>
  induction r with
  | zero => rfl
  | one => exact (h 1 rfl).elim
  | sym x => rcases x with a | a <;> exact (h _ rfl).elim
  | plus e f ihe ihf =>
    rw [mk_plus, ihe fun s hs => h s (by rw [mk_plus, pl_add, SetSemiring.mem_add]; exact Or.inl hs),
      ihf fun s hs => h s (by rw [mk_plus, pl_add, SetSemiring.mem_add]; exact Or.inr hs), add_zero]
  | mul e f ihe ihf =>
    by_cases he : ∃ a, SetSemiring.Mem a (pl (mk e))
    · obtain ⟨a, ha⟩ := he
      rw [mk_mul, ihf fun b hb => h (a * b) (by
        rw [mk_mul, pl_mul, SetSemiring.mem_mul]; exact ⟨a, ha, b, hb, rfl⟩), mul_zero]
    · simp only [not_exists] at he
      rw [mk_mul, ihe he, zero_mul]
  | star e _ =>
    exact (h 1 (by rw [mk_star, pl_kstar, SetSemiring.mem_kstar_iff_unfold]; exact Or.inl rfl)).elim

/-- **Corollary 8.** Every nonzero term lies above some string. -/
theorem exists_ofPair_le (e : TD A) (he : e ≠ 0) : ∃ s, ofPair s ≤ e := by
  by_contra H
  simp only [not_exists] at H
  exact he (eq_zero_of_pl_eq_zero e fun s hs => H s ((ofPair_le_iff_mem s e).2 hs))

theorem zero_ne_one : (0 : TD A) ≠ 1 := fun h => by
  have : SetSemiring.Mem (1 : W A) (pl (1 : TD A)) := rfl
  rw [← h, pl_zero] at this
  exact SetSemiring.mem_zero _ this

/-! ### Nullability `[−]₀` -/

theorem fm_mul_eq_one {u u' : FreeMonoid A} : u * u' = 1 ↔ u = 1 ∧ u' = 1 :=
  List.append_eq_nil_iff

theorem W.mul_eq_one {s t : W A} : s * t = 1 ↔ s = 1 ∧ t = 1 := by
  obtain ⟨u, v⟩ := s; obtain ⟨u', v'⟩ := t
  simp only [Prod.mk_mul_mk, Prod.mk_eq_one, fm_mul_eq_one]
  tauto

/-- `1 ∈ l(e)`. -/
def Nullable (e : TD A) : Prop := SetSemiring.Mem (1 : W A) (pl e)

theorem nullable_iff (e : TD A) : Nullable e ↔ 1 ≤ e := by
  rw [Nullable, ← ofPair_le_iff_mem, ofPair_one]

theorem nullable_add (e f : TD A) : Nullable (e + f) ↔ Nullable e ∨ Nullable f := by
  simp only [Nullable, pl_add, SetSemiring.mem_add]

theorem nullable_mul (e f : TD A) : Nullable (e * f) ↔ Nullable e ∧ Nullable f := by
  simp only [Nullable, pl_mul, SetSemiring.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨rfl, rfl⟩ := W.mul_eq_one.1 hab
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩; exact ⟨1, ha, 1, hb, mul_one 1⟩

theorem nullable_kstar (e : TD A) : Nullable e∗ := by
  rw [Nullable, pl_kstar, SetSemiring.mem_kstar_iff_unfold]; exact Or.inl rfl

theorem nullable_one : Nullable (1 : TD A) := rfl

theorem not_nullable_zero : ¬ Nullable (0 : TD A) := SetSemiring.mem_zero _

theorem not_nullable_of : ∀ x : A ⊕ A, ¬ Nullable (of x : TD A)
  | .inl a => fun h =>
    FreeMonoid.of_ne_one a (congrArg Prod.fst (h : (1 : W A) = (FreeMonoid.of a, 1))).symm
  | .inr a => fun h =>
    FreeMonoid.of_ne_one a (congrArg Prod.snd (h : (1 : W A) = (1, FreeMonoid.of a))).symm

open Classical in
/-- The constant term `[e]₀ ∈ {0, 1}`. -/
noncomputable def nul (e : TD A) : TD A := if Nullable e then 1 else 0

theorem nul_le (e : TD A) : nul e ≤ e := by
  unfold nul; split_ifs with h
  · exact (nullable_iff e).1 h
  · rw [← add_eq_right_iff_le, zero_add]

theorem nul_eq_one_iff (e : TD A) : nul e = 1 ↔ 1 ≤ e := by
  rw [← nullable_iff]; unfold nul; split_ifs with h
  · simp [h]
  · simp only [h, iff_false]; exact zero_ne_one

theorem nul_commute (e x : TD A) : Commute (nul e) x := by
  unfold nul; split_ifs
  exacts [Commute.one_left x, Commute.zero_left x]

theorem nul_add (e f : TD A) : nul (e + f) = nul e + nul f := by
  unfold nul
  by_cases he : Nullable e <;> by_cases hf : Nullable f
  · rw [ite_eq_left ((nullable_add e f).2 (Or.inl he)), ite_eq_left he, ite_eq_left hf, add_idem]
  · rw [ite_eq_left ((nullable_add e f).2 (Or.inl he)), ite_eq_left he, ite_eq_right hf, add_zero]
  · rw [ite_eq_left ((nullable_add e f).2 (Or.inr hf)), ite_eq_right he, ite_eq_left hf, zero_add]
  · rw [ite_eq_right (by rw [nullable_add]; tauto), ite_eq_right he, ite_eq_right hf, add_zero]

theorem nul_mul (e f : TD A) : nul (e * f) = nul e * nul f := by
  unfold nul
  by_cases he : Nullable e <;> by_cases hf : Nullable f
  · rw [ite_eq_left ((nullable_mul e f).2 ⟨he, hf⟩), ite_eq_left he, ite_eq_left hf, mul_one]
  · rw [ite_eq_right (by rw [nullable_mul]; tauto), ite_eq_left he, ite_eq_right hf, mul_zero]
  · rw [ite_eq_right (by rw [nullable_mul]; tauto), ite_eq_right he, ite_eq_left hf, zero_mul]
  · rw [ite_eq_right (by rw [nullable_mul]; tauto), ite_eq_right he, ite_eq_right hf, mul_zero]

/-! ### Lengths -/

/-- The size `|s| = |π_l s| + |π_r s|` of a string over `Σ̈`. -/
def size (s : W A) : ℕ := s.1.length + s.2.length

@[simp] theorem size_mul (s t : W A) : size (s * t) = size s + size t := by
  simp only [size, Prod.fst_mul, Prod.snd_mul, FreeMonoid.length_mul]; omega

@[simp] theorem size_one : size (1 : W A) = 0 := rfl

end TD

end DiagonaLean.KAComm
