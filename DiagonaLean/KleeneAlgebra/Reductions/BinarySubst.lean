/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Reductions.ExprCode

@[expose] public section

/-! # Substituting words for letters

The paper fixes `Σ = {0, 1}`. This file provides the tools to move from `ℕ` to `{0, 1}`, by
substituting each letter `n` with the word `1ⁿ0`.

* A substitution preserves provable equality (`Equiv.sb`, `KAEquiv.sb`). The commutation rule needs
  a left word to commute with a right word.
* An injective substitution reflects inclusion in the language model (`pl_le_of_sb`). The word code
  is a prefix code, so it is injective (`cd_injective`).
* `subC` computes the substitution on expression codes and is primitive recursive, so a machine
  can search for proofs of the substituted instance. The proof enumerator runs over `ℕ ⊕ ℕ`, and
  `equiv_iff_map` shows that nothing is lost on the letters `0` and `1`.
-/

open scoped Computability

namespace DiagonaLean.KAComm.Reduction

open Cslib.Turing Enc RExp FreePreKA TD Nat.Partrec DiagonaLean.Foundations.Computability
open DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation Undec

/-! ### Substitution -/

section subst

variable {A B : Type*}

/-- The left copy of a word. -/
def lW (u : List B) : RExp (B ⊕ B) := prodL (u.map fun a => sym (.inl a))

/-- The right copy of a word. -/
def rW (u : List B) : RExp (B ⊕ B) := prodL (u.map fun a => sym (.inr a))

/-- Substitute each letter with a word, keeping its side. -/
def sb (w : A → List B) : RExp (A ⊕ A) → RExp (B ⊕ B)
  | RExp.zero => RExp.zero
  | RExp.one => RExp.one
  | RExp.sym (.inl a) => lW (w a)
  | RExp.sym (.inr a) => rW (w a)
  | RExp.plus e f => RExp.plus (sb w e) (sb w f)
  | RExp.mul e f => RExp.mul (sb w e) (sb w f)
  | RExp.star e => RExp.star (sb w e)

theorem comm_words (u v : List B) :
    Equiv DComm (mul (lW u) (rW v)) (mul (rW v) (lW u)) := by
  refine (mk_eq_mk (C := DComm)).1 ?_
  simp only [mk_mul, lW, rW, mk_prodL, List.map_map]
  refine Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 hy
  exact (mk_eq_mk (C := DComm)).2 (RExp.Equiv.comm (x := (Sum.inl a : B ⊕ B)) (y := Sum.inr b) trivial)

/-- Substitution preserves provable equality in pre-Kleene algebra. -/
theorem Equiv.sb (w : A → List B) {e f : RExp (A ⊕ A)} (h : Equiv DComm e f) :
    Equiv DComm (Reduction.sb w e) (Reduction.sb w f) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | plus _ _ ih₁ ih₂ => exact .plus ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact .mul ih₁ ih₂
  | star _ ih => exact .star ih
  | plus_assoc => exact .plus_assoc _ _ _
  | plus_comm => exact .plus_comm _ _
  | zero_plus => exact .zero_plus _
  | plus_idem => exact .plus_idem _
  | mul_assoc => exact .mul_assoc _ _ _
  | one_mul => exact .one_mul _
  | mul_one => exact .mul_one _
  | zero_mul => exact .zero_mul _
  | mul_zero => exact .mul_zero _
  | left_distrib => exact .left_distrib _ _ _
  | right_distrib => exact .right_distrib _ _ _
  | unfold => exact .unfold _
  | @comm x y hxy =>
    rcases x with a | a <;> rcases y with b | b
    · exact hxy.elim
    · exact comm_words _ _
    · exact (comm_words _ _).symm
    · exact hxy.elim

/-- Substitution preserves provable equality in Kleene algebra. -/
theorem KAEquiv.sb (w : A → List B) {e f : RExp (A ⊕ A)} (h : KAEquiv DComm e f) :
    KAEquiv DComm (Reduction.sb w e) (Reduction.sb w f) := by
  induction h with
  | ofEquiv h => exact .ofEquiv (Equiv.sb w h)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | plus _ _ ih₁ ih₂ => exact .plus ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact .mul ih₁ ih₂
  | star _ ih => exact .star ih
  | kstar_mul_le _ => exact .kstar_mul_le _
  | mul_kstar_le_self _ ih => exact .mul_kstar_le_self ih
  | kstar_mul_le_self _ ih => exact .kstar_mul_le_self ih

/-- Renaming preserves provable equality in Kleene algebra. -/
theorem KAEquiv.map' (g : A → B) {e f : RExp (A ⊕ A)} (h : KAEquiv DComm e f) :
    KAEquiv DComm (e.map (dmap g)) (f.map (dmap g)) := by
  induction h with
  | ofEquiv h => exact .ofEquiv (RExp.Equiv.map _ (dComm_dmap g) h)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | plus _ _ ih₁ ih₂ => exact .plus ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact .mul ih₁ ih₂
  | star _ ih => exact .star ih
  | kstar_mul_le _ => exact .kstar_mul_le _
  | mul_kstar_le_self _ ih => exact .mul_kstar_le_self ih
  | kstar_mul_le_self _ ih => exact .kstar_mul_le_self ih

theorem map_map' {C : Type*} (g : A → B) (h : B → C) (e : RExp A) :
    (e.map g).map h = e.map (h ∘ g) := by
  induction e with
  | zero => rfl
  | one => rfl
  | sym x => rfl
  | plus e f ihe ihf => simp [RExp.map, ihe, ihf]
  | mul e f ihe ihf => simp [RExp.map, ihe, ihf]
  | star e ih => simp [RExp.map, ih]

theorem map_id' (e : RExp A) : e.map id = e := by
  induction e with
  | zero => rfl
  | one => rfl
  | sym x => rfl
  | plus e f ihe ihf => simp [RExp.map, ihe, ihf]
  | mul e f ihe ihf => simp [RExp.map, ihe, ihf]
  | star e ih => simp [RExp.map, ih]

/-! ### The language model -/

/-- A word substitution on the free monoid. -/
def cd (w : A → List B) : FreeMonoid A →* FreeMonoid B :=
  FreeMonoid.lift fun a => FreeMonoid.ofList (w a)

/-- A word substitution on strings of `Σ̈`. -/
def wsub (w : A → List B) : W A →* W B := MonoidHom.prodMap (cd w) (cd w)

theorem pl_lW (u : List B) : pl (mk (lW u) : TD B) = single (FreeMonoid.ofList u, 1) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    have : (mk (lW (a :: u)) : TD B) = mk (sym (.inl a)) * mk (lW u) := rfl
    rw [this, pl_mul, ih]
    show gen (.inl a) * _ = _
    simp only [gen, single_mul]
    congr 1

theorem pl_rW (u : List B) : pl (mk (rW u) : TD B) = single (1, FreeMonoid.ofList u) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    have : (mk (rW (a :: u)) : TD B) = mk (sym (.inr a)) * mk (rW u) := rfl
    rw [this, pl_mul, ih]
    show gen (.inr a) * _ = _
    simp only [gen, single_mul]
    congr 1

/-- The language of a substituted expression is the image of the language. -/
theorem mem_pl_sb (w : A → List B) (e : RExp (A ⊕ A)) (y : W B) :
    SetSemiring.Mem y (pl (mk (Reduction.sb w e))) ↔
      ∃ x, SetSemiring.Mem x (pl (mk e)) ∧ wsub w x = y := by
  induction e generalizing y with
  | zero =>
    simp only [Reduction.sb, mk_zero, pl_zero]
    exact iff_of_false (SetSemiring.mem_zero y) fun ⟨x, hx, _⟩ => SetSemiring.mem_zero x hx
  | one =>
    simp only [Reduction.sb, mk_one, pl_one, SetSemiring.mem_one]
    exact ⟨fun h => ⟨1, rfl, by rw [map_one, h]⟩, fun ⟨x, hx, h⟩ => by rw [← h, hx, map_one]⟩
  | sym x =>
    rcases x with a | a
    · change SetSemiring.Mem y (pl (mk (lW (w a)))) ↔
        ∃ x, SetSemiring.Mem x (gen (Sum.inl a)) ∧ wsub w x = y
      rw [pl_lW]
      simp only [gen, mem_single, exists_eq_left]
      simp [wsub, cd, eq_comm]
    · change SetSemiring.Mem y (pl (mk (rW (w a)))) ↔
        ∃ x, SetSemiring.Mem x (gen (Sum.inr a)) ∧ wsub w x = y
      rw [pl_rW]
      simp only [gen, mem_single, exists_eq_left]
      simp [wsub, cd, eq_comm]
  | plus e f ihe ihf =>
    simp only [Reduction.sb, mk_plus, pl_add, SetSemiring.mem_add, ihe, ihf]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      exacts [⟨x, Or.inl hx, rfl⟩, ⟨x, Or.inr hx, rfl⟩]
    · rintro ⟨x, hx | hx, rfl⟩
      exacts [Or.inl ⟨x, hx, rfl⟩, Or.inr ⟨x, hx, rfl⟩]
  | mul e f ihe ihf =>
    simp only [Reduction.sb, mk_mul, pl_mul, SetSemiring.mem_mul, ihe, ihf]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, map_mul _ _ _⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, (map_mul _ _ _).symm⟩
  | star e ihe =>
    simp only [Reduction.sb, mk_star, pl_kstar, SetSemiring.mem_kstar]
    constructor
    · rintro ⟨l, hl, rfl⟩
      induction l with
      | nil => exact ⟨1, ⟨[], by simp, rfl⟩, by simp⟩
      | cons z l ih =>
        obtain ⟨x, hx, rfl⟩ := (ihe z).1 (hl z (by simp))
        obtain ⟨x', ⟨l', hl', rfl⟩, hx'⟩ := ih fun y hy => hl y (by simp [hy])
        refine ⟨x * l'.prod, ⟨x :: l', ?_, List.prod_cons⟩, ?_⟩
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          exacts [hx, hl' y hy]
        · rw [map_mul, hx', List.prod_cons]
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨l.map (wsub w), fun y hy => ?_, (map_list_prod _ _).symm⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact (ihe _).2 ⟨x, hl x hx, rfl⟩

theorem wsub_injective {w : A → List B} (h : Function.Injective (cd w)) :
    Function.Injective (wsub w) :=
  Prod.map_injective.2 ⟨h, h⟩

/-- An injective substitution reflects inclusion in the language model. -/
theorem pl_le_of_sb {w : A → List B} (hw : Function.Injective (cd w)) {e f : RExp (A ⊕ A)}
    (h : pl (mk (Reduction.sb w e)) ≤ pl (mk (Reduction.sb w f))) : pl (mk e) ≤ pl (mk f) := by
  intro x hx
  obtain ⟨x', hx', he⟩ := (mem_pl_sb w f _).1 (h ((mem_pl_sb w e _).2 ⟨x, hx, rfl⟩))
  rwa [← wsub_injective hw he]

/-- A substitution preserves inclusion in the language model. -/
theorem pl_sb_le (w : A → List B) {e f : RExp (A ⊕ A)} (h : pl (mk e) ≤ pl (mk f)) :
    pl (mk (Reduction.sb w e)) ≤ pl (mk (Reduction.sb w f)) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_pl_sb w e y).1 hy
  exact (mem_pl_sb w f _).2 ⟨x, h hx, rfl⟩

/-- An injective substitution preserves and reflects language equality. -/
theorem pl_sb_eq_iff {w : A → List B} (hw : Function.Injective (cd w)) {e f : RExp (A ⊕ A)} :
    pl (mk (Reduction.sb w e)) = pl (mk (Reduction.sb w f)) ↔ pl (mk e) = pl (mk f) :=
  ⟨fun h => le_antisymm (pl_le_of_sb hw h.le) (pl_le_of_sb hw h.ge),
    fun h => le_antisymm (pl_sb_le w h.le) (pl_sb_le w h.ge)⟩

end subst

/-! ### The prefix code -/

/-- The word of a letter: `1ⁿ0`. -/
def wordOf (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Decoding. -/
def decW (l : List Bool) : List ℕ :=
  l.foldr (fun b acc => if b then (acc.headI + 1) :: acc.tail else 0 :: acc) []

theorem decW_word (n : ℕ) (r : List Bool) : decW (wordOf n ++ r) = n :: decW r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : decW (wordOf (n + 1) ++ r) =
        ((decW (wordOf n ++ r)).headI + 1) :: (decW (wordOf n ++ r)).tail := by
      simp [wordOf, List.replicate_succ, decW]
    rw [h, ih]
    rfl

theorem cd_toList (l : List ℕ) :
    FreeMonoid.toList (cd wordOf (FreeMonoid.ofList l)) = l.flatMap wordOf := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have : (FreeMonoid.ofList (a :: l)) = FreeMonoid.of a * FreeMonoid.ofList l := rfl
    rw [this, map_mul, FreeMonoid.toList_mul, ih]
    simp [cd]

theorem decW_flatMap (l : List ℕ) : decW (l.flatMap wordOf) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, decW_word, ih]

/-- The code is injective. -/
theorem cd_injective : Function.Injective (cd wordOf) := fun u v h => by
  have h' := congrArg FreeMonoid.toList h
  have hu := cd_toList (FreeMonoid.toList u)
  have hv := cd_toList (FreeMonoid.toList v)
  simp only [FreeMonoid.ofList_toList] at hu hv
  rw [hu, hv] at h'
  have := congrArg decW h'
  rw [decW_flatMap, decW_flatMap] at this
  exact FreeMonoid.toList.injective this

/-! ### Back to `ℕ ⊕ ℕ`, for the proof enumerator -/

/-- The letters `0` and `1` of `ℕ`. -/
def boolNat (b : Bool) : ℕ := b.toNat

/-- A retraction of `boolNat`. -/
def natBool (n : ℕ) : Bool := decide (n ≠ 0)

theorem natBool_comp : natBool ∘ boolNat = id := by
  funext b
  cases b <;> rfl

theorem dmap_natBool_comp :
    (dmap natBool) ∘ (dmap boolNat) = (id : Bool ⊕ Bool → Bool ⊕ Bool) := by
  funext x
  rcases x with b | b <;> cases b <;> rfl

/-- Over the letters `0` and `1`, provable equality in pre-Kleene algebra is the same in `ℕ ⊕ ℕ` as
in `Bool ⊕ Bool`. -/
theorem equiv_iff_map {e f : RExp (Bool ⊕ Bool)} :
    Equiv DComm (e.map (dmap boolNat)) (f.map (dmap boolNat)) ↔ Equiv DComm e f := by
  constructor
  · intro h
    have := RExp.Equiv.map _ (dComm_dmap natBool) h
    rwa [map_map', map_map', dmap_natBool_comp, map_id', map_id'] at this
  · exact RExp.Equiv.map _ (dComm_dmap boolNat)

/-- Over the letters `0` and `1`, provable equality in Kleene algebra is the same in `ℕ ⊕ ℕ` as in
`Bool ⊕ Bool`. -/
theorem kaEquiv_iff_map {e f : RExp (Bool ⊕ Bool)} :
    KAEquiv DComm (e.map (dmap boolNat)) (f.map (dmap boolNat)) ↔ KAEquiv DComm e f := by
  constructor
  · intro h
    have := KAEquiv.map' natBool h
    rwa [map_map', map_map', dmap_natBool_comp, map_id', map_id'] at this
  · exact KAEquiv.map' boolNat

/-! ### Computing the substitution on codes -/

/-- The code of the word of a letter code: `s / 2` ones and a zero, on the side given by `s % 2`. -/
def wC (s : ℕ) : ℕ := (fun acc => cm (cs (2 + s % 2)) acc)^[s / 2] (cm (cs (s % 2)) co)

/-- One entry of the table of `subC`: the entry at the current length of `L`. -/
def subV (L : List ℕ) : ℕ :=
  if L.length.unpair.1 = 2 then wC L.length.unpair.2
  else if L.length.unpair.1 = 3 then
    cp (L.getD L.length.unpair.2.unpair.1 0) (L.getD L.length.unpair.2.unpair.2 0)
  else if L.length.unpair.1 = 4 then
    cm (L.getD L.length.unpair.2.unpair.1 0) (L.getD L.length.unpair.2.unpair.2 0)
  else if L.length.unpair.1 = 5 then ct (L.getD L.length.unpair.2 0)
  else L.length

/-- The table of `subC` below `n`. -/
def subT (n : ℕ) : List ℕ := (fun L => L ++ [subV L])^[n] []

/-- The substitution, on expression codes. -/
def subC (n : ℕ) : ℕ := subV (subT n)

theorem subT_succ (n : ℕ) : subT (n + 1) = subT n ++ [subC n] := by
  simp only [subT, Function.iterate_succ_apply', subC]

theorem length_subT (n : ℕ) : (subT n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [subT_succ, ih]

theorem subT_get {n k : ℕ} (hk : k < n) : (subT n).getD k 0 = subC k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [subT_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
    · rw [List.getD_append _ _ _ _ (by simpa [length_subT] using h)]
      exact ih h
    · rw [List.getD_append_right _ _ _ _ (by simp [length_subT])]
      simp [length_subT]

theorem lt_pair_tag {t x : ℕ} (ht : 0 < t) : x < Nat.pair t x :=
  lt_of_le_of_lt (Nat.right_le_pair 0 x) (Nat.pair_lt_pair_left x ht)

theorem subC_eq (n : ℕ) : subC n = subV (subT n) := rfl

theorem subC_cs (s : ℕ) : subC (cs s) = wC s := by
  simp [subC, subV, length_subT, cs]

theorem subC_cz : subC cz = cz := by
  simp [subC, subV, length_subT, cz]

theorem subC_co : subC co = co := by
  simp [subC, subV, length_subT, co]

theorem subC_cp (a b : ℕ) : subC (cp a b) = cp (subC a) (subC b) := by
  have h : Nat.pair a b < cp a b := lt_pair_tag (by omega)
  have ha : a < cp a b := lt_of_le_of_lt (Nat.left_le_pair a b) h
  have hb : b < cp a b := lt_of_le_of_lt (Nat.right_le_pair a b) h
  simp only [subC_eq (cp a b), subV, length_subT]
  rw [show (cp a b).unpair = (3, Nat.pair a b) from Nat.unpair_pair _ _]
  have e₁ := subT_get ha
  have e₂ := subT_get hb
  simp only [List.getD_eq_getElem?_getD] at e₁ e₂
  simp [e₁, e₂]

theorem subC_cm (a b : ℕ) : subC (cm a b) = cm (subC a) (subC b) := by
  have h : Nat.pair a b < cm a b := lt_pair_tag (by omega)
  have ha : a < cm a b := lt_of_le_of_lt (Nat.left_le_pair a b) h
  have hb : b < cm a b := lt_of_le_of_lt (Nat.right_le_pair a b) h
  simp only [subC_eq (cm a b), subV, length_subT]
  rw [show (cm a b).unpair = (4, Nat.pair a b) from Nat.unpair_pair _ _]
  have e₁ := subT_get ha
  have e₂ := subT_get hb
  simp only [List.getD_eq_getElem?_getD] at e₁ e₂
  simp [e₁, e₂]

theorem subC_ct (a : ℕ) : subC (ct a) = ct (subC a) := by
  have ha : a < ct a := lt_pair_tag (by omega)
  simp only [subC_eq (ct a), subV, length_subT]
  rw [show (ct a).unpair = (5, a) from Nat.unpair_pair _ _]
  have e₁ := subT_get ha
  simp only [List.getD_eq_getElem?_getD] at e₁
  simp [e₁]

/-- The substitution of the two-letter layer. -/
abbrev sbB : RExp (ℕ ⊕ ℕ) → RExp (Bool ⊕ Bool) := sb wordOf

/-- The expression over `ℕ ⊕ ℕ` for a two-letter expression. -/
abbrev toNat (e : RExp (Bool ⊕ Bool)) : RExp (ℕ ⊕ ℕ) := e.map (dmap boolNat)

theorem rc_lW (a : ℕ) : rc (toNat (lW (wordOf a))) = wC (symC (.inl a)) := by
  have h2 : 2 * a % 2 = 0 := by omega
  have h3 : 2 * a / 2 = a := by omega
  simp only [wC, symC, h2, h3]
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    have h2' : 2 * a % 2 = 0 := by omega
    have h3' : 2 * a / 2 = a := by omega
    rw [← ih h2' h3']
    rfl

theorem rc_rW (a : ℕ) : rc (toNat (rW (wordOf a))) = wC (symC (.inr a)) := by
  have h2 : (2 * a + 1) % 2 = 1 := by omega
  have h3 : (2 * a + 1) / 2 = a := by omega
  simp only [wC, symC, h2, h3]
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    have h2' : (2 * a + 1) % 2 = 1 := by omega
    have h3' : (2 * a + 1) / 2 = a := by omega
    rw [← ih h2' h3']
    rfl

/-- **`subC` computes the substitution.** -/
theorem subC_rc (e : RExp (ℕ ⊕ ℕ)) : subC (rc e) = rc (toNat (sbB e)) := by
  induction e with
  | zero => exact subC_cz
  | one => exact subC_co
  | sym x =>
    rcases x with a | a
    · exact (subC_cs _).trans (rc_lW a).symm
    · exact (subC_cs _).trans (rc_rW a).symm
  | plus e f ihe ihf =>
    show subC (cp (rc e) (rc f)) = cp (rc (toNat (sbB e))) (rc (toNat (sbB f)))
    rw [subC_cp, ihe, ihf]
  | mul e f ihe ihf =>
    show subC (cm (rc e) (rc f)) = cm (rc (toNat (sbB e))) (rc (toNat (sbB f)))
    rw [subC_cm, ihe, ihf]
  | star e ih =>
    show subC (ct (rc e)) = ct (rc (toNat (sbB e)))
    rw [subC_ct, ih]

theorem wC_prim : Primrec wC := by
  unfold wC
  exact Primrec.nat_iterate (prim_div Primrec.id (Primrec.const 2))
    (prim_cm (prim_cs (prim_mod Primrec.id (Primrec.const 2))) (Primrec.const co))
    (Primrec₂.mk (prim_cm (prim_cs (prim_add (Primrec.const 2)
      (prim_mod Primrec.fst (Primrec.const 2)))) Primrec.snd))

theorem subV_prim : Primrec subV := by
  unfold subV
  have hw := wC_prim
  repeat' first
    | exact hw.comp (prim_snd (prim_unpair (prim_length Primrec.id)))
    | prim_step

theorem subC_prim : Primrec subC := by
  have hT : Primrec subT :=
    Primrec.nat_iterate Primrec.id (Primrec.const [])
      (Primrec₂.mk (prim_append Primrec.snd
        (prim_cons (subV_prim.comp Primrec.snd) (Primrec.const []))))
  exact subV_prim.comp hT

end DiagonaLean.KAComm.Reduction
