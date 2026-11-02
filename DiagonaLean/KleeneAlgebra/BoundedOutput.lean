/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Expansion
import DiagonaLean.KleeneAlgebra.Representable
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Bounded-output terms (§5.2, Def 28, Lemmas 29–31)

A term `e ∈ T Σ̈` has *fanout* `k` when each string `s ≤ e` satisfies
`|π_r s| ≤ (|π_l s| + 1) k`. Such terms relate each word to finitely many words (Lemma 29), are
closed under the regular operations (Lemma 30), and admit an expansion whose long prefixes obey
the same bound (Lemma 31).

## Main statements

* `TD.Fanout`, `TD.BoundedOutput`: Definition 28.
* `TD.Fanout.next_finite`: Lemma 29.
* `TD.Fanout.zero/one/of/add/mul/kstar`: Lemma 30.
* `TD.IsAutomaton.lemma31`: Lemma 31.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], §5.2
-/

open scoped Computability

namespace DiagonaLean.KAComm

namespace TD

open FreePreKA Classical

variable {A : Type*}

/-- `e` has fanout `k`: `|π_r s| ≤ (|π_l s| + 1) k` for every string `s ≤ e`. -/
def Fanout (e : TD A) (k : ℕ) : Prop :=
  ∀ s, SetSemiring.Mem s (pl e) → s.2.length ≤ (s.1.length + 1) * k

/-- **Definition 28.** -/
def BoundedOutput (e : TD A) : Prop := ∃ k, Fanout e k

namespace Fanout

variable {e : TD A} {k : ℕ}

theorem mono (h : Fanout e k) {k' : ℕ} (hk : k ≤ k') : Fanout e k' :=
  fun s hs => (h s hs).trans (Nat.mul_le_mul_left _ hk)

/-- **Lemma 29**, the length bound. -/
theorem length_le_of_mem_next [Fintype A] [DecidableEq A] (h : Fanout e k)
    {Λ : Finset (FreeMonoid A)} {m : ℕ}
    (hm : ∀ u ∈ Λ, u.length ≤ m) {v : FreeMonoid A} (hv : v ∈ Next e ↑Λ) :
    v.length ≤ (m + 1) * k := by
  obtain ⟨u, hu, huv⟩ := hv
  exact (h _ huv).trans (Nat.mul_le_mul_right _ (by have := hm u hu; simp only at this ⊢; omega))

/-- **Lemma 29**, finiteness. -/
theorem next_finite [Fintype A] [DecidableEq A] (h : Fanout e k) (Λ : Finset (FreeMonoid A)) :
    (Next e ↑Λ).Finite :=
  (List.finite_length_le A ((Λ.sup FreeMonoid.length + 1) * k)).subset fun _ hv =>
    h.length_le_of_mem_next (fun _ hu => Finset.le_sup (f := FreeMonoid.length) hu) hv

/-! ### Lemma 30 -/

theorem zero : Fanout (0 : TD A) k := fun s hs => absurd hs (SetSemiring.mem_zero s)

theorem one : Fanout (1 : TD A) k := fun s hs => by
  rw [show s = 1 from hs]; exact Nat.zero_le _

theorem of : ∀ x : A ⊕ A, Fanout (FreePreKA.of x : TD A) 1
  | .inl a => fun s hs => by
    rw [show s = (FreeMonoid.of a, 1) from hs]; exact Nat.zero_le _
  | .inr a => fun s hs => by
    rw [show s = (1, FreeMonoid.of a) from hs]; simp

theorem add {a b : TD A} {k₁ k₂ : ℕ} (ha : Fanout a k₁) (hb : Fanout b k₂) :
    Fanout (a + b) (max k₁ k₂) := fun s hs => by
  rw [pl_add, SetSemiring.mem_add] at hs
  rcases hs with hs | hs
  exacts [(ha.mono (le_max_left _ _)) s hs, (hb.mono (le_max_right _ _)) s hs]

theorem mul {a b : TD A} {k₁ k₂ : ℕ} (ha : Fanout a k₁) (hb : Fanout b k₂) :
    Fanout (a * b) (2 * max k₁ k₂) := fun s hs => by
  rw [pl_mul, SetSemiring.mem_mul] at hs
  obtain ⟨t, ht, u, hu, rfl⟩ := hs
  have h1 := (ha.mono (le_max_left k₁ k₂)) t ht
  have h2 := (hb.mono (le_max_right k₁ k₂)) u hu
  simp only [Prod.fst_mul, Prod.snd_mul, FreeMonoid.length_mul] at h1 h2 ⊢
  set K := max k₁ k₂
  have : (t.1.length + u.1.length + 1) * (2 * K) =
      (t.1.length + 1) * K + (u.1.length + 1) * K + (t.1.length + u.1.length) * K := by ring
  omega

theorem kstar {a : TD A} (ha : Fanout a k) (hl : ∀ s, SetSemiring.Mem s (pl a) → 1 ≤ s.1.length) :
    Fanout a∗ (2 * k) := fun s hs => by
  rw [pl_kstar, SetSemiring.mem_kstar] at hs
  obtain ⟨l, hl', rfl⟩ := hs
  have key : l.prod.2.length ≤ 2 * k * l.prod.1.length := by
    induction l with
    | nil => simp
    | cons y l ih =>
      have hy := ha y (hl' y (by simp))
      have hy1 := hl y (hl' y (by simp))
      have ih := ih fun z hz => hl' z (by simp [hz])
      simp only [List.prod_cons, Prod.fst_mul, Prod.snd_mul, FreeMonoid.length_mul]
      have : k ≤ y.1.length * k := Nat.le_mul_of_pos_left k hy1
      have : 2 * k * (y.1.length + l.prod.1.length) =
          y.1.length * k + y.1.length * k + 2 * k * l.prod.1.length := by ring
      have : (y.1.length + 1) * k = y.1.length * k + k := by ring
      omega
  have : (l.prod.1.length + 1) * (2 * k) = 2 * k * l.prod.1.length + 2 * k := by ring
  omega

end Fanout

/-! ### Lemma 31 -/

variable [Fintype A]

/-- **Lemma 31.** A bounded-output state of an automaton has a fanout `k` such that, for every
`n`, its expansion of depth `n` only uses prefixes `s` with `|π_r s| ≤ (|π_l s| + 1) k`. -/
theorem IsAutomaton.lemma31 {S : Finset (TD A)} (hS : IsAutomaton S) {e : TD A} (he : e ∈ S)
    {k₀ : ℕ} (hk₀ : Fanout e k₀) : ∃ k, Fanout e k ∧ ∀ n, ∃ (B T : Finset (W A))
      (es : W A → TD A), (∀ s, s ∈ B ↔ ofPair s ≤ e ∧ size s < n) ∧
      (∀ s ∈ T, size s = n ∧ s.2.length ≤ (s.1.length + 1) * k) ∧ (∀ s, es s ∈ S) ∧
      e = ∑ s ∈ B, ofPair s + ∑ s ∈ T, ofPair s * es s := by
  -- A witness string below each nonzero state (Corollary 8).
  let wit : TD A → W A := fun e' => if h : e' ≠ 0 then (exists_ofPair_le e' h).choose else 1
  have hwit : ∀ e', e' ≠ 0 → ofPair (wit e') ≤ e' := fun e' h => by
    simp only [wit, ne_eq, h, not_false_eq_true, ↓reduceDIte]
    exact (exists_ofPair_le e' h).choose_spec
  let m := S.sup fun e' => (wit e').1.length
  refine ⟨(m + 1) * k₀, hk₀.mono (Nat.le_mul_of_pos_left _ (Nat.succ_pos m)), fun n => ?_⟩
  obtain ⟨B, T, es, hB, hT, hes, heq⟩ := hS.expansion he n
  have hTe : ∑ s ∈ T, ofPair s * es s ≤ e := by
    conv_rhs => rw [heq]
    exact le_add_left le_rfl
  refine ⟨B, T.filter (fun s => es s ≠ 0), es, hB, fun s hs => ?_, hes, ?_⟩
  · obtain ⟨hsT, hne⟩ := Finset.mem_filter.1 hs
    refine ⟨hT s hsT, ?_⟩
    set w := wit (es s)
    have hw : w.1.length ≤ m := Finset.le_sup (f := fun e' => (wit e').1.length) (hes s)
    have hsw : SetSemiring.Mem (s * w) (pl e) := by
      rw [← ofPair_le_iff_mem, ofPair_mul]
      exact (mul_le_mul' le_rfl (hwit _ hne)).trans
        ((le_sum_of_mem (fun s => ofPair s * es s) hsT).trans hTe)
    have h := hk₀ _ hsw
    simp only [Prod.fst_mul, Prod.snd_mul, FreeMonoid.length_mul] at h
    have h1 : (s.1.length + w.1.length + 1) * k₀ ≤ (s.1.length + m + 1) * k₀ :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (s.1.length + 1) * ((m + 1) * k₀) =
        (s.1.length + m + 1) * k₀ + s.1.length * m * k₀ := by ring
    omega
  · rw [Finset.sum_filter]
    refine heq.trans (congrArg _ (Finset.sum_congr rfl fun s _ => ?_))
    split_ifs with h
    · rfl
    · rw [not_not.1 h, mul_zero]

end TD

end DiagonaLean.KAComm
