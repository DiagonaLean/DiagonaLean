/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.BoundedOutput

@[expose] public section

/-! # Single-step representability (Lemmas 33 and 34)

Lemma 33: if two words `s`, `u` over `Σ` diverge (neither is a prefix of the other), then
`s_r u_l` contains a mismatched pair `x_l y_r` (`x ≠ y`) after a common diagonal prefix, so it
lies in the error term `Σ∗ Σ^≠ ⋯`.

Lemma 34: a finite-state, bounded-output term between words of a prefix-free set `L` is a
representable relation on `L`.

## Deviations from the paper's proof of Lemma 34

* Step (4) only needs `≤`, so the reindexing bijection is not needed: each string `t ≤ e` with
  `π_l t = s` contributes `s · (π_r t)_r ≤ s Next_e(s)_r`.
* Step (6) applies Lemma 33 to `s` and `π_l s′` directly (with `|π_l s′| > |s|` and
  prefix-freeness), rather than to `s` and `π_l(s′s″)` followed by a case analysis.
* Lemma 33 is stated with an arbitrary right context `Z` kept *to the right* of the remainder
  string: the paper's form `s_r u_l Σ̈∗ ≤ Σ∗Σ^≠Σ̈∗` is `lemma33'`. Pre-Kleene algebra cannot
  absorb a string to the right of `Σ̈∗`, so Lemma 34 needs the general form.

## Main statements

* `TD.lemma33`, `TD.lemma33'`: Lemma 33.
* `TD.lemma34`: Lemma 34; `TD.lemma34_le` with the explicit residue `Σ̈∗ b`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Lemmas 33, 34
-/

open scoped Computability

namespace DiagonaLean.KAComm

namespace TD

open FreePreKA Classical

variable {A : Type*}

/-- Two diverging lists split as `s₀ a s₁` and `s₀ b u₁` with `a ≠ b`. -/
theorem List.exists_diverge :
    ∀ s u : List A, ¬ s <+: u → ¬ u <+: s →
      ∃ s₀ a s₁ b u₁, a ≠ b ∧ s = s₀ ++ a :: s₁ ∧ u = s₀ ++ b :: u₁
  | [], _, h, _ => absurd (List.nil_prefix) h
  | _ :: _, [], _, h => absurd (List.nil_prefix) h
  | a :: s, b :: u, h₁, h₂ => by
    by_cases hab : a = b
    · subst hab
      rw [List.prefix_cons_inj] at h₁ h₂
      obtain ⟨s₀, c, s₁, d, u₁, hcd, rfl, rfl⟩ := exists_diverge s u h₁ h₂
      exact ⟨a :: s₀, c, s₁, d, u₁, hcd, rfl, rfl⟩
    · exact ⟨[], a, s, b, u, hab, rfl, rfl⟩

/-- `R v` is the string `(ε, v)`. -/
theorem R_eq_ofPair (v : FreeMonoid A) : R v = ofPair (1, v) := by simp [ofPair]

theorem R_mul_L (s u : FreeMonoid A) : R s * L u = ofPair (u, s) := (commute_R_L u s).eq

variable [Fintype A]

/-- `Σ̈`, all symbols. -/
def sigAll : TD A := ∑ x, of x

theorem ofPair_mul_kstar_le (r : W A) : ofPair r * sigAll∗ ≤ (sigAll : TD A)∗ := by
  have hr : ofPair r = (r.1.toList.map (fun a => of (Sum.inl a)) ++
      r.2.toList.map (fun a => of (Sum.inr a)) : List (TD A)).prod := by
    rw [List.prod_append, ofPair, L, R, FreeMonoid.lift_apply, FreeMonoid.lift_apply]
  rw [hr]
  refine list_prod_mul_kstar_le _ _ fun a ha => ?_
  rcases List.mem_append.1 ha with ha | ha <;> obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha <;>
    exact le_sum_of_mem (fun x => (of x : TD A)) (Finset.mem_univ _)

theorem ofPair_le_sigAll_kstar (r : W A) : ofPair r ≤ (sigAll : TD A)∗ :=
  (mul_one _).symm.le.trans ((mul_le_mul' le_rfl (one_le_kstar' _)).trans (ofPair_mul_kstar_le r))

theorem dg_le_sig_kstar (u : FreeMonoid A) : dg u ≤ (sig : TD A)∗ :=
  (mul_one _).symm.le.trans
    ((mul_le_mul' le_rfl (one_le_kstar' _)).trans (dg_mul_kstar_le _ dg_of_le_sig u))

variable [DecidableEq A]

theorem mismatch_le_sigNe {a b : A} (h : a ≠ b) :
    (of (Sum.inl b) * of (Sum.inr a) : TD A) ≤ sigNe :=
  (le_sum_of_mem (fun b' => (of (Sum.inl b) * of (Sum.inr b') : TD A))
      (Finset.mem_filter.2 ⟨Finset.mem_univ a, h⟩)).trans
    (le_sum_of_mem (fun a' => ∑ b' ∈ Finset.univ.filter (· ≠ a'),
      (of (Sum.inl a') * of (Sum.inr b') : TD A)) (Finset.mem_univ b))

/-- **Lemma 33.** If neither of `s`, `u` is a prefix of the other, then for some remainder string
`r` and every `Z`, `s_r u_l Z ≤ Σ∗ Σ^≠ (r Z)`. -/
theorem lemma33 (s u : FreeMonoid A) (h₁ : ¬ s.toList <+: u.toList)
    (h₂ : ¬ u.toList <+: s.toList) :
    ∃ r : W A, ∀ Z : TD A, R s * L u * Z ≤ sig∗ * (sigNe * (ofPair r * Z)) := by
  obtain ⟨s₀, a, s₁, b, u₁, hab, hs, hu⟩ := List.exists_diverge _ _ h₁ h₂
  refine ⟨(FreeMonoid.ofList u₁, FreeMonoid.ofList s₁), fun Z => ?_⟩
  have hsplit : ((u, s) : W A) = (FreeMonoid.ofList s₀, FreeMonoid.ofList s₀) *
      (FreeMonoid.of b, FreeMonoid.of a) * (FreeMonoid.ofList u₁, FreeMonoid.ofList s₁) := by
    refine Prod.ext ?_ ?_ <;> apply FreeMonoid.toList.injective <;>
      simp [FreeMonoid.toList_mul, hs, hu]
  rw [R_mul_L, hsplit, ofPair_mul, ofPair_mul, mul_assoc, mul_assoc]
  refine mul_le_mul' (dg_le_sig_kstar _) (mul_le_mul' ?_ le_rfl)
  have : ofPair ((FreeMonoid.of b, FreeMonoid.of a) : W A) = of (Sum.inl b) * of (Sum.inr a) := by
    simp [ofPair]
  rw [this]
  exact mismatch_le_sigNe hab

/-- Lemma 33 in the paper's form: `s_r u_l Σ̈∗ ≤ Σ∗ Σ^≠ Σ̈∗`. -/
theorem lemma33' (s u : FreeMonoid A) (h₁ : ¬ s.toList <+: u.toList)
    (h₂ : ¬ u.toList <+: s.toList) :
    R s * L u * sigAll∗ ≤ sig∗ * (sigNe * (sigAll : TD A)∗) := by
  obtain ⟨r, hr⟩ := lemma33 s u h₁ h₂
  exact (hr _).trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl (ofPair_mul_kstar_le r)))

/-- `L` is prefix-free (Definition 32). -/
def PrefixFree (L : Set (FreeMonoid A)) : Prop :=
  ∀ u ∈ L, ∀ v ∈ L, u.toList <+: v.toList → u = v

/-- **Lemma 34**, with an explicit residue: if the automaton of `e` has its states below `b`,
then `ρ = Σ̈∗ b` works. -/
theorem lemma34_le {L : Set (FreeMonoid A)} (hpf : PrefixFree L) {e b : TD A}
    (hl : ∀ s, SetSemiring.Mem s (pl e) → s.1 ∈ L) (hr : ∀ s, SetSemiring.Mem s (pl e) → s.2 ∈ L)
    (hfs : FiniteStateLe e b) (hbo : BoundedOutput e) :
    ∃ h : Rel L e, h.ResidBy (sigAll∗ * b) := by
  obtain ⟨S, hS, heS, hρe⟩ := hfs
  obtain ⟨k₀, hk₀⟩ := hbo
  obtain ⟨k, hk, hexp⟩ := hS.lemma31 heS hk₀
  have hfin := hk.next_finite
  let ρe : TD A := b
  let ρ : TD A := sigAll∗ * ρe
  have herr : ∀ (r : W A) (Z : TD A), Z ≤ ρe → ofPair r * Z ≤ ρ :=
    fun r Z hZ => mul_le_mul' (ofPair_le_sigAll_kstar r) hZ
  -- The singleton case.
  have single : ∀ s ∈ L, R s * e ≤ dg s * rtS (hfin {s}).toFinset + err ρ := by
    intro s hsL
    set n := s.length
    obtain ⟨B, T, es, hB, hT, hes, heq⟩ := hexp ((k + 1) * (n + 1) + 1)
    have hTe : ∑ t ∈ T, ofPair t * es t ≤ e := by
      conv_rhs => rw [heq]
      exact le_add_left le_rfl
    have hdiv : ∀ u ∈ L, s ≠ u → ¬ s.toList <+: u.toList ∧ ¬ u.toList <+: s.toList :=
      fun u hu hsu => ⟨fun h => hsu (hpf s hsL u hu h), fun h => hsu (hpf u hu s hsL h).symm⟩
    conv_lhs => rw [heq]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    refine add_le (sum_le_of_forall _ _ fun t htB => ?_)
      (sum_le_of_forall _ _ fun t htT => le_add_left ?_)
    · -- Short strings: steps (4) and (5).
      have htmem := (ofPair_le_iff_mem t e).1 ((hB t).1 htB).1
      by_cases hts : t.1 = s
      · refine le_add_right ?_
        have : R s * ofPair t = dg s * R t.2 := by
          rw [ofPair, ← mul_assoc, R_mul_L, hts, dg, R_eq_ofPair, ← ofPair_mul]
        rw [this]
        refine mul_le_mul' le_rfl (le_sum_of_mem _ ?_)
        rw [Set.Finite.mem_toFinset]
        exact ⟨s, by simp, by rw [← hts]; exact htmem⟩
      · refine le_add_left ?_
        obtain ⟨d₁, d₂⟩ := hdiv t.1 (hl t htmem) (Ne.symm hts)
        obtain ⟨r, hr'⟩ := lemma33 s t.1 d₁ d₂
        rw [ofPair, ← mul_assoc]
        refine (hr' _).trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_))
        rw [R_eq_ofPair, ← ofPair_mul, ← mul_one (ofPair _)]
        exact herr _ _ (hρe 1 hS.one_mem)
    · -- Long strings: step (6).
      by_cases h0 : es t = 0
      · rw [h0, mul_zero, mul_zero, ← add_eq_right_iff_le, zero_add]
      obtain ⟨w, hw⟩ := exists_ofPair_le _ h0
      have htw : SetSemiring.Mem (t * w) (pl e) := by
        rw [← ofPair_le_iff_mem, ofPair_mul]
        exact (mul_le_mul' le_rfl hw).trans
          ((le_sum_of_mem (fun t => ofPair t * es t) htT).trans hTe)
      obtain ⟨hsize, hbound⟩ := hT t htT
      have hlong : n < t.1.length := by
        by_contra hle
        push Not at hle
        have h1 : (t.1.length + 1) * k ≤ (n + 1) * k := Nat.mul_le_mul_right _ (by omega)
        have h2 : (k + 1) * (n + 1) = (n + 1) * k + n + 1 := by ring
        unfold size at hsize
        omega
      have hwL := hl _ htw
      have d₂ : ¬ t.1.toList <+: s.toList := fun h => by
        have := h.length_le
        have e1 : t.1.toList.length = t.1.length := rfl
        have e2 : s.toList.length = n := rfl
        omega
      have d₁ : ¬ s.toList <+: t.1.toList := fun h => by
        have hpre : s.toList <+: (t * w).1.toList := by
          simp only [Prod.fst_mul, FreeMonoid.toList_mul]; exact h.trans (List.prefix_append _ _)
        have heq' := hpf s hsL _ hwL hpre
        have : (t * w).1.length = s.length := by rw [heq']
        simp only [Prod.fst_mul, FreeMonoid.length_mul] at this
        omega
      obtain ⟨r, hr'⟩ := lemma33 s t.1 d₁ d₂
      rw [ofPair, mul_assoc, ← mul_assoc (R s)]
      refine (hr' _).trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_))
      rw [R_eq_ofPair, ← mul_assoc, ← ofPair_mul]
      exact herr _ _ (hρe _ (hes t))
  have key : ∀ Λ : Finset (FreeMonoid A), ↑Λ ⊆ L →
      rtS Λ * e ≤ dgS Λ * rtS (hfin Λ).toFinset + err ρ := by
    intro Λ hΛ
    rw [rtS, Finset.sum_mul]
    refine sum_le_of_forall _ _ fun u hu => (single u (hΛ hu)).trans (add_le_add ?_ le_rfl)
    refine mul_le_mul' (le_sum_of_mem dg hu) (rtS_mono fun v hv => ?_)
    rw [Set.Finite.mem_toFinset] at hv ⊢
    obtain ⟨u', hu', huv⟩ := hv
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hu'
    subst hu'
    exact ⟨u', hu, huv⟩
  exact ⟨⟨hl, hr, hfin, ρ, key⟩, key⟩

/-- **Lemma 34.** -/
theorem lemma34 {L : Set (FreeMonoid A)} (hpf : PrefixFree L) {e : TD A}
    (hl : ∀ s, SetSemiring.Mem s (pl e) → s.1 ∈ L) (hr : ∀ s, SetSemiring.Mem s (pl e) → s.2 ∈ L)
    (hfs : FiniteState e) (hbo : BoundedOutput e) : Rel L e := by
  obtain ⟨b, hb⟩ := (finiteState_iff e).1 hfs
  exact (lemma34_le hpf hl hr hb hbo).1

end TD

end DiagonaLean.KAComm
