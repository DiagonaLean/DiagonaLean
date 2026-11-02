/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.SingleStep

@[expose] public section

/-! # Completeness along a terminating trace (proof of Theorem 16, machine-independent part)

The proof of Theorem 16 uses only two facts about the machine's transition term `R_M`: it is a
representable relation (Lemma 35 via Lemma 34), and it is deterministic, so from the initial
configuration `Nextⁱ(s) = {sᵢ}` until the halting configuration, which has no successor. This file
proves the resulting bound for any such term:

`(s₀)_r e∗ ≤ Σ∗ {s₀, …, sₙ}_r + Σ∗ Σ^≠ ρ`, with `ρ` depending only on `e`.

The machine-specific remainder of Theorem 16 is to show `{s₀, …, sₙ} ≤ C_M + c₁`.

## Main statements

* `TD.Rel.complete_of_trace`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], proof of Theorem 16
-/

open scoped Computability

namespace DiagonaLean.KAComm

namespace TD

open FreePreKA Classical

variable {A : Type*} [Fintype A] [DecidableEq A]

namespace Rel

variable {L : Set (FreeMonoid A)} {e : TD A} (h : Rel L e)
include h

theorem mem_next {Λ : Finset (FreeMonoid A)} {v : FreeMonoid A} :
    v ∈ h.next Λ ↔ ∃ u ∈ Λ, SetSemiring.Mem (u, v) (pl e) := by
  rw [next, Set.Finite.mem_toFinset]; rfl

theorem next_empty : h.next ∅ = ∅ := by
  ext v; simp [mem_next]

theorem iter_empty : ∀ j, h.iter j ∅ = ∅
  | 0 => rfl
  | j + 1 => by simp only [iter, next_empty, iter_empty j]

theorem mem_below : ∀ (j : ℕ) (Λ : Finset (FreeMonoid A)) (v : FreeMonoid A),
    v ∈ h.below j Λ → ∃ i < j, v ∈ h.iter i Λ
  | 0, _, _, hv => absurd hv (Finset.notMem_empty _)
  | j + 1, Λ, v, hv => by
    rcases Finset.mem_union.1 hv with hv | hv
    · exact ⟨0, Nat.succ_pos j, hv⟩
    · obtain ⟨i, hi, hv⟩ := mem_below j _ v hv
      exact ⟨i + 1, by omega, hv⟩

/-- **Completeness along a trace.** There is a residue `ρ` (depending only on `e`) such that
for every trace `s₀ → s₁ → ⋯ → sₙ` in `L` along which `e` is deterministic, and whose last
element has no successor, `(s₀)_r e∗ ≤ Σ∗ {s₀, …, sₙ}_r + Σ∗ Σ^≠ ρ`. -/
theorem complete_of_trace : ∃ ρ : TD A, ∀ (n : ℕ) (s : ℕ → FreeMonoid A),
    s 0 ∈ L →
    (∀ i < n, ∀ v, SetSemiring.Mem (s i, v) (pl e) ↔ v = s (i + 1)) →
    (∀ v, ¬ SetSemiring.Mem (s n, v) (pl e)) →
    R (s 0) * e∗ ≤ sig∗ * rtS ((Finset.range (n + 1)).image s) + err ρ := by
  obtain ⟨ρ, hρ⟩ := h.theorem22
  refine ⟨ρ, fun n s hs0 hstep hlast => ?_⟩
  have hnext : ∀ i < n, h.next {s i} = {s (i + 1)} := fun i hi => by
    ext v; simp [mem_next, hstep i hi]
  have hnextn : h.next {s n} = ∅ := by
    ext v; simp [mem_next, hlast]
  have hiter : ∀ i ≤ n, h.iter i {s 0} = {s i} := by
    intro i
    induction i with
    | zero => intro; rfl
    | succ i ih =>
      intro hi
      have key : ∀ j (m : ℕ), m + j ≤ n → h.iter j {s m} = {s (m + j)} := by
        intro j
        induction j with
        | zero => intro m _; rfl
        | succ j ihj =>
          intro m hm
          simp only [iter]
          rw [hnext m (by omega), ihj (m + 1) (by omega)]
          congr 2; omega
      simpa using key (i + 1) 0 (by omega)
  have hend : h.iter (n + 1) {s 0} = ∅ := by
    have key : ∀ j (m : ℕ), m + j = n → h.iter (j + 1) {s m} = ∅ := by
      intro j
      induction j with
      | zero => intro m hm; subst hm; simpa only [iter, Nat.add_zero] using hnextn
      | succ j ihj =>
        intro m hm
        simp only [iter] at ihj ⊢
        rw [hnext m (by omega)]
        exact ihj (m + 1) (by omega)
    exact key n 0 (by omega)
  have hb := hρ (n + 1) {s 0} (by simpa using hs0) hend
  rw [rtS, Finset.sum_singleton] at hb
  refine hb.trans (add_le_add (mul_le_mul' le_rfl (rtS_mono fun v hv => ?_)) le_rfl)
  obtain ⟨i, hi, hv⟩ := h.mem_below _ _ v hv
  rw [hiter i (by omega), Finset.mem_singleton] at hv
  exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, hv.symm⟩

end Rel

end TD

end DiagonaLean.KAComm
