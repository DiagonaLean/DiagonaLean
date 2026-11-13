/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.Copy
import DiagonaLean.Foundations.KleeneAlgebra.SingleStep

@[expose] public section

/-! # Soundness along a trace

The machine-independent part of the proof of Theorem 15. If `s₀ →ₑ s₁ →ₑ ⋯ →ₑ sₙ`, the string
`p = (s₀ ⋯ sₙ₋₁, s₀ ⋯ sₙ)` lies in `l((s₀)_r e∗)`. Its left component is a prefix of its right
one, so `p` avoids `l(Σ∗ Σ^≠ Σ̈∗)`. Hence a language inequality `(s₀)_r e∗ ≤ Σ∗ X + Σ∗ Σ^≠ Σ̈∗`,
with `X` purely right, forces `(sₙ)_r ∈ l(X)`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], proof of Theorem 15
-/

open scoped Computability

namespace DiagonaLean.Foundations.KleeneAlgebra

namespace TD

open FreePreKA

variable {A : Type*} [Fintype A]

/-- `l(Σ∗)` is the set of pairs `(u, u)`. -/
theorem mem_sig_kstar (s : W A) : SetSemiring.Mem s (pl (sig : TD A)∗) ↔ ∃ u, s = (u, u) := by
  change SetSemiring.Mem s (pl (cpf (id : A → A))∗) ↔ _
  rw [mem_cpf_star]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨u, rfl⟩; exact ⟨u.toList, by simp⟩

/-- Every string is in `l(Σ̈∗)`. -/
theorem mem_sigAll_kstar (s : W A) : SetSemiring.Mem s (pl (sigAll : TD A)∗) :=
  (ofPair_le_iff_mem _ _).1 (ofPair_le_sigAll_kstar s)

/-- Every language is contained in `l(Σ̈∗)`. -/
theorem pl_le_sigAll_kstar (e : TD A) : pl e ≤ pl (sigAll : TD A)∗ :=
  (SetSemiring.le_iff _ _).2 fun s _ => mem_sigAll_kstar s

variable [DecidableEq A]

/-- `l(Σ^≠)` is the set of pairs `(a, b)` of letters with `a ≠ b`. -/
theorem mem_sigNe (s : W A) :
    SetSemiring.Mem s (pl (sigNe : TD A)) ↔
      ∃ a b : A, a ≠ b ∧ s = (FreeMonoid.of a, FreeMonoid.of b) := by
  have hab : ∀ a b : A, (of (Sum.inl a) * of (Sum.inr b) : TD A) =
      ofPair (FreeMonoid.of a, FreeMonoid.of b) := fun a b => by simp [ofPair]
  simp only [sigNe, mem_pl_sum, Finset.mem_univ, true_and, Finset.mem_filter, hab, mem_ofPair]
  constructor
  · rintro ⟨a, b, hb, rfl⟩; exact ⟨a, b, Ne.symm hb, rfl⟩
  · rintro ⟨a, b, hb, rfl⟩; exact ⟨a, b, Ne.symm hb, rfl⟩

/-- `l(Σ∗ Σ^≠ Σ̈∗)` contains no `(x, x y)`. -/
theorem not_mem_err_prefix (x y : FreeMonoid A) :
    ¬ SetSemiring.Mem (x, x * y) (pl (err (sigAll : TD A)∗)) := by
  intro h
  simp only [err, pl_mul, SetSemiring.mem_mul] at h
  obtain ⟨_, hu, _, ⟨_, hab, z, -, rfl⟩, he⟩ := h
  obtain ⟨u, rfl⟩ := (mem_sig_kstar _).1 hu
  obtain ⟨a, b, hne, rfl⟩ := (mem_sigNe _).1 hab
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  simp only [Prod.fst_mul, Prod.snd_mul] at h1 h2
  rw [← h1, mul_assoc] at h2
  have h3 := congrArg FreeMonoid.toList (mul_left_cancel h2)
  simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of,
    List.cons_append, List.cons.injEq] at h3
  exact hne h3.1.symm

/-- Prefix products `s₀ ⋯ sₖ₋₁`. -/
def pre (s : ℕ → FreeMonoid A) : ℕ → FreeMonoid A
  | 0 => 1
  | k + 1 => pre s k * s k

omit [Fintype A] [DecidableEq A] in
/-- Along `s₀ →ₑ ⋯ →ₑ sₙ`, for every `k ≤ n`, the string `(s₀ ⋯ sₖ₋₁, s₀ ⋯ sₖ)` is in
`l((s₀)_r e∗)`. -/
theorem mem_trace (e : TD A) (n : ℕ) (s : ℕ → FreeMonoid A)
    (hstep : ∀ i < n, SetSemiring.Mem (s i, s (i + 1)) (pl e)) :
    ∀ k ≤ n, SetSemiring.Mem (pre s k, pre s k * s k) (pl (R (s 0) * e∗)) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [pl_mul, SetSemiring.mem_mul]
    refine ⟨(1, s 0), by rw [pl_R]; rfl, 1, ?_, by simp [pre]⟩
    rw [pl_kstar, SetSemiring.mem_kstar]; exact ⟨[], by simp, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨a, ha, b, hb, hab⟩ := (SetSemiring.mem_mul _ _ _).1
      (by have := ih (by omega); rwa [pl_mul] at this)
    rw [pl_mul, SetSemiring.mem_mul]
    refine ⟨a, ha, b * (s k, s (k + 1)), ?_, ?_⟩
    · rw [pl_kstar, SetSemiring.mem_kstar] at hb ⊢
      obtain ⟨l, hl, rfl⟩ := hb
      refine ⟨l ++ [(s k, s (k + 1))], fun y hy => ?_, by simp⟩
      rcases List.mem_append.1 hy with hy | hy
      · exact hl y hy
      · rw [List.mem_singleton.1 hy]; exact hstep k (by omega)
    · rw [← mul_assoc, hab]
      simp [pre, mul_assoc]

/-- **Soundness along a trace.** If `s₀ →ₑ ⋯ →ₑ sₙ` and the language inequality
`(s₀)_r e∗ ≤ Σ∗ X + Σ∗ Σ^≠ Σ̈∗` holds, with every string of `X` purely right, then
`(sₙ)_r ∈ l(X)`. -/
theorem sound_of_trace (e X : TD A) (hX : ∀ x, SetSemiring.Mem x (pl X) → x.1 = 1)
    (n : ℕ) (s : ℕ → FreeMonoid A)
    (hstep : ∀ i < n, SetSemiring.Mem (s i, s (i + 1)) (pl e))
    (h : pl (R (s 0) * e∗) ≤ pl (sig∗ * X + err (sigAll : TD A)∗)) :
    SetSemiring.Mem (1, s n) (pl X) := by
  have hp := (SetSemiring.le_iff _ _).1 h _ (mem_trace e n s hstep n le_rfl)
  rw [pl_add, SetSemiring.mem_add] at hp
  rcases hp with hp | hp
  · rw [pl_mul, SetSemiring.mem_mul] at hp
    obtain ⟨_, hu, x, hx, he⟩ := hp
    obtain ⟨u, rfl⟩ := (mem_sig_kstar _).1 hu
    have hx1 := hX x hx
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only [Prod.fst_mul, Prod.snd_mul, hx1, mul_one] at h1 h2
    rw [h1] at h2
    have : x = (1, s n) := Prod.ext hx1 (mul_left_cancel h2)
    rwa [this] at hx
  · exact absurd hp (not_mem_err_prefix _ _)

end TD

end DiagonaLean.Foundations.KleeneAlgebra
