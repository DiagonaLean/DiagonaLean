/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.PreKleeneNotKleene
import DiagonaLean.KleeneAlgebra.Free
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # Theorem 6 and Corollary 7 fail as stated

Theorem 6 of the paper says that a term `e ∈ T X` with finite language equals the sum of the
strings in `l(e)`. Corollary 7 says that `l` is injective on such terms. Both fail at `e = 1∗`:
its language is `{ε}`, but `1∗ ≠ 1` in `T X`, because the morphism into Example 1 sends `1∗` to
`⊤` and `1` to the unit. The paper notes as much in §5.1 ("the closest we can get to an expansion
for `1∗` is `1∗ = 1 + 1∗`"), but the proof of Theorem 6, by induction on `e`, misses the star
case.

The counterexample works for every alphabet and every commutation relation, `X = Empty`
included.

## Main statements

* `FreePreKA.one_kstar_ne_one`: `(1 : T X)∗ ≠ 1`.
* `FreePreKA.lang_one_kstar`: `l(1∗) = {ε}`.
* `FreePreKA.not_forall_finite_lang_eq_sum`: the negation of Theorem 6.
* `FreePreKA.not_lang_injective_on_finite`: the negation of Corollary 7.
* `FreePreKA.not_forall_finite_lang_mul_kstar_le`: the negation of Theorem 9 (same counterexample).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 6,
  Corollary 7, Example 1.
-/

open scoped Computability

namespace DiagonaLean.KAComm

namespace FreePreKA

variable {X : Type*}

/-- `1∗ ≠ 1` in the free pre-Kleene algebra, for any alphabet and commutation relation. -/
theorem one_kstar_ne_one {C : X → X → Prop} : (1 : FreePreKA X C)∗ ≠ 1 := by
  intro h
  have := congrArg (lift (fun _ => (0 : NatBotTop)) (fun _ _ _ => rfl)) h
  rw [lift_kstar, lift_one] at this
  exact NatBotTop.one_kstar_ne this

/-- The string `x₁ ⋯ xₙ` as a term. -/
def ofWord {C : X → X → Prop} (w : List X) : FreePreKA X C := (w.map of).prod

/-- The language of `1∗` is `{ε}`. -/
theorem lang_one_kstar : lang (1 : FreePreKA X (· = ·))∗ = {[]} := by
  rw [lang_kstar, lang_one, kstar_one]; rfl

/-- `e` has a finite language, listed by the finite set `S`. -/
def LangIs (e : FreePreKA X (· = ·)) (S : Finset (List X)) : Prop := ∀ s, s ∈ lang e ↔ s ∈ S

theorem langIs_one_kstar : LangIs (1 : FreePreKA X (· = ·))∗ {[]} := by
  intro s; rw [lang_one_kstar, Finset.mem_singleton]; rfl

theorem langIs_one : LangIs (1 : FreePreKA X (· = ·)) {[]} := by
  intro s; rw [lang_one, Finset.mem_singleton]; rfl

/-- **Theorem 6 is false.** It is not true that every term with a finite language equals the sum
of the strings in its language. -/
theorem not_forall_finite_lang_eq_sum :
    ¬ ∀ (e : FreePreKA X (· = ·)) (S : Finset (List X)), LangIs e S →
        e = ∑ s ∈ S, ofWord s := by
  intro H
  have := H _ _ (langIs_one_kstar (X := X))
  rw [Finset.sum_singleton] at this
  exact one_kstar_ne_one this

/-- **Corollary 7 is false.** The language interpretation is not injective on terms with finite
languages. -/
theorem not_lang_injective_on_finite :
    ¬ ∀ (e₁ e₂ : FreePreKA X (· = ·)) (S : Finset (List X)), LangIs e₁ S → LangIs e₂ S →
        e₁ = e₂ :=
  fun H => one_kstar_ne_one (H _ _ _ (langIs_one_kstar (X := X)) langIs_one)

/-- **Theorem 9 is false.** For finite `X`, it is not true that every term `e` with a finite
language satisfies `e X∗ ≤ X∗`. Counterexample: `e = 1∗`, sent to Example 1 with every
generator mapped to `⊥`. Then `X∗ ↦ 1` and `1∗ X∗ ↦ ⊤`. -/
theorem not_forall_finite_lang_mul_kstar_le [Fintype X] :
    ¬ ∀ (e : FreePreKA X (· = ·)) (S : Finset (List X)), LangIs e S →
        e * (∑ x, of x)∗ ≤ (∑ x, of x)∗ := by
  intro H
  have h := lift_mono (fun _ : X => (0 : NatBotTop)) (fun _ _ _ => rfl)
    (H _ _ (langIs_one_kstar (X := X)))
  rw [lift_mul, lift_kstar, lift_kstar, lift_one, lift_sum] at h
  simp only [lift_of, Finset.sum_const_zero] at h
  exact NatBotTop.top_not_le_one h

end FreePreKA

end DiagonaLean.KAComm
