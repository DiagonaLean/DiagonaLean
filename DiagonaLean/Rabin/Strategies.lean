/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Computability.RE
import DiagonaLean.Rabin.Basic

@[expose] public section

/-! # Strategies and the range of a Rabin payoff

Player I needs every number above an opening to be attainable. Player II needs a way to
select arbitrarily large missing numbers. A computable enumeration of infinitely many
missing numbers suffices to implement the latter strategy by search. Exactly one player has a
winning strategy (`winningII_iff_not_hasWinningI`).

## References

* [M. O. Rabin, *Effective computability of winning strategies*][Rabin1957]
-/

namespace DiagonaLean.Rabin

/-- Player I wins exactly when the range of the payoff contains a tail of the naturals. -/
theorem hasWinningI_iff_finite_compl (g : ℕ → ℕ) :
    HasWinningI g ↔ (Set.range g)ᶜ.Finite := by
  rw [Set.finite_iff_bddAbove]
  constructor
  · rintro ⟨i, last, hw⟩
    refine ⟨i, fun n hn => ?_⟩
    by_contra! h
    exact hn ⟨last (n - i), (hw (n - i)).trans (by omega)⟩
  · rintro ⟨b, hb⟩
    have h (j : ℕ) : b + 1 + j ∈ Set.range g := by
      by_contra hn
      have := hb (show b + 1 + j ∈ (Set.range g)ᶜ from hn)
      omega
    exact ⟨b + 1, fun j => (h j).choose, fun j => (h j).choose_spec⟩

/-- Player II wins exactly when the range of the payoff misses infinitely many numbers. -/
theorem exists_winningII_iff_infinite_compl (g : ℕ → ℕ) :
    (∃ s, WinningII g s) ↔ (Set.range g)ᶜ.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · rintro ⟨s, hs⟩ a
    refine ⟨a + 1 + s (a + 1), ?_, by omega⟩
    rintro ⟨k, hk⟩
    exact hs (a + 1) k hk
  · intro h
    choose n hn hlt using h
    refine ⟨fun i => n i - i, fun i k hk => hn i ⟨k, ?_⟩⟩
    exact hk.trans (Nat.add_sub_of_le (hlt i).le)

/-- Exactly one of the two players has a winning strategy for any payoff. -/
theorem winningII_iff_not_hasWinningI (g : ℕ → ℕ) :
    (∃ s, WinningII g s) ↔ ¬ HasWinningI g := by
  rw [exists_winningII_iff_infinite_compl, hasWinningI_iff_finite_compl]
  rfl

/-- For computable payoffs, search for a preimage implements I's winning final response. -/
theorem exists_computable_last {g : ℕ → ℕ} (hg : Computable g) (hw : HasWinningI g) :
    ∃ (i : ℕ) (last : ℕ → ℕ), Computable last ∧ ∀ j, PlayerIWins g i j (last j) := by
  obtain ⟨i, last, hi⟩ := hw
  have he (j : ℕ) : ∃ k, g k = i + j := ⟨last j, hi j⟩
  refine ⟨i, _, Computable.find (P := fun j k => g k = i + j) ?_ he, fun j => Nat.find_spec _⟩
  apply Computable.computablePred
  exact Primrec.eq.decide.to_comp.comp (hg.comp Computable.snd) (by fun_prop)

/-- II can play computably exactly when the missing numbers contain an infinite c.e. set,
expressed as the infinite range of a total computable enumeration. -/
theorem computable_winningII_iff_infinite_range (g : ℕ → ℕ) :
    (∃ s, Computable s ∧ WinningII g s) ↔
      ∃ f : ℕ → ℕ, Computable f ∧ (Set.range f).Infinite ∧ Set.range f ⊆ (Set.range g)ᶜ := by
  constructor
  · rintro ⟨s, hs, hw⟩
    refine ⟨fun i => i + s i, ?_, Set.infinite_iff_exists_gt.mpr ?_, ?_⟩
    · fun_prop (disch := assumption)
    · intro a
      exact ⟨_, ⟨a + 1, rfl⟩, by dsimp; omega⟩
    · rintro _ ⟨i, rfl⟩ ⟨k, hk⟩
      exact hw i k hk
  · rintro ⟨f, hf, hi, hgap⟩
    have he (i : ℕ) : ∃ k, i ≤ f k := by
      obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Set.infinite_iff_exists_gt.mp hi i
      exact ⟨k, hk.le⟩
    have hfind : Computable (fun i => Nat.find (he i)) := by
      apply Computable.find (P := fun i k => i ≤ f k) _ he
      apply Computable.computablePred
      exact Primrec.nat_le.decide.to_comp.comp Computable.fst (hf.comp Computable.snd)
    refine ⟨fun i => f (Nat.find (he i)) - i, ?_, fun i k hk => ?_⟩
    · fun_prop (disch := assumption)
    · apply hgap ⟨Nat.find (he i), rfl⟩
      exact ⟨k, hk.trans (Nat.add_sub_of_le (Nat.find_spec (he i)))⟩

end DiagonaLean.Rabin
