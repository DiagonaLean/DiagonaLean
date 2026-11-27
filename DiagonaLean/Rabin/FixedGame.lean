/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Computability.PartrecCode
import Mathlib.Order.Interval.Finset.Nat
import DiagonaLean.Rabin.Basic

@[expose] public section

/-! # Rabin's fixed game

For the primitive recursive rule `rabinFunction`, Player II has a winning strategy, but every
computable reply function can be defeated (`rabin_game`).

## References

* [M. O. Rabin, *Effective computability of winning strategies*][Rabin1957]
-/

namespace DiagonaLean.Rabin

open Nat.Partrec

/-- Program number `e` is challenged on this opening. Spacing the openings leaves gaps. -/
private def opening (e : ℕ) : ℕ := 2 * e + 2

/-- On the final move `(e, t)`, `rabinFunction` runs reply program `e` on its opening for `t`
steps. A successful simulation gives Player I the sum needed to defeat that reply. -/
def rabinFunction (k : ℕ) : ℕ :=
  let (e, t) := k.unpair
  ((Code.evaln t (Denumerable.ofNat Code e) (opening e)).map (opening e + ·)).getD 0

/-- The function used to score a completed play is primitive recursive. -/
theorem rabinFunction_primrec : Primrec rabinFunction := by
  have h : Primrec fun k : ℕ =>
      Code.evaln k.unpair.2 (Denumerable.ofNat Code k.unpair.1) (opening k.unpair.1) := by
    apply Code.primrec_evaln.comp
      (g := fun k : ℕ => ((k.unpair.2, Denumerable.ofNat Code k.unpair.1), opening k.unpair.1))
    unfold opening
    fun_prop
  unfold rabinFunction opening at *
  fun_prop (disch := assumption)

/-- Every computable reply can be defeated at its own program's opening. -/
theorem exists_winning_play_of_computable {s : ℕ → ℕ} (hs : Computable s) :
    ∃ i k, PlayerIWins rabinFunction i (s i) k := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hs.partrec)
  let e := Encodable.encode c
  have hm : s (opening e) ∈ c.eval (opening e) := by
    rw [hc]
    exact Part.mem_some _
  obtain ⟨t, ht⟩ := Code.evaln_complete.1 hm
  refine ⟨opening e, Nat.pair e t, ?_⟩
  change Code.evaln t c (opening e) = some (s (opening e)) at ht
  simp only [PlayerIWins, rabinFunction, Nat.unpair_pair]
  rw [show Denumerable.ofNat Code e = c from Denumerable.ofNat_encode c, ht]
  rfl

/-- Above every opening there is a number outside the range of the payoff function. -/
private theorem exists_gap (i : ℕ) : ∃ n, i ≤ n ∧ ∀ k, rabinFunction k ≠ n := by
  classical
  let run (e : ℕ) := (Denumerable.ofNat Code e).eval (opening e)
  let target (e : ℕ) := opening e + (run e).getOrElse 0
  -- Only programs 0 through i can hit the interval [i + 1, 2*i + 2].
  -- Each contributes at most one nonzero value, and the interval has i + 2 elements.
  have hcard : ((Finset.range (i + 1)).image target).card ≤ i + 1 := by
    simpa using (Finset.card_image_le (s := Finset.range (i + 1)) (f := target))
  have hlt : ((Finset.range (i + 1)).image target).card <
      (Finset.Icc (i + 1) (2 * i + 2)).card := by
    rw [Nat.card_Icc]
    omega
  obtain ⟨n, hn, hmiss⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  refine ⟨n, by omega, fun k heq => ?_⟩
  obtain ⟨e, t, rfl⟩ : ∃ e t, Nat.pair e t = k := ⟨_, _, Nat.pair_unpair k⟩
  simp only [rabinFunction, Nat.unpair_pair] at heq
  cases h : Code.evaln t (Denumerable.ofNat Code e) (opening e) with
  | none =>
    simp [h] at heq
    omega
  | some v =>
    have hv : v ∈ run e := Code.evaln_sound h
    have hn' : opening e + v = n := by simpa [h] using heq
    apply hmiss
    refine Finset.mem_image.mpr ⟨e, Finset.mem_range.mpr ?_, ?_⟩
    · unfold opening at hn'
      omega
    · simpa [target, Part.getOrElse_of_dom _ (Part.dom_iff_mem.mpr ⟨_, hv⟩),
        Part.get_eq_of_mem hv] using hn'

/-- Player II can choose a reply taking the sum to a gap in the range. -/
theorem exists_winningII : ∃ s, WinningII rabinFunction s := by
  choose n hle hgap using exists_gap
  exact ⟨fun i => n i - i, fun i k => by
    simpa [PlayerIWins, Nat.add_sub_of_le (hle i)] using hgap i k⟩

/-- **Rabin's theorem.** The rule `rabinFunction` is primitive recursive, Player II has a winning
strategy for it, and no computable strategy wins for Player II. -/
theorem rabin_game : Primrec rabinFunction ∧ (∃ s, WinningII rabinFunction s) ∧
    ¬ ∃ s, Computable s ∧ WinningII rabinFunction s := by
  refine ⟨rabinFunction_primrec, exists_winningII, ?_⟩
  rintro ⟨s, hs, hw⟩
  obtain ⟨i, k, h⟩ := exists_winning_play_of_computable hs
  exact hw i k h

end DiagonaLean.Rabin
