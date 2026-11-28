/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Rabin.Basic
import DiagonaLean.Synthetic.HaltReduction
import DiagonaLean.Synthetic.Tactics.ReductionPath

@[expose] public section

/-! # Halting reduces to winner determination in Rabin's game

The payoff program `haltToRabin p` returns its argument once the simulated machine has halted.
From that point on, Player I can match every reply. If the simulation never halts, Player II
wins by playing 1 (`winningII_of_not_halts`). So `haltToRabin` many-one reduces the halting
problem to winner determination (`halt_reducesto_rabin_spec`); `SynthHardness.lean` states it as
`Rabin.synthFromHalt`.

## References

* [M. O. Rabin, *Effective computability of winning strategies*][Rabin1957]
-/

namespace DiagonaLean.Rabin.Reduction

open DiagonaLean.Foundations.Computability DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions

/-- The payoff program of a machine and an input: it returns its argument `k` when the machine
halts within `k` steps, and zero otherwise. -/
def haltToRabin (p : EncodableTM Bool × List Bool) : PayoffCode := .bounded (dataOf p)

/-- A bounded simulation payoff gives Player I a winning strategy exactly when its test succeeds
at some bound. -/
theorem winner_bounded_iff (d : List (ℕ × ℕ) × SC) :
    DecisionProblem (.bounded d) ↔ ∃ t, Test d t := by
  constructor
  · rintro ⟨i, last, h⟩
    refine ⟨last 1, ?_⟩
    by_contra hn
    have hwin := h 1
    simp [PlayerIWins, PayoffCode.eval, hn] at hwin
  · rintro ⟨t, ht⟩
    refine ⟨t, fun j => t + j, fun j => ?_⟩
    have h : Test d (t + j) := by
      unfold Test
      rw [iterate_sstep_of_le ht (Nat.le_add_right t j)]
      exact ht
    simp [PlayerIWins, PayoffCode.eval, h]

/-- A machine halts on an input iff Player I wins the game of `haltToRabin`. -/
theorem halt_reducesto_rabin_spec : HaltProblem ⪯_s[haltToRabin] DecisionProblem :=
  fun p => (halt_iff_test p).trans (winner_bounded_iff (dataOf p)).symm

/-- If the input machine runs forever, the constant reply 1 wins for Player II. -/
theorem winningII_of_not_halts {p : EncodableTM Bool × List Bool} (hp : ¬ HaltProblem p) :
    WinningII (haltToRabin p).eval (fun _ => 1) := by
  intro i k
  have hk : ¬ Test (dataOf p) k := fun h => hp ((halt_iff_test p).2 ⟨k, h⟩)
  simp [PlayerIWins, haltToRabin, PayoffCode.eval, hk]

/-- Winner determination in Rabin's game is displayed as "Rabin game winner". -/
instance : Synthetic.ReductionChain.ProblemName DecisionProblem :=
  ⟨"Rabin game winner"⟩

end DiagonaLean.Rabin.Reduction
