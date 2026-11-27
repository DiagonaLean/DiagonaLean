/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Rabin.FixedGame
import DiagonaLean.Foundations.Computability.UndecTransfer

@[expose] public section

/-! # Halting reduces to computable strategy existence when Player II wins

Until a simulated computation halts, the payoff agrees with Rabin's example. After halting
it is zero, so the remaining finite range can be avoided by a constant reply. So no machine
decides whether Player II has a computable winning strategy, even when it only has to answer on
inputs where Player II has some winning strategy (`not_machineDecidable_promised_strategy`).
The statement is a promise problem, which `MachineDecidable` does not express.

## References

* [M. O. Rabin, *Effective computability of winning strategies*][Rabin1957]
-/

namespace DiagonaLean.Rabin.Reduction

open DiagonaLean.Foundations.Computability DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions

/-- The payoff switches permanently to zero once the simulated machine halts. -/
def cutoff (d : List (ℕ × ℕ) × SC) (k : ℕ) : ℕ :=
  if Test d k then 0 else rabinFunction k

/-- Every cutoff game is won by II. A computable strategy exists exactly on halting inputs. -/
theorem cutoff_spec (d : List (ℕ × ℕ) × SC) :
    (∃ s, WinningII (cutoff d) s) ∧
    ((∃ s, Computable s ∧ WinningII (cutoff d) s) ↔ ∃ t, Test d t) := by
  by_cases h : ∃ t, Test d t
  · obtain ⟨t, ht⟩ := h
    let b := (Finset.range t).sup rabinFunction + 1
    have hw : WinningII (cutoff d) (fun _ => b) := by
      intro i k
      change cutoff d k ≠ i + b
      unfold cutoff
      split
      · dsimp [b]; omega
      · rename_i hk
        have hkt : k < t := by
          by_contra! hle
          apply hk
          unfold Test
          rw [iterate_sstep_of_le ht hle]
          exact ht
        have hub := Finset.le_sup (f := rabinFunction) (Finset.mem_range.mpr hkt)
        dsimp [b]; omega
    exact ⟨⟨_, hw⟩, fun _ => ⟨t, ht⟩, fun _ => ⟨_, Computable.const b, hw⟩⟩
  · have heq : cutoff d = rabinFunction := by
      funext k
      simp [cutoff, show ¬ Test d k from fun hk => h ⟨k, hk⟩]
    rw [heq]
    exact ⟨rabin_game.2.1, iff_of_false rabin_game.2.2 h⟩

/-- `cutoffCode base d` is a payoff program for `cutoff d`, built from a program `base` for
Rabin's payoff by a fixed primitive recursion template.
The recursion returns its base at zero and zero at every successor. -/
def cutoffCode (base : PayoffCode) (d : List (ℕ × ℕ) × SC) : PayoffCode :=
  .comp (.prec base .zero) (.pair (.pair .left .right) (.bounded d))

/-- `cutoffCode base` is primitive recursive. -/
theorem cutoffCode_primrec (base : PayoffCode) : Primrec (cutoffCode base) := by
  unfold cutoffCode
  fun_prop

/-- The compiled code implements the cutoff, including the ambiguous bounded output at zero. -/
theorem eval_cutoffCode {base : PayoffCode} (hb : base.eval = rabinFunction)
    (d : List (ℕ × ℕ) × SC) : (cutoffCode base d).eval = cutoff d := by
  funext k
  simp only [cutoffCode, PayoffCode.eval, Nat.pair_unpair, Nat.unpaired, Nat.unpair_pair, hb]
  by_cases ht : Test d k
  · simp only [ht, ite_true, cutoff]
    cases k with
    | zero => simp [rabinFunction, Nat.unpair_zero, Nat.Partrec.Code.evaln]
    | succ k => rfl
  · simp [cutoff, ht]

/-- **No Turing machine decides whether Player II has a computable winning strategy**, even if it
only has to answer on payoff programs for which Player II has a winning strategy. -/
theorem not_machineDecidable_promised_strategy {enc : PayoffCode → List Bool}
    (henc : Computable enc) :
    ¬ ∃ D : Cslib.Turing.SingleTapeTM Bool, ∀ c : PayoffCode, (∃ s, WinningII c.eval s) →
      ((∃ s, Computable s ∧ WinningII c.eval s) → D.Outputs (enc c) [true]) ∧
      ((¬ ∃ s, Computable s ∧ WinningII c.eval s) → D.Outputs (enc c) [false]) := by
  rintro ⟨D, hD⟩
  obtain ⟨base, hb⟩ := exists_payoffCode rabinFunction_primrec
  have hn : ¬ ComputablePred (fun d => ∃ t, Test d t) :=
    not_computablePred_of_selfHalt dataC_prim.to_comp (fun _ => selfHalt_iff_test)
  apply not_machineDecidable_of_not_computablePred
    (henc.comp (cutoffCode_primrec base).to_comp) hn
  refine ⟨D, fun d => ?_⟩
  obtain ⟨hw, hiff⟩ := cutoff_spec d
  rw [← eval_cutoffCode hb d] at hw hiff
  simpa only [hiff] using hD (cutoffCode base d) hw

end DiagonaLean.Rabin.Reduction
