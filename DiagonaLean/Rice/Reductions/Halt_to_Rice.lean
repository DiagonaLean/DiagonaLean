/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kshitij Salunke, Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Rice.Basic
import DiagonaLean.Foundations.Computability.OutputSearch

@[expose] public section

/-! # `HaltProblem ⪯_s` Rice's problem

`wait n x` searches for a step at which the machine whose data has code `n` has halted, and then
returns `x`. It is partial recursive (`wait_part`), so some program `w` computes it on `⟪n, x⟫`
(`IsWaiter`, `exists_isWaiter`).

`reduction w cT` sends a `HaltProblem` instance `p` to the program that waits for `p` to halt and
then runs `cT`. If `p` halts, it computes `cT.eval` (`eval_reduction_of_halts`); if not, it computes
the nowhere-defined function (`eval_reduction_of_not_halts`). So if `cT.eval ∈ C` and the
nowhere-defined function is not in `C`, then `p` halts iff the program is in `RiceProblem C`
(`halt_reducesto_rice_spec`).

## References

* H. G. Rice, *Classes of recursively enumerable sets and their decision problems* (1953)
-/

namespace DiagonaLean.Rice.Reduction

open Nat.Partrec DiagonaLean.Foundations.Computability DiagonaLean.Halt DiagonaLean.Halt.Encoding

/-- `wait n x` searches for a step at which the machine whose data has code `n` has halted, and
then returns `x`. -/
def wait (n x : ℕ) : Part ℕ :=
  (Nat.rfind ((fun k => decide (Test (Denumerable.ofNat (List (ℕ × ℕ) × SC) n) k) : ℕ → Bool) :
    ℕ →. Bool)).map fun _ => x

/-- `wait` is partial recursive. -/
theorem wait_part : Partrec₂ wait := by
  have ht : Computable₂ fun (q : ℕ × ℕ) (k : ℕ) =>
      decide (Test (Denumerable.ofNat (List (ℕ × ℕ) × SC) q.1) k) :=
    (test_prim.decide.comp
      (((Primrec.ofNat _).comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).to_comp
  exact (Partrec.rfind ht.partrec₂).map (Computable.snd.comp Computable.fst).to₂

/-- `w` is a program that, on `⟪n, x⟫`, waits for the machine whose data has code `n` to halt and
then returns `x`. -/
def IsWaiter (w : Code) : Prop := ∀ n x, w.eval (Nat.pair n x) = wait n x

/-- A waiter program exists. -/
theorem exists_isWaiter : ∃ w, IsWaiter w := by
  obtain ⟨w, hw⟩ := Code.exists_code.1 (Partrec₂.unpaired'.2 wait_part)
  exact ⟨w, fun n x => by rw [hw, Nat.unpaired, Nat.unpair_pair]⟩

/-- **The reduction.** The program that waits for `p` to halt and then runs `cT`. -/
def reduction (w cT : Code) (p : EncodableTM Bool × List Bool) : Code :=
  Code.comp cT (Code.curry w (Encodable.encode (dataOf p)))

/-- The program `reduction w cT p` runs `cT` on `x` after waiting for `p` to halt. -/
theorem eval_reduction {w : Code} (hw : IsWaiter w) (cT : Code)
    (p : EncodableTM Bool × List Bool) (x : ℕ) :
    (reduction w cT p).eval x =
      Nat.rfind ((fun k => decide (Test (dataOf p) k) : ℕ → Bool) : ℕ →. Bool) >>=
        fun _ => cT.eval x := by
  show (Code.curry w _).eval x >>= cT.eval = _
  rw [Code.eval_curry, hw, wait, Denumerable.ofNat_encode]
  exact Part.bind_map _ _ _

/-- If `p` halts, then `reduction w cT p` computes the same function as `cT`. -/
theorem eval_reduction_of_halts {w : Code} (hw : IsWaiter w) (cT : Code)
    {p : EncodableTM Bool × List Bool} (h : HaltProblem p) : (reduction w cT p).eval = cT.eval := by
  funext x
  obtain ⟨k, hk⟩ := (halt_iff_test p).1 h
  obtain ⟨n, hn, -⟩ := Nat.rfind_min' (p := fun k => decide (Test (dataOf p) k)) (by simpa using hk)
  rw [eval_reduction hw, Part.eq_some_iff.2 hn]
  simp

/-- If `p` does not halt, then `reduction w cT p` computes the nowhere-defined function. -/
theorem eval_reduction_of_not_halts {w : Code} (hw : IsWaiter w) (cT : Code)
    {p : EncodableTM Bool × List Bool} (h : ¬ HaltProblem p) :
    (reduction w cT p).eval = fun _ => Part.none := by
  funext x
  have hd : ¬ (Nat.rfind ((fun k => decide (Test (dataOf p) k) : ℕ → Bool) : ℕ →. Bool)).Dom := by
    rintro ⟨n, hn, -⟩
    exact h ((halt_iff_test p).2 ⟨n, by simpa using hn⟩)
  rw [eval_reduction hw, Part.eq_none_iff'.2 hd]
  simp

/-- If `cT` computes a function in `C` and the nowhere-defined function is not in `C`, then
`reduction w cT` reduces `HaltProblem` to `RiceProblem C`. -/
theorem halt_reducesto_rice_spec {C : Set (ℕ →. ℕ)} {w cT : Code} (hw : IsWaiter w)
    (hT : cT.eval ∈ C) (hbot : (fun _ => Part.none : ℕ →. ℕ) ∉ C) :
    HaltProblem ⪯_s[reduction w cT] RiceProblem C := fun p => by
  by_cases h : HaltProblem p
  · refine iff_of_true h ?_
    show (reduction w cT p).eval ∈ C
    rwa [eval_reduction_of_halts hw cT h]
  · refine iff_of_false h ?_
    show (reduction w cT p).eval ∉ C
    rwa [eval_reduction_of_not_halts hw cT h]

/-- **Rice's problem is synthetically halting-hard.** If `cT` computes a function in `C` and the
nowhere-defined function is not in `C`, then `RiceProblem C` is synthetically halting-hard, given a
waiter program `w` (`exists_isWaiter`). `HaltProblem` many-one reduces to `RiceProblem C`. -/
def _root_.DiagonaLean.Rice.synthFromHalt {C : Set (ℕ →. ℕ)} (w cT : Code) (hw : IsWaiter w)
    (hT : cT.eval ∈ C) (hbot : (fun _ => Part.none : ℕ →. ℕ) ∉ C) :
    HaltProblem ⪯_s RiceProblem C :=
  ⟨reduction w cT, halt_reducesto_rice_spec hw hT hbot⟩

end DiagonaLean.Rice.Reduction
