/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.CombinatoryLogic.Race
import DiagonaLean.Foundations.LambdaCalculus.Translation

@[expose] public section

/-! # The race program for β-conversion

The λ-instance `linst U c n` is the translation of the SKI instance `inst U c n` of
`Foundations/CombinatoryLogic/Race.lean`. When `c` outputs `1` on `n` it β-reduces to `tr FF`
(`betaConv_linst_of_one`); when `c` outputs `0` it β-reduces to `tr TT`, which is not
β-convertible to `tr FF` (`not_betaConv_linst_of_zero`).

The race program `C` runs the race of `Foundations/Computability/ProofRace.lean` against the
proof checker for β-conversion: it searches for a halting run of the machine and for a proof
that its own λ-instance is β-convertible to `tr FF`. Smullyan's argument gives `HaltProblem p ↔`
the λ-instance of `p` is β-convertible to `tr FF` (`halt_iff_betaConv`).

## References

* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.Foundations.LambdaCalculus

open Cslib SKI LambdaCalculus.LocallyNameless.Untyped Nat.Partrec
  DiagonaLean.Foundations.Computability DiagonaLean.Halt DiagonaLean.Halt.Encoding

/-- The λ-instance for the program `c` on input `n`: the translation of the SKI instance. -/
def linst (U : SKI) (c : Code) (n : ℕ) : Term ℕ := tr (CombinatoryLogic.inst U c n)

/-- If `c` outputs `1` on `n`, the λ-instance is β-convertible to `tr FF`. -/
theorem betaConv_linst_of_one {u : Code} {U : SKI} (hu : CombinatoryLogic.IsUniversal u)
    (hU : Computes U u.eval) {c : Code} {n : ℕ} (h : 1 ∈ c.eval n) :
    BetaConv (linst U c n) (tr FF) :=
  betaConv_of_steps (tr_mRed (CombinatoryLogic.inst_mRed_of_one hu hU h))

/-- If `c` outputs `0` on `n`, the λ-instance is not β-convertible to `tr FF`. -/
theorem not_betaConv_linst_of_zero {u : Code} {U : SKI} (hu : CombinatoryLogic.IsUniversal u)
    (hU : Computes U u.eval) {c : Code} {n : ℕ} (h : 0 ∈ c.eval n) :
    ¬ BetaConv (linst U c n) (tr FF) := fun hc =>
  not_betaConv_tr_TT_FF (betaConv_equivalence.trans (betaConv_equivalence.symm
    (betaConv_of_steps (tr_mRed (CombinatoryLogic.inst_mRed_of_zero hu hU h)))) hc)

/-- The code of the translation of `toChurch n` is the code of the translation of `Zero` with
`n` applications of the translation of `Succ` in front. -/
theorem tc_tr_toChurch (n : ℕ) :
    tc (tr (toChurch n)) = (fun m => cp (tc (tr SKI.Succ)) m)^[n] (tc (tr SKI.Zero)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

/-- The code of the translation of `toChurch n` is primitive recursive in `n`. -/
theorem tc_tr_toChurch_prim : Primrec fun n => tc (tr (toChurch n)) := by
  have h : Primrec fun n : ℕ => (fun m => cp (tc (tr SKI.Succ)) m)^[n] (tc (tr SKI.Zero)) := by
    fun_prop
  exact h.of_eq fun n => (tc_tr_toChurch n).symm

/-- The code of `linst U c n` is built from the codes of its parts with `cp`. -/
theorem tc_linst (U : SKI) (c : Code) (n : ℕ) :
    tc (linst U c n) =
      cp (cp (cp (tc (tr U)) (tc (tr (toChurch (Nat.pair (Encodable.encode c) n)))))
        (tc (tr (K ⬝ FF)))) (tc (tr TT)) := rfl

/-- The code of the λ-instance is primitive recursive in the program and the input. -/
theorem tc_linst_prim (U : SKI) : Primrec fun x : Code × ℕ => tc (linst U x.1 x.2) := by
  have h : Primrec fun x : Code × ℕ =>
      tc (tr (toChurch (Nat.pair (Encodable.encode x.1) x.2))) :=
    tc_tr_toChurch_prim.comp (prim_natPair (Primrec.encode.comp Primrec.fst) Primrec.snd)
  have h' : Primrec fun x : Code × ℕ =>
      cp (cp (cp (tc (tr U)) (tc (tr (toChurch (Nat.pair (Encodable.encode x.1) x.2)))))
        (tc (tr (K ⬝ FF)))) (tc (tr TT)) := by
    fun_prop
  exact h'.of_eq fun x => (tc_linst U x.1 x.2).symm

/-- The proof test: `k` codes a program that checks the β-conversion with codes `i`. -/
def chk (k : ℕ) (i : ℕ × ℕ) : Bool := decide (Checks k i.1 i.2)

/-- `chk` is primitive recursive. -/
theorem chk_prim : Primrec₂ chk :=
  (checks_prim.decide.comp (prim_pair Primrec.fst
    (prim_pair (prim_fst Primrec.snd) (prim_snd Primrec.snd)))).to₂

/-- The instance family: the codes of the λ-instance of `c` on `n` and of `tr FF`. -/
def instCode (U : SKI) (c : Code) (n : ℕ) : ℕ × ℕ := (tc (linst U c n), tc (tr FF))

/-- `instCode U` is primitive recursive. -/
theorem instCode_prim (U : SKI) : Primrec₂ (instCode U) :=
  (prim_pair (tc_linst_prim U) (Primrec.const _)).to₂

/-- The λ-instance of `c` on `n` is β-convertible to `tr FF` iff some `k` passes the proof test. -/
theorem betaConv_iff_chk (U : SKI) (c : Code) (n : ℕ) :
    BetaConv (linst U c n) (tr FF) ↔ ∃ k, chk k (instCode U c n) = true :=
  (betaConv_iff_checks (lc_tr _) (lc_tr _)).trans
    (exists_congr fun k => (decide_eq_true_iff (p := Checks k _ _)).symm)

/-- `C` is the race program for β-conversion and the universal term `U`. -/
def RaceProg (U : SKI) (C : Code) : Prop := ProofRace.RaceOn chk (instCode U) C

/-- A race program exists for every SKI term `U`. -/
theorem exists_raceProg (U : SKI) : ∃ C, RaceProg U C :=
  ProofRace.exists_raceOn chk_prim (instCode_prim U)

/-- **Smullyan's argument, for β-conversion.** A `HaltProblem` instance `p` holds iff the
λ-instance of the race program on the data of `p` is β-convertible to `tr FF`. -/
theorem halt_iff_betaConv {u : Code} {U : SKI} {C : Code} (hu : CombinatoryLogic.IsUniversal u)
    (hU : Computes U u.eval) (hC : RaceProg U C) (p : EncodableTM Bool × List Bool) :
    HaltProblem p ↔ BetaConv (linst U C (Encodable.encode (dataOf p))) (tr FF) :=
  ProofRace.halt_iff hC (Q := fun n => BetaConv (linst U C n) (tr FF))
    (fun _ => betaConv_iff_chk U C _)
    (fun _ h => betaConv_linst_of_one hu hU h) (fun _ h => not_betaConv_linst_of_zero hu hU h) p

end DiagonaLean.Foundations.LambdaCalculus
