/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Cslib.Languages.CombinatoryLogic.Evaluation
import Cslib.Languages.CombinatoryLogic.PartrecToSKI
import DiagonaLean.Foundations.CombinatoryLogic.ProofSearch
import DiagonaLean.Foundations.Computability.ProofRace

@[expose] public section

/-! # The race program for SKI convertibility

`U` is an SKI term that computes a universal code `u`: on the Church numeral of `⟪e, n⟫` it
reduces to a Church numeral for the output of the program `e` on `n`, whenever there is one
(`Nat.Partrec.Code.toSKI_correct`). The instance `inst U c n` applies that numeral to `K ⬝ FF` and
`TT`, so it reduces to `FF` when `c` outputs `1` on `n` (`conv_inst_of_one`), and to `TT`, which
is not convertible to `FF`, when `c` outputs `0` (`not_conv_inst_of_zero`).

For a `HaltProblem` instance with data `d`, the race program `C` runs the race of
`Foundations/Computability/ProofRace.lean` on input `d`: it searches for a halting run of the
machine, and for a proof that its own instance `inst U C d` is convertible to `FF`. If the
halting run comes first it returns `1`, and otherwise `0`. Smullyan's argument gives
`HaltProblem p ↔` the instance of `p` is convertible to `FF` (`halt_iff_conv`).

## References

* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.Foundations.CombinatoryLogic

open Cslib SKI Nat.Partrec DiagonaLean.Foundations.Computability DiagonaLean.Halt
  DiagonaLean.Halt.Encoding

/-- `u` is a universal code: on `⟪e, n⟫` it runs the program with code `e` on `n`. -/
def IsUniversal (u : Code) : Prop :=
  ∀ e n, u.eval (Nat.pair e n) = (Denumerable.ofNat Code e).eval n

/-- A universal code exists. -/
theorem exists_isUniversal : ∃ u, IsUniversal u := by
  have hf : Partrec₂ fun e n => (Denumerable.ofNat Code e).eval n :=
    Code.eval_part.comp ((Computable.ofNat Code).comp Computable.fst) Computable.snd
  obtain ⟨u, hu⟩ := Code.exists_code.1 (Partrec₂.unpaired'.2 hf)
  exact ⟨u, fun e n => by simp [hu, Nat.unpaired, Nat.unpair_pair]⟩

/-- The instance for the program `c` on input `n`, given an SKI term `U` for a universal code. -/
def inst (U : SKI) (c : Code) (n : ℕ) : SKI :=
  U ⬝ toChurch (Nat.pair (Encodable.encode c) n) ⬝ (K ⬝ FF) ⬝ TT

/-- If `c` outputs `m` on `n`, then `U` sends the numeral of `⟪c, n⟫` to a numeral for `m`. -/
theorem isChurch_of_mem {u : Code} {U : SKI} (hu : IsUniversal u) (hU : Computes U u.eval)
    {c : Code} {n m : ℕ} (h : m ∈ c.eval n) :
    IsChurch m (U ⬝ toChurch (Nat.pair (Encodable.encode c) n)) :=
  hU _ _ (toChurch_correct _) m (by rwa [hu, Denumerable.ofNat_encode])

/-- If `c` outputs `1` on `n`, the instance reduces to `FF`. -/
theorem inst_mRed_of_one {u : Code} {U : SKI} (hu : IsUniversal u) (hU : Computes U u.eval)
    {c : Code} {n : ℕ} (h : 1 ∈ c.eval n) : inst U c n ↠ FF :=
  (isChurch_of_mem hu hU h (K ⬝ FF) TT).trans (MRed.K FF TT)

/-- If `c` outputs `0` on `n`, the instance reduces to `TT`. -/
theorem inst_mRed_of_zero {u : Code} {U : SKI} (hu : IsUniversal u) (hU : Computes U u.eval)
    {c : Code} {n : ℕ} (h : 0 ∈ c.eval n) : inst U c n ↠ TT :=
  isChurch_of_mem hu hU h (K ⬝ FF) TT

/-- If `c` outputs `1` on `n`, the instance is convertible to `FF`. -/
theorem conv_inst_of_one {u : Code} {U : SKI} (hu : IsUniversal u) (hU : Computes U u.eval)
    {c : Code} {n : ℕ} (h : 1 ∈ c.eval n) : Conv (inst U c n) FF :=
  conv_of_mRed (inst_mRed_of_one hu hU h)

/-- If `c` outputs `0` on `n`, the instance is not convertible to `FF`. -/
theorem not_conv_inst_of_zero {u : Code} {U : SKI} (hu : IsUniversal u) (hU : Computes U u.eval)
    {c : Code} {n : ℕ} (h : 0 ∈ c.eval n) : ¬ Conv (inst U c n) FF := fun hc =>
  TF_nequiv (join_mRed_equivalence.trans
    (join_mRed_equivalence.symm (conv_of_mRed (inst_mRed_of_zero hu hU h))) hc)

/-- The code of `inst U c n` is built from the codes of its parts with `ca`. -/
theorem skc_inst (U : SKI) (c : Code) (n : ℕ) :
    skc (inst U c n) =
      ca (ca (ca (skc U) (skc (toChurch (Nat.pair (Encodable.encode c) n)))) (skc (K ⬝ FF)))
        (skc TT) := rfl

/-- The code of the instance is primitive recursive in the program and the input. -/
theorem skc_inst_prim (U : SKI) : Primrec fun x : Code × ℕ => skc (inst U x.1 x.2) := by
  have h : Primrec fun x : Code × ℕ => skc (toChurch (Nat.pair (Encodable.encode x.1) x.2)) :=
    skc_toChurch_prim.comp (prim_natPair (Primrec.encode.comp Primrec.fst) Primrec.snd)
  have h' : Primrec fun x : Code × ℕ =>
      ca (ca (ca (skc U) (skc (toChurch (Nat.pair (Encodable.encode x.1) x.2)))) (skc (K ⬝ FF)))
        (skc TT) := by
    prim
  exact h'.of_eq fun x => (skc_inst U x.1 x.2).symm

/-- The proof test: `k` codes a program that checks the conversion with codes `i`. -/
def chk (k : ℕ) (i : ℕ × ℕ) : Bool := decide (Checks k i.1 i.2)

/-- `chk` is primitive recursive. -/
theorem chk_prim : Primrec₂ chk :=
  (checks_prim.decide.comp (prim_pair Primrec.fst
    (prim_pair (prim_fst Primrec.snd) (prim_snd Primrec.snd)))).to₂

/-- The instance family: the codes of the instance of `c` on `n` and of `FF`. -/
def instCode (U : SKI) (c : Code) (n : ℕ) : ℕ × ℕ := (skc (inst U c n), skc FF)

/-- `instCode U` is primitive recursive. -/
theorem instCode_prim (U : SKI) : Primrec₂ (instCode U) :=
  (prim_pair (skc_inst_prim U) (Primrec.const _)).to₂

/-- The instance of `c` on `n` is convertible to `FF` iff some `k` passes the proof test. -/
theorem conv_inst_iff_chk (U : SKI) (c : Code) (n : ℕ) :
    Conv (inst U c n) FF ↔ ∃ k, chk k (instCode U c n) = true :=
  conv_iff_checks.trans (exists_congr fun _ => decide_eq_true_iff.symm)

/-- `C` is the race program for the universal term `U`. -/
def RaceProg (U : SKI) (C : Code) : Prop := ProofRace.RaceOn chk (instCode U) C

/-- A race program exists for every SKI term `U`. -/
theorem exists_raceProg (U : SKI) : ∃ C, RaceProg U C :=
  ProofRace.exists_raceOn chk_prim (instCode_prim U)

/-- **Smullyan's argument, for the race program.** A `HaltProblem` instance `p` holds iff the
instance of the race program on the data of `p` is convertible to `FF`. -/
theorem halt_iff_conv {u : Code} {U : SKI} {C : Code} (hu : IsUniversal u)
    (hU : Computes U u.eval) (hC : RaceProg U C) (p : EncodableTM Bool × List Bool) :
    HaltProblem p ↔ Conv (inst U C (Encodable.encode (dataOf p))) FF :=
  ProofRace.halt_iff hC (Q := fun n => Conv (inst U C n) FF)
    (fun _ => conv_inst_iff_chk U C _)
    (fun _ h => conv_inst_of_one hu hU h) (fun _ h => not_conv_inst_of_zero hu hU h) p

end DiagonaLean.Foundations.CombinatoryLogic
