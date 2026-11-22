/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.BetaConv.Basic
import DiagonaLean.Foundations.LambdaCalculus.Race
import DiagonaLean.Halt.Inseparable
import DiagonaLean.Foundations.Computability.OutputSearch

@[expose] public section

/-! # `HaltProblem ⪯_s` β-conversion

`reduction U C` sends a `HaltProblem` instance `p` to the pair `(linst U C d, tr FF)`, where `d`
is the code of the data of `p` and `linst U C d` is the translation of the SKI instance of the
race program `C` on `d`. By Smullyan's argument, `p` halts iff the two terms are β-convertible
(`halt_iff_betaConv`). The constants are `U`, an SKI term for a universal code, and `C`, the race
program from the recursion theorem.

`sepRed U c` sends a machine `M` to the λ-instance of the reader program `c` on the data of `M`
on its own code, against `tr FF`. If `M` outputs `[true]` the terms are β-convertible; if it
outputs `[false]` they are not (`sepRed_separates`). So β-conversion separates
`SelfOut true` from `SelfOut false`.

## References

* [A. Church, *An Unsolvable Problem of Elementary Number Theory*][Church1936]
  (for the λI-calculus)
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.BetaConv.Reduction

open Cslib SKI LambdaCalculus.LocallyNameless.Untyped Nat.Partrec
  DiagonaLean.Foundations.LambdaCalculus DiagonaLean.Foundations.Computability DiagonaLean.Halt
  DiagonaLean.Halt.Encoding DiagonaLean.Halt.Inseparable

/-- **The reduction.** The λ-instance of the race program on the data of `p`, against
`tr FF`. -/
def reduction (U : SKI) (C : Code) (p : EncodableTM Bool × List Bool) : Term ℕ × Term ℕ :=
  (linst U C (Encodable.encode (dataOf p)), tr FF)

/-- `reduction U C` reduces `HaltProblem` to β-conversion. -/
theorem halt_reducesto_betaConv_spec {u : Code} {U : SKI} {C : Code}
    (hu : Foundations.CombinatoryLogic.IsUniversal u) (hU : Computes U u.eval)
    (hC : RaceProg U C) : HaltProblem ⪯_s[reduction U C] BetaConvProblem :=
  halt_iff_betaConv hu hU hC

/-- `HaltProblem` many-one reduces to β-conversion. -/
def haltReducesBetaConv {u : Code} (U : SKI) (C : Code)
    (hu : Foundations.CombinatoryLogic.IsUniversal u) (hU : Computes U u.eval)
    (hC : RaceProg U C) : HaltProblem ⪯_s BetaConvProblem :=
  ⟨reduction U C, halt_reducesto_betaConv_spec hu hU hC⟩

/-- The separating instance of a machine: the λ-instance of the reader program `c` on the data
of `M` on its own code, against `tr FF`. -/
def sepRed (U : SKI) (c : Code) (M : EncodableTM Bool) : Term ℕ × Term ℕ :=
  (linst U c (Encodable.encode (dataOf (M, encodeBoolTM M))), tr FF)

/-- `sepRed U c` separates `SelfOut true` from `SelfOut false` by β-conversion. -/
theorem sepRed_separates {u : Code} (U : SKI) (c : Code)
    (hu : Foundations.CombinatoryLogic.IsUniversal u) (hU : Computes U u.eval) (hc : IsReader c) :
    Separates (SelfOut true) (SelfOut false) fun M => BetaConvProblem (sepRed U c M) :=
  ⟨fun _ h => betaConv_linst_of_one hu hU (by simpa using mem_eval_of_outputs hc h),
    fun _ h => not_betaConv_linst_of_zero hu hU (by simpa using mem_eval_of_outputs hc h)⟩

end DiagonaLean.BetaConv.Reduction
