/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.SKIConv.Basic
import DiagonaLean.Foundations.CombinatoryLogic.Race
import DiagonaLean.Halt.Inseparable
import DiagonaLean.Foundations.Computability.OutputSearch

@[expose] public section

/-! # `HaltProblem ⪯ₘ` SKI convertibility

`reduction U C` sends a `HaltProblem` instance `p` to the pair `(inst U C d, FF)`, where `d` is
the code of the data of `p` and `inst U C d` is the instance of the race program `C` on `d`. By
Smullyan's argument, `p` halts iff the two terms are convertible (`halt_iff_conv`). The
constants are `U`, an SKI term for a universal code, and `C`, the race program from the
recursion theorem.

`sepRed U c` sends a machine `M` to the instance of the reader program `c` on the data of `M` on
its own code, against `FF`. If `M` outputs `[true]` the reader returns `1` and the terms are
convertible; if it outputs `[false]` the reader returns `0` and they are not (`sepRed_separates`).
So convertibility separates `SelfOut true` from `SelfOut false`.

## References

* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.SKIConv.Reduction

open Cslib SKI Nat.Partrec DiagonaLean.Foundations.CombinatoryLogic
  DiagonaLean.Foundations.Computability DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Inseparable

/-- **The reduction.** The instance of the race program on the data of `p`, against `FF`. -/
def reduction (U : SKI) (C : Code) (p : EncodableTM Bool × List Bool) : SKI × SKI :=
  (inst U C (Encodable.encode (dataOf p)), FF)

/-- `reduction U C` reduces `HaltProblem` to SKI convertibility. -/
theorem halt_reducesto_skiConv_spec {u : Code} {U : SKI} {C : Code} (hu : IsUniversal u)
    (hU : Computes U u.eval) (hC : RaceProg U C) :
    HaltProblem ⪯ₘ[reduction U C] SKIConvProblem :=
  halt_iff_conv hu hU hC

/-- `HaltProblem` many-one reduces to SKI convertibility. -/
def haltReducesSKIConv {u : Code} (U : SKI) (C : Code) (hu : IsUniversal u)
    (hU : Computes U u.eval) (hC : RaceProg U C) : HaltProblem ⪯ₘ SKIConvProblem :=
  ⟨reduction U C, halt_reducesto_skiConv_spec hu hU hC⟩

/-- The separating instance of a machine: the instance of the reader program `c` on the data of
`M` on its own code, against `FF`. -/
def sepRed (U : SKI) (c : Code) (M : EncodableTM Bool) : SKI × SKI :=
  (inst U c (Encodable.encode (dataOf (M, encodeBoolTM M))), FF)

/-- `sepRed U c` separates `SelfOut true` from `SelfOut false` by SKI convertibility. -/
theorem sepRed_separates {u : Code} (U : SKI) (c : Code) (hu : IsUniversal u)
    (hU : Computes U u.eval) (hc : IsReader c) :
    Separates (SelfOut true) (SelfOut false) fun M => SKIConvProblem (sepRed U c M) :=
  ⟨fun _ h => conv_inst_of_one hu hU (by simpa using mem_eval_of_outputs hc h),
    fun _ h => not_conv_inst_of_zero hu hU (by simpa using mem_eval_of_outputs hc h)⟩

end DiagonaLean.SKIConv.Reduction
