/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.BetaConv.Basic
import DiagonaLean.Foundations.LambdaCalculus.ProofSearch
import DiagonaLean.Foundations.LambdaCalculus.Primcodable
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # β-conversion is recursively enumerable

Two λ-terms are β-convertible iff they are equal or some program of the proof search checks the
conversion (`Foundations.LambdaCalculus.conv_iff_exists_checks`): on locally closed terms by the
proof search, and otherwise because `FullBeta` takes no step from a term that is not locally closed.
Equality of terms and checking are primitive recursive (`checks_prim`, `tc_primrec`), so
β-conversion is recursively enumerable (`BetaConv.rePred`). With `BetaConv.haltHard` it is as hard
as the halting problem and no harder.

## Main statements

* `BetaConv.rePred`: β-conversion of λ-terms is recursively enumerable.
-/

namespace DiagonaLean.BetaConv

open Cslib LambdaCalculus.LocallyNameless.Untyped Foundations.LambdaCalculus

/-- **β-conversion is recursively enumerable**: the terms are equal, or search for a program that
checks the conversion. -/
theorem rePred : REPred DecisionProblem :=
  REPred.of_exists_primrecPred (q := fun i k => i.1 = i.2 ∨ Checks k (tc i.1) (tc i.2))
    (PrimrecPred.or (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
      (checks_prim.comp (f := fun x : (Term ℕ × Term ℕ) × ℕ => (x.2, tc x.1.1, tc x.1.2)) (by
        have := tc_primrec; fun_prop)))
    fun i => conv_iff_exists_checks i.1 i.2

end DiagonaLean.BetaConv
