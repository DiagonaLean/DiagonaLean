/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.SKIConv.Basic
import DiagonaLean.Foundations.CombinatoryLogic.ProofSearch
import DiagonaLean.Foundations.CombinatoryLogic.Primcodable
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # SKI convertibility is recursively enumerable

Two SKI terms are convertible iff some program of the proof search checks the conversion
(`Foundations.CombinatoryLogic.conv_iff_checks`), and checking is primitive recursive in the
program and the codes of the terms (`checks_prim`, `skc_primrec`). So convertibility is recursively
enumerable (`SKIConv.rePred`), by a search for a checking program. With `SKIConv.haltHard` it is as
hard as the halting problem and no harder: it is semi-decidable, and its complement is not.

## Main statements

* `SKIConv.rePred`: convertibility of SKI terms is recursively enumerable.
-/

namespace DiagonaLean.SKIConv

open Cslib Foundations.CombinatoryLogic

/-- **SKI convertibility is recursively enumerable**: search for a program that checks the
conversion. -/
theorem rePred : REPred DecisionProblem :=
  REPred.of_exists_primrecPred (q := fun i k => Checks k (skc i.1) (skc i.2))
    (checks_prim.comp (f := fun x : (SKI × SKI) × ℕ => (x.2, skc x.1.1, skc x.1.2)) (by
      have := skc_primrec; fun_prop))
    fun _ => conv_iff_checks

end DiagonaLean.SKIConv
