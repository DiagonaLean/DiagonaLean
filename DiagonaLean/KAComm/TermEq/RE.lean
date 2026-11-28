/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.KAComm.TermEq.Basic
import DiagonaLean.KAComm.KleeneAlgebra.ProofSearch
import DiagonaLean.KAComm.KleeneAlgebra.RExpPrimcodable
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Equality on `T Σ̈` is recursively enumerable

An equation `e = f` is provable iff some program of the stack machine `sys` checks the codes
`(rc e, rc f)` (`equiv_iff_checks`), and checking is primitive recursive in the program and the two
codes (`checks_prim`). So equality on `T Σ̈` is recursively enumerable (`TermEq.rePred`). With
`TermEq.haltHard` it is as hard as the halting problem and no harder.

## Main statements

* `TermEq.rePred`: equality on `T Σ̈` is recursively enumerable.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.TermEq

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Foundations.Computability

/-- **Equality on `T Σ̈` is recursively enumerable**: search for a program that checks
the equation. -/
theorem rePred : REPred DecisionProblem :=
  REPred.of_exists_primrecPred (q := fun i k => Checks false k (rc i.1) (rc i.2))
    ((checks_prim false).comp (Primrec.snd.pair
      ((RExp.rc_primrec.comp (Primrec.fst.comp Primrec.fst)).pair
        (RExp.rc_primrec.comp (Primrec.snd.comp Primrec.fst)))))
    fun _ => equiv_iff_checks

end DiagonaLean.KAComm.TermEq
