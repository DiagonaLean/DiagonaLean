/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.KAComm.KATermEq.Basic
import DiagonaLean.KAComm.KleeneAlgebra.ProofSearch
import DiagonaLean.KAComm.KleeneAlgebra.RExpPrimcodable
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Equality in Kleene algebra with commutations is recursively enumerable

An equation `e = f` is provable iff some program of the stack machine `sys` checks the codes
`(rc e, rc f)` (`kaEquiv_iff_checks`), and checking is primitive recursive in the program and the
two codes (`checks_prim`). So provable equality in Kleene algebra with these commutations is
recursively enumerable (`KATermEq.rePred`). With `KATermEq.haltHard` it is as hard as the halting
problem and no harder.

## Main statements

* `KATermEq.rePred`: provable equality in Kleene algebra with commutations is recursively
  enumerable.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.KATermEq

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Foundations.Computability

/-- **Provable equality in Kleene algebra with commutations is recursively enumerable**: search for
a program that checks the equation. -/
theorem rePred : REPred DecisionProblem :=
  REPred.of_exists_primrecPred (q := fun i k => Checks true k (rc i.1) (rc i.2))
    ((checks_prim true).comp (Primrec.snd.pair
      ((RExp.rc_primrec.comp (Primrec.fst.comp Primrec.fst)).pair
        (RExp.rc_primrec.comp (Primrec.snd.comp Primrec.fst)))))
    fun _ => kaEquiv_iff_checks

end DiagonaLean.KAComm.KATermEq
