/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.KAComm.KATermEqBool.Basic
import DiagonaLean.KAComm.KleeneAlgebra.ProofSearch
import DiagonaLean.KAComm.KleeneAlgebra.RExpPrimcodable
import DiagonaLean.KAComm.KleeneAlgebra.BoolCode
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Equality in Kleene algebra with commutations over `{0, 1}` is recursively enumerable

Over the letters `0` and `1`, an equation over `Bool ⊕ Bool` is provable iff its copy over `ℕ ⊕ ℕ`
is (`kaEquiv_iff_map`), which is provable iff some program of the stack machine `sys` checks the
codes (`kaEquiv_iff_checks`). Checking is primitive recursive (`checks_prim`), and so is the code
`rc (toNat e)` (`rcb_prim`). So provable equality in Kleene algebra with these commutations over
`{0, 1}` is recursively enumerable (`KATermEqBool.rePred`). With `KATermEqBool.haltHard` it is as
hard as the halting problem and no harder.

## Main statements

* `KATermEqBool.rePred`: provable equality in Kleene algebra with commutations over `{0, 1}` is
  recursively enumerable.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.KATermEqBool

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Foundations.Computability

/-- **Provable equality in Kleene algebra with commutations over `{0, 1}` is recursively
enumerable**: search for a program that checks the equation. -/
theorem rePred : REPred DecisionProblem :=
  REPred.of_exists_primrecPred (q := fun i k => Checks true k (rc (toNat i.1)) (rc (toNat i.2)))
    ((checks_prim true).comp (Primrec.snd.pair
      ((rcb_prim.comp (Primrec.fst.comp Primrec.fst)).pair
        (rcb_prim.comp (Primrec.snd.comp Primrec.fst)))))
    fun _ => kaEquiv_iff_map.symm.trans kaEquiv_iff_checks

end DiagonaLean.KAComm.KATermEqBool
