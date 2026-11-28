/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.KAComm.TermEqBool.Basic
import DiagonaLean.KAComm.KleeneAlgebra.ProofSearch
import DiagonaLean.KAComm.KleeneAlgebra.RExpPrimcodable
import DiagonaLean.KAComm.KleeneAlgebra.BoolCode
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Equality on `T Σ̈` over `{0, 1}` is recursively enumerable

Over the letters `0` and `1`, an equation over `Bool ⊕ Bool` is provable iff its copy over `ℕ ⊕ ℕ`
is (`equiv_iff_map`), which is provable iff some program of the stack machine `sys` checks the codes
(`equiv_iff_checks`). Checking is primitive recursive (`checks_prim`), and so is the code
`rc (toNat e)` (`rcb_prim`). So equality on `T Σ̈` over `{0, 1}` is recursively enumerable
(`TermEqBool.rePred`). With `TermEqBool.haltHard` it is as hard as the halting problem and no
harder.

## Main statements

* `TermEqBool.rePred`: equality on `T Σ̈` over `{0, 1}` is recursively enumerable.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

namespace DiagonaLean.KAComm.TermEqBool

open DiagonaLean.KAComm.KleeneAlgebra DiagonaLean.Foundations.Computability

/-- **Equality on `T Σ̈` over `{0, 1}` is recursively enumerable**: search for a program that checks
the equation. -/
theorem rePred : REPred DecisionProblem :=
  REPred.of_exists_primrecPred (q := fun i k => Checks false k (rc (toNat i.1)) (rc (toNat i.2)))
    ((checks_prim false).comp (Primrec.snd.pair
      ((rcb_prim.comp (Primrec.fst.comp Primrec.fst)).pair
        (rcb_prim.comp (Primrec.snd.comp Primrec.fst)))))
    fun _ => equiv_iff_map.symm.trans equiv_iff_checks

end DiagonaLean.KAComm.TermEqBool
