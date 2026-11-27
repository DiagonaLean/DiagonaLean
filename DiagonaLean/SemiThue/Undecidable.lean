/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.SemiThue.AlphabetLift
import DiagonaLean.MPCP.Undecidable
import DiagonaLean.SemiThue.Reductions.HaltCanon_to_SemiThue
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Undecidability of the word problem for string rewriting systems

The word problem asks, given a system `R` and words `u`, `v`, whether `u ↠[R] v`
(`WordProblem R u v`, `Basic.lean`). Its one-argument form `DecisionProblem (R, u, v)` is the same
predicate (`decisionProblem_mk`), so `SemiThue.not_computablePred : Undecidable DecisionProblem`
says that no computable function of `(R, u, v)` decides whether `u ↠[R] v`.

`canonToEmpty` (`Reductions/HaltCanon_to_SemiThue.lean`) reduces the halting problem on canonical
machines to `ToEmpty`, whether a word rewrites to `[]`, computably, and `canonWord` reduces it to
`PosWordProblem`, the word problem for systems with non-empty left sides. The change of alphabet
along `semiThueFunctor` (`AlphabetLift.lean`) and `posToWord` give the word problem over every
alphabet with two distinct letters. The synthetic results are in `SynthHardness.lean`.

## Main statements

* `SemiThue.toEmptyFromHalt`: `ToEmpty` is halting-hard, over `Alpha ℕ Sym2`.
* `SemiThue.posFromHalt`: `PosWordProblem` is halting-hard, over `Alpha ℕ Sym2`, through Post's and
  Markov's reduction `canonWord`.
* `SemiThue.posFromHaltOver`, `SemiThue.fromHaltOver b0 b1 hne`, `SemiThue.fromHaltBool`: over any
  alphabet with two distinct letters.
* By `halt_results`: `SemiThue.haltHard`, `SemiThue.not_computablePred`,
  `SemiThue.not_machineDecidable` for the word problem (Post, Markov 1947) over every nontrivial
  alphabet; the same under `SemiThue.Pos` for `PosWordProblem`, and under `SemiThue.ToEmpty` for
  `ToEmpty` over `Alpha ℕ Sym2`. They are halting-hard, undecidable, and no Turing machine decides
  them under any computable encoding.

## References

* E. L. Post, *Recursive unsolvability of a problem of Thue* (1947)
* A. A. Markov, *On the impossibility of certain algorithms in the theory of associative systems*
  (1947)
-/

namespace DiagonaLean.SemiThue

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.SemiThue.Reduction

/-- **Whether a word rewrites to the empty word (`ToEmpty`) is halting-hard**, over
`Alpha ℕ Sym2`: a reduction from the halting problem on canonical machines, proved computable. -/
def toEmptyFromHalt : HaltReduction (@ToEmptyProblem (Alpha ℕ Normalize.Sym2)) :=
  ⟨canonToEmpty, canonToEmpty_prim.to_comp, haltCanon_iff_toEmpty⟩

/-- **The word problem for systems with non-empty left sides (`PosWordProblem`) is halting-hard**,
over `Alpha ℕ Sym2`: the reduction `canonWord` of Post and Markov (1947), whose systems have
non-empty left sides (`codeRules_lhs_ne`). The plain word problem over `Alpha ℕ Sym2` follows,
with the same function, and over every alphabet with two letters from `fromHaltOver`. -/
def posFromHalt : HaltReduction (@DecisionProblemPos (Alpha ℕ Normalize.Sym2)) :=
  ⟨canonWord, canonWord_prim.to_comp,
    fun x => (haltCanon_iff_toEmpty x).trans (and_iff_right (codeRules_lhs_ne _)).symm⟩

/-- **The word problem for systems with non-empty left sides is halting-hard over any alphabet with
two distinct letters**: `posFromHalt`, then the change of alphabet along `semiThueFunctor`. -/
def posFromHaltOver {α : Type} [Primcodable α] (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction (@DecisionProblemPos α) := by
  code_lift semiThueFunctor from posFromHalt

/-- **The word problem for string rewriting systems is halting-hard over any alphabet with two
distinct letters**: `posFromHaltOver`, then `posToWord b0` (`posToWord_spec`, `posToWord_prim`). -/
def fromHaltOver {α : Type} [Primcodable α] (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction (@DecisionProblem α) := by
  hard_reduce_from (posFromHaltOver b0 b1 hne) with (posToWord b0) using (posToWord_spec b0)

/-- **The word problem for string rewriting systems over `Bool` is halting-hard.** -/
def fromHaltBool : HaltReduction (@DecisionProblem Bool) :=
  fromHaltOver false true Bool.false_ne_true

/-- The word problem over `Bool` is registered as halting-hard. -/
instance : HaltSource (@DecisionProblem Bool) := ⟨fromHaltBool⟩

section
variable {α : Type} [Primcodable α] [Nontrivial α]

halt_results (@DecisionProblem α) over_letters from fromHaltOver

halt_results Pos for (@DecisionProblemPos α) over_letters from posFromHaltOver

halt_results ToEmpty for (@ToEmptyProblem (Alpha ℕ Normalize.Sym2)) from toEmptyFromHalt

end

end DiagonaLean.SemiThue
