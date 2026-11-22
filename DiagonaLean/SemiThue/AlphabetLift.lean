/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.SemiThue.MachineLevel
import DiagonaLean.Foundations.Codes.Tactic
import DiagonaLean.Foundations.Codes.Rewriting

@[expose] public section

/-! # The word problem over every alphabet with two letters

The word problem for systems whose left sides are all non-empty (`DecisionProblemPos`) is a
functor on synchronizing codes (`semiThueFunctor`): encoding every word keeps left sides non-empty
(`Foundations.Codes.lhs_ne_encode_iff`), and on such systems preserves and reflects derivability
(`Foundations.Codes.derives_encode_iff`). The plain word problem is not: an empty left side
matches inside a block.

The reductions from the halting problem produce systems with non-empty left sides, so the restricted
problem is undecidable over `Alpha ℕ Sym2`, both by a synthetic halting reduction and at machine
level. The lifting of `Foundations.Codes.Functor` moves it to every alphabet with two distinct
letters, and `posReduces` returns to the plain word problem, sending a system with an empty left
side to a fixed instance without solution. The `SynthHaltReduction` statements obtained this way are
in `Undecidable.lean` (`undecidableSemiThuePosOf`, `undecidableSemiThueOf`,
`undecidableSemiThueBool`).

## Main statements

* `semiThueFunctor`, `posReduces`.
* `not_computablePred_semiThuePosOf`, `not_computablePred_semiThueOf`,
  `not_machineDecidable_semiThueOf`: over every nontrivial `Primcodable` alphabet.
* `semiThuePos_manyOneEquiv`: the restricted problem is many-one equivalent over any two such
  alphabets.
-/

namespace DiagonaLean.SemiThue

open Foundations.Grammar Foundations.Codes DiagonaLean.Synthetic.Definitions

variable {α T : Type}

/-- **The word problem with non-empty left sides, as a functor on synchronizing codes.** -/
abbrev semiThueFunctor : CodeFunctor IsSync where
  Inst T := SRS T × List T × List T
  map c x := (SRS.encode c x.1, encode c x.2.1, encode c x.2.2)
  Prob x := DecisionProblemPos x
  map_unit x := by simp
  map_kcomp c₁ c₂ x := by simp [SRS.encode_kcomp, encode_kcomp]
  natural hc x := by
    rw [DecisionProblemPos, DecisionProblemPos, lhs_ne_encode_iff hc.isCode]
    exact and_congr_right fun h => derives_encode_iff hc h
  supp x := letters x.1 ++ x.2.1 ++ x.2.2
  map_congr x h := Prod.ext (SRS.encode_congr fun a ha => h a (by simp [ha]))
    (Prod.ext (encode_congr fun a ha => h a (by simp [ha]))
      (encode_congr fun a ha => h a (by simp [ha])))

/-- Back to the plain word problem: a system with an empty left side goes to `[a] ⇒* []` in the
empty system, which has no solution. -/
def posToWord (a : T) (x : SRS T × List T × List T) : SRS T × List T × List T :=
  bif x.1.all (fun lr => !(lr.1.length == 0)) then x else ([], [a], [])

/-- `posToWord a` witnesses the reduction from the restricted word problem to the plain one. -/
theorem posToWord_spec (a : T) : @DecisionProblemPos T ⪯_s[posToWord a] @DecisionProblem T := by
  intro x
  have hall : x.1.all (fun lr => !(lr.1.length == 0)) = true ↔ ∀ lr ∈ x.1, lr.1 ≠ [] := by
    simp [List.all_eq_true]
  unfold posToWord
  cases h : x.1.all (fun lr => !(lr.1.length == 0))
  · refine iff_of_false (fun hx => by simp [hall.2 hx.1] at h) fun hd => ?_
    rcases Relation.ReflTransGen.cases_head (r := SRS.Step []) hd with h' | ⟨_, ⟨_, hlr, -⟩, -⟩
    · simp at h'
    · simp at hlr
  · exact and_iff_right (hall.1 h)

/-- The restricted word problem many-one reduces to the plain one, given a letter. -/
def posReduces (a : T) : @DecisionProblemPos T ⪯_s @DecisionProblem T :=
  ⟨posToWord a, posToWord_spec a⟩

namespace MachineLevel

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.MPCP.Reduction
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions

/-- **The restricted word problem is not a computable predicate** over `Alpha ℕ Sym2`: the systems
of machine codes have non-empty left sides (`codeRules_lhs_ne`). -/
theorem not_computablePred_semiThuePos :
    ¬ ComputablePred (@DecisionProblemPos (Alpha ℕ Foundations.Computability.Normalize.Sym2)) :=
  not_computablePred_of_selfHalt (code := fun w => ((toEmptyCode w).1, (toEmptyCode w).2, []))
    (by have := toEmptyCode_prim; exact Primrec.to_comp (by fun_prop))
    fun M => (selfHalt_iff_toEmpty M).trans (and_iff_right (codeRules_lhs_ne _)).symm

/- Encoding a system is primitive recursive, for a code that may depend on the input. -/
derive_primrec SRS.encode [Primcodable α] [Primcodable β]

/-- **The restricted word problem is not a computable predicate over any nontrivial alphabet.** -/
theorem not_computablePred_semiThuePosOf [Primcodable α] [Nontrivial α] :
    ¬ ComputablePred (@DecisionProblemPos α) := by
  code_lift semiThueFunctor from not_computablePred_semiThuePos

/-- **The word problem for string rewriting systems is not a computable predicate over any
nontrivial alphabet.** -/
theorem not_computablePred_semiThueOf [Primcodable α] [Nontrivial α] :
    ¬ ComputablePred (@DecisionProblem α) := by
  obtain ⟨a, -, -⟩ := exists_pair_ne α
  refine not_computablePred_of_reduces (posReduces a) (Primrec.to_comp ?_)
    not_computablePred_semiThuePosOf
  show Primrec (posToWord a)
  unfold posToWord
  fun_prop

/-- **No Turing machine decides the word problem for string rewriting systems over any nontrivial
alphabet**, under any computable encoding. -/
theorem not_machineDecidable_semiThueOf [Primcodable α] [Nontrivial α]
    {enc : SRS α × List α × List α → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc (@DecisionProblem α) :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_semiThueOf

/-- **Alphabet invariance of the restricted word problem**: over any two nontrivial `Primcodable`
alphabets, it is many-one equivalent. -/
theorem semiThuePos_manyOneEquiv {β : Type} [Primcodable α] [Primcodable β] [Nontrivial α]
    [Nontrivial β] : ManyOneEquiv (@DecisionProblemPos α) (@DecisionProblemPos β) := by
  code_lift semiThueFunctor

end MachineLevel

end DiagonaLean.SemiThue
