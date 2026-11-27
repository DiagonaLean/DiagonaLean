/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.SemiThue.Reductions.HaltCanon_to_SemiThue
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
problem is halting-hard over `Alpha ℕ Sym2`. The lifting of `Foundations.Codes.Functor` moves it
to every alphabet with two distinct letters, and `posToWord` returns to the plain word
problem, sending a system with an empty left side to a fixed instance without solution. The
`SynthHaltReduction` statements obtained this way are in `SynthHardness.lean`
(`SemiThue.synthPosFromHaltOver`, `SemiThue.synthFromHaltOver`, `SemiThue.synthFromHaltBool`), the
proved ones in `Undecidable.lean`.

## Main statements

* `semiThueFunctor`, `posToWord_spec`.
* The results over every nontrivial alphabet (`SemiThue.haltHard`, `SemiThue.Pos.haltHard`, …) are
  in `Undecidable.lean`, from `SemiThue.posFromHaltOver` and `SemiThue.fromHaltOver`.
* `semiThuePos_manyOneEquiv`: the restricted problem is many-one equivalent over any two such
  alphabets.
-/

namespace DiagonaLean.SemiThue

open Foundations.Grammar Foundations.Rewriting Foundations.Codes DiagonaLean.Synthetic.Definitions

variable {α T : Type}

/-- **The word problem with non-empty left sides, as a functor on synchronizing codes.** -/
abbrev semiThueFunctor : CodeFunctor IsSync where
  Inst T := SRS T × List T × List T
  map c x := (SRS.encode c x.1, encode c x.2.1, encode c x.2.2)
  Prob x := DecisionProblemPos x
  map_unit x := by simp
  map_kcomp c₁ c₂ x := by simp [SRS.encode_kcomp, encode_kcomp]
  natural hc x := by
    rw [DecisionProblemPos, DecisionProblemPos, PosWordProblem, PosWordProblem,
      lhs_ne_encode_iff hc.isCode]
    exact and_congr_right fun h => derives_encode_iff hc h
  supp x := SRS.letters x.1 ++ x.2.1 ++ x.2.2
  map_congr x h := Prod.ext (SRS.encode_congr fun a ha => h a (by simp [ha]))
    (Prod.ext (encode_congr fun a ha => h a (by simp [ha]))
      (encode_congr fun a ha => h a (by simp [ha])))

/-- Back to the plain word problem: a system with an empty left side goes to `[a] ⇒* []` in the
empty system, which has no solution. -/
def posToWord (a : T) (x : SRS T × List T × List T) : SRS T × List T × List T :=
  bif x.1.all (fun lr => !(lr.lhs.length == 0)) then x else ([], [a], [])

/-- `posToWord a` witnesses the reduction from the restricted word problem to the plain one. -/
theorem posToWord_spec (a : T) : @DecisionProblemPos T ⪯_s[posToWord a] @DecisionProblem T := by
  intro x
  have hall : x.1.all (fun lr => !(lr.lhs.length == 0)) = true ↔ ∀ lr ∈ x.1, lr.lhs ≠ [] := by
    simp [List.all_eq_true]
  unfold posToWord
  cases h : x.1.all (fun lr => !(lr.lhs.length == 0))
  · refine iff_of_false (fun hx => by simp [hall.2 hx.1] at h) fun hd => ?_
    rcases Relation.ReflTransGen.cases_head (r := SRS.Step []) hd with h' | ⟨_, hs, -⟩
    · simp at h'
    · obtain ⟨_, hlr, -⟩ := SRS.step_iff.1 hs
      simp at hlr
  · exact and_iff_right (hall.1 h)

/-- `posToWord a` is primitive recursive. -/
@[fun_prop] theorem posToWord_prim [Primcodable T] (a : T) : Primrec (posToWord a) := by
  unfold posToWord
  fun_prop

namespace AlphabetLift

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.MPCP.Reduction
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions

/- Encoding a system is primitive recursive, for a code that may depend on the input. -/
derive_primrec SRS.encode [Primcodable α] [Primcodable β]

/- The letters of a system are primitive recursive in it. -/
derive_primrec SRS.letters [Primcodable α]

/-- **Alphabet invariance of the restricted word problem**: over any two nontrivial `Primcodable`
alphabets, it is many-one equivalent. -/
theorem semiThuePos_manyOneEquiv {β : Type} [Primcodable α] [Primcodable β] [Nontrivial α]
    [Nontrivial β] : ManyOneEquiv (@DecisionProblemPos α) (@DecisionProblemPos β) := by
  code_lift semiThueFunctor

end AlphabetLift

end DiagonaLean.SemiThue
