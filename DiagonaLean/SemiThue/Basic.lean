/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Rewriting.SRS

@[expose] public section

/-! # The word problem for string rewriting systems

A string rewriting system (semi-Thue system) `R` over `T` is a finite list of rules `l ⟶ r` between
words (`Foundations.Rewriting.SRS`, where the rewriting relations `⭢[R]` and `↠[R]` are defined).
Its **word problem** asks whether a word `u` rewrites to a word `v` in finitely many steps:
`WordProblem R u v`, which is `u ↠[R] v`. Partially applied, `WordProblem R u` is the set of words
that `u` rewrites to. Two variants are specialisations of it: `ToEmpty R u`, the target `[]`, and
`PosWordProblem R u v`, for systems whose left sides are all non-empty.

The decision problems take one argument, an instance (`DecisionProblem`, `DecisionProblemPos`,
`ToEmptyProblem`), since the reductions and the computability statements are about predicates on
one type; each is one line that uncurries the curried form, and `decisionProblem_mk` and its
companions state them curried, by `Iff.rfl`. The answer depends only on the set of rules
(`wordProblem_congr`).

To audit the definition, read `WordProblem`, `decisionProblem_mk` and `wordProblem_iff`, which
states the word problem in Mathlib's terms; all are pinned in `scripts/HeadlineTest.lean`.

## Main definitions

* `WordProblem`, `ToEmpty`, `PosWordProblem`: the problems, curried.
* `DecisionProblem`, `DecisionProblemPos`, `ToEmptyProblem`: the same, on instances.

## Main statements

* `decisionProblem_mk`, `decisionProblemPos_mk`, `toEmptyProblem_mk`: the problems on instances
  are the curried problems.
* `wordProblem_iff`: the word problem in Mathlib's terms, `ReflTransGen` of one step.
* `wordProblem_congr`: the word problem depends only on the set of rules.

## References

* E. L. Post, *Recursive unsolvability of a problem of Thue* (1947)
* A. A. Markov, *On the impossibility of certain algorithms in the theory of associative systems*
  (1947)
-/

namespace DiagonaLean.SemiThue

open DiagonaLean.Foundations.Rewriting Relation

variable {T : Type}

/-! ### The problems, curried -/

/-- **The word problem for `R`**: does `u` rewrite to `v`? Partially applied, `WordProblem R u` is
the set of words that `u` rewrites to. -/
abbrev WordProblem (R : SRS T) (u v : Word T) : Prop := u ↠[R] v

/-- Does `u` rewrite to the empty word? The word problem with target `[]`. -/
abbrev ToEmpty (R : SRS T) (u : Word T) : Prop := WordProblem R u []

/-- The word problem for systems whose rules all have non-empty left sides: are they all non-empty,
and does `u` rewrite to `v`? Synchronizing codes preserve and reflect it (`AlphabetLift.lean`);
they do not preserve and reflect the word problem, since an empty left side matches inside a
block. -/
def PosWordProblem (R : SRS T) (u v : Word T) : Prop :=
  (∀ ρ ∈ R, ρ.lhs ≠ []) ∧ WordProblem R u v

/-! ### The problems on instances, for the reductions and the computability statements -/

/-- An instance of the word problem: a system `R`, a source word `u` and a target word `v`. -/
abbrev Instance (T : Type) := SRS T × Word T × Word T

/-- **The word problem on an instance `(R, u, v)`**, for the reductions and the computability
statements: `WordProblem R u v`. Read it curried, `decisionProblem_mk`. -/
def DecisionProblem (x : Instance T) : Prop := WordProblem x.1 x.2.1 x.2.2

/-- **`PosWordProblem` on an instance `(R, u, v)`**. Read it curried, `decisionProblemPos_mk`. -/
def DecisionProblemPos (x : Instance T) : Prop := PosWordProblem x.1 x.2.1 x.2.2

/-- **`ToEmpty` on an instance `(R, u)`**. Read it curried, `toEmptyProblem_mk`. -/
def ToEmptyProblem (x : SRS T × Word T) : Prop := ToEmpty x.1 x.2

/-- The word problem on an instance is the curried word problem. -/
@[simp] theorem decisionProblem_mk (R : SRS T) (u v : Word T) :
    DecisionProblem (R, u, v) ↔ WordProblem R u v := Iff.rfl

/-- `DecisionProblemPos` on an instance is `PosWordProblem`. -/
@[simp] theorem decisionProblemPos_mk (R : SRS T) (u v : Word T) :
    DecisionProblemPos (R, u, v) ↔ PosWordProblem R u v := Iff.rfl

/-- `ToEmptyProblem` on an instance is `ToEmpty`. -/
@[simp] theorem toEmptyProblem_mk (R : SRS T) (u : Word T) :
    ToEmptyProblem (R, u) ↔ ToEmpty R u := Iff.rfl

/-! ### Transparency -/

/-- **The word problem in Mathlib's terms**: the reflexive–transitive closure of one step, where a
step `p ++ l ++ q ⭢[R] p ++ r ++ q` uses a rule `l ⟶ r` of `R` (`SRS.step_iff`). -/
theorem wordProblem_iff (R : SRS T) (u v : Word T) :
    WordProblem R u v ↔ ReflTransGen (SRS.Step R) u v := Iff.rfl

/-- **The word problem depends only on the set of rules**: not on their order or repetition. -/
theorem wordProblem_congr {R R' : SRS T} (h : ∀ ρ, ρ ∈ R ↔ ρ ∈ R') (u v : Word T) :
    WordProblem R u v ↔ WordProblem R' u v :=
  SRS.derives_congr h u v

end DiagonaLean.SemiThue
