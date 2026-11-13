/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.Reductions.SelfOut_to_Eq

@[expose] public section

/-! # `HaltProblem ⪯ₘ` equality on `T Σ̈` and `K Σ̈`: the logical core of Theorem 19

`eqRed` sends machines with output `1` into equality on `X` and machines with output `0` out of
it. Smullyan's argument upgrades this to a many-one reduction from `HaltProblem`, given a
`SmullyanFamily`: machines `N p` that, on their own code, race a halting run of `p` against
evidence that `SelfEq F (N p)` holds. Then `HaltProblem p ↔ SelfEq F (N p)` (`halt_iff_selfEq`).

Since Lean's logic is classical, a `SmullyanFamily` can be chosen by deciding `HaltProblem p`, so
the theorems here are meaningful only for a family built from the data of `p` with the recursion
theorem. The closed theorems are in `Halt_to_TermEq.lean`, which builds the race directly on empty
input and does not use `SmullyanFamily`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 19
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

open scoped Computability

namespace DiagonaLean.KAComm.Undec

open DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation RExp

variable {X : Type*}

/-- The machines that the recursion theorem must supply: on its own code, `N p` outputs `1` when
`p` halts and `S (N p)` fails, and outputs `0` when `p` diverges and `S (N p)` holds. See the
module docstring: `N` must be constructed from the data of `p`, never chosen by deciding
`HaltProblem p`. -/
structure SmullyanFamily (S : EncodableTM Bool → Prop) where
  /-- The machine for the instance `p`. -/
  N : EncodableTM Bool × List Bool → EncodableTM Bool
  /-- The halting run wins the race. -/
  out_true : ∀ p, HaltProblem p → ¬ S (N p) → SelfOut true (N p)
  /-- The evidence for `S` wins the race. -/
  out_false : ∀ p, ¬ HaltProblem p → S (N p) → SelfOut false (N p)

/-- **Smullyan's argument.** `p` halts iff `eqRed (N p)` holds in `X`. -/
theorem halt_iff_selfEq (F : LangFactor X) (fam : SmullyanFamily (SelfEq F))
    (p : EncodableTM Bool × List Bool) : HaltProblem p ↔ SelfEq F (fam.N p) := by
  constructor
  · intro hp
    by_contra hS
    exact hS (eqVia_eqRed_pos F (fam.out_true p hp hS))
  · intro hS
    by_contra hp
    exact eqVia_eqRed_neg F (fam.out_false p hp hS) hS

/-- `HaltProblem` many-one reduces to equality on `X`, through `eqRed ∘ N`. -/
def haltReducesEqVia (F : LangFactor X) (fam : SmullyanFamily (SelfEq F)) :
    HaltProblem ⪯ₘ EqVia F :=
  ⟨eqRed ∘ fam.N, halt_iff_selfEq F fam⟩

/-- **`Undecidable` for equality on `X`,** given a Smullyan family. -/
theorem undecidable_eqVia_of_family (F : LangFactor X) (fam : SmullyanFamily (SelfEq F)) :
    Undecidable (EqVia F) :=
  ⟨haltReducesEqVia F fam⟩

/-- `HaltProblem` many-one reduces to provable equality in pre-Kleene algebra with commutativity,
through `eqRed ∘ N`. -/
def haltReducesTermEq (fam : SmullyanFamily (SelfEq factorT)) :
    HaltProblem ⪯ₘ @TermEq.DecisionProblem ℕ :=
  ⟨eqRed ∘ fam.N, fun p => (halt_iff_selfEq factorT fam p).trans (eqVia_factorT _)⟩

/-- `HaltProblem` many-one reduces to provable equality in Kleene algebra with commutativity,
through `eqRed ∘ N`. -/
def haltReducesKATermEq (fam : SmullyanFamily (SelfEq factorK)) :
    HaltProblem ⪯ₘ @KATermEq.DecisionProblem ℕ :=
  ⟨eqRed ∘ fam.N, fun p => (halt_iff_selfEq factorK fam p).trans (eqVia_factorK _)⟩

/-- **Provable equality in pre-Kleene algebra with commutativity is `Undecidable`,** given a
Smullyan family for `T Σ̈`. -/
theorem undecidable_termEq_of_family (fam : SmullyanFamily (SelfEq factorT)) :
    Undecidable (@TermEq.DecisionProblem ℕ) :=
  ⟨haltReducesTermEq fam⟩

/-- **Provable equality in Kleene algebra with commutativity is `Undecidable`,** given a Smullyan
family for `K Σ̈`. -/
theorem undecidable_kaTermEq_of_family (fam : SmullyanFamily (SelfEq factorK)) :
    Undecidable (@KATermEq.DecisionProblem ℕ) :=
  ⟨haltReducesKATermEq fam⟩

end DiagonaLean.KAComm.Undec
