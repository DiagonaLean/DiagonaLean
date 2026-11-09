/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Reductions.SelfOut_to_Eq

@[expose] public section

/-! # `HaltProblem ⪯ₘ` equality on `T Σ̈` and `K Σ̈`: the logical core of Theorem 19 (M8)

`eqRed` sends machines with output `1` into equality on `X` and machines with output `0` out of
it, and says nothing about the others. Smullyan's argument upgrades this to a many-one reduction
from `HaltProblem`, given a family of machines built with the recursion theorem.

For a `HaltProblem` instance `p = (M, w)`, the machine `N p`, run on its own code, searches in
parallel for a halting run of `M` on `w` and for evidence that `SelfEq F (N p)` holds, i.e. a proof
that `eqRed (N p)` is an equality in `X`. If the halting run comes first it outputs `1`; if the
evidence comes first it outputs `0`. That machine satisfies the two fields of `SmullyanFamily`:

* if `M` halts on `w` and `SelfEq F (N p)` fails, no evidence is ever found, so the output is `1`;
* if `M` diverges and `SelfEq F (N p)` holds, the evidence is found, so the output is `0`.

`halt_iff_selfEq` then shows `HaltProblem p ↔ SelfEq F (N p)`.

The closed theorems are in `Reductions/Halt_to_TermEq.lean`, which builds the race directly on empty input and
does not use `SmullyanFamily`. This file remains the statement of the argument on a machine's own
code.

## The hypothesis must be built, not chosen

Lean's logic is classical, so a family with these two fields exists for trivial reasons: send
`p` to a fixed machine that outputs `1` when `HaltProblem p`, and to one that outputs `0` otherwise.
That witness decides `HaltProblem` by case split and breaks the convention on `ManyOneReduces`. A
`SmullyanFamily` is meaningful only when `N` is the machine described above, constructed from the
data of `p` with the recursion theorem. The construction needs:

1. the recursion theorem for `SingleTapeTM Bool` (or a bridge to Mathlib's
   `Nat.Partrec.Code.fixed_point`);
2. a Turing machine that computes `eqRed` from `encodeBoolTM M`;
3. a Turing machine that enumerates the proofs of `Equiv DComm` (or `KAEquiv DComm`).

This is why the evidence must be enumerable: the argument applies to `T Σ̈` and `K Σ̈`, whose
equalities are r.e., and not to language equality, which is co-r.e.

## Main statements

* `SmullyanFamily`: the interface the recursion theorem must supply.
* `halt_iff_selfEq`, `haltReduces_eqVia`, `haltReduces_termEq`, `haltReduces_kaTermEq`: the
  reduction from `HaltProblem`.
* `undecidable_eqVia_of_family`, `undecidable_termEq_of_family`,
  `undecidable_kaTermEq_of_family`: `Undecidable` in the synthetic framework, given a family.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 19
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

open scoped Computability

namespace DiagonaLean.KAComm.Undec

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
def haltReduces_eqVia (F : LangFactor X) (fam : SmullyanFamily (SelfEq F)) :
    HaltProblem ⪯ₘ EqVia F :=
  ⟨eqRed ∘ fam.N, halt_iff_selfEq F fam⟩

/-- **`Undecidable` for equality on `X`,** given a Smullyan family. -/
theorem undecidable_eqVia_of_family (F : LangFactor X) (fam : SmullyanFamily (SelfEq F)) :
    Undecidable (EqVia F) :=
  ⟨haltReduces_eqVia F fam⟩

/-- `HaltProblem` many-one reduces to provable equality in pre-Kleene algebra with commutativity,
through `eqRed ∘ N`. -/
def haltReduces_termEq (fam : SmullyanFamily (SelfEq factorT)) :
    HaltProblem ⪯ₘ @TermEq.DecisionProblem ℕ :=
  ⟨eqRed ∘ fam.N, fun p => (halt_iff_selfEq factorT fam p).trans (eqVia_factorT _)⟩

/-- `HaltProblem` many-one reduces to provable equality in Kleene algebra with commutativity,
through `eqRed ∘ N`. -/
def haltReduces_kaTermEq (fam : SmullyanFamily (SelfEq factorK)) :
    HaltProblem ⪯ₘ @KATermEq.DecisionProblem ℕ :=
  ⟨eqRed ∘ fam.N, fun p => (halt_iff_selfEq factorK fam p).trans (eqVia_factorK _)⟩

/-- **Provable equality in pre-Kleene algebra with commutativity is `Undecidable`,** given a
Smullyan family for `T Σ̈`. -/
theorem undecidable_termEq_of_family (fam : SmullyanFamily (SelfEq factorT)) :
    Undecidable (@TermEq.DecisionProblem ℕ) :=
  ⟨haltReduces_termEq fam⟩

/-- **Provable equality in Kleene algebra with commutativity is `Undecidable`,** given a Smullyan
family for `K Σ̈`. -/
theorem undecidable_kaTermEq_of_family (fam : SmullyanFamily (SelfEq factorK)) :
    Undecidable (@KATermEq.DecisionProblem ℕ) :=
  ⟨haltReduces_kaTermEq fam⟩

end DiagonaLean.KAComm.Undec
