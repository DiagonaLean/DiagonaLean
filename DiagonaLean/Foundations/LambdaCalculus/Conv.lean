/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence

@[expose] public section

/-! # β-convertibility of λ-terms

Cslib defines locally nameless λ-terms (`Term`), full β-reduction (`FullBeta`, written `M ⭢βᶠ N`)
and its reflexive–transitive closure (`M ↠βᶠ N`). Two terms are β-convertible when they have a
common reduct, `Join (ReflTransGen FullBeta)` (`Conv`, the counterpart of
`Foundations.CombinatoryLogic.Conv` for SKI terms); by Cslib's confluence of `FullBeta` this is an
equivalence relation (`betaConv_equivalence`). The stack machine that enumerates β-conversions is in
`ProofSearch.lean`.

## Main definitions

* `Conv`: β-convertibility. Its former name `BetaConv` is a deprecated alias.

## Main statements

* `betaConv_equivalence`, `betaConv_of_steps`.

## References

* [A. Church, *An Unsolvable Problem of Elementary Number Theory*][Church1936]
-/

namespace DiagonaLean.Foundations.LambdaCalculus

open Cslib LambdaCalculus.LocallyNameless.Untyped Term Relation

/-- Two λ-terms are β-convertible: they have a common reduct under full β-reduction. -/
abbrev Conv (M N : Term ℕ) : Prop := Join (ReflTransGen FullBeta) M N

/-- β-convertibility is an equivalence relation. -/
theorem betaConv_equivalence : Equivalence Conv :=
  Confluent.equivalence_join_reflTransGen confluent_fullBeta

/-- A β-reduction is a β-conversion. -/
theorem betaConv_of_steps {M N : Term ℕ} (h : M ↠βᶠ N) : Conv M N := ⟨N, h, .refl⟩

/-- The former name of `Conv`. -/
@[deprecated Conv (since := "2026-11-27")]
abbrev BetaConv (M N : Term ℕ) : Prop := Conv M N

end DiagonaLean.Foundations.LambdaCalculus
