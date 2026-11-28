/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Cslib.Languages.CombinatoryLogic.Confluence

@[expose] public section

/-! # Convertibility of SKI terms

Cslib defines SKI terms (`SKI`), one reduction step (`SKI.Red`, written `x ⭢ y`) and its
reflexive–transitive closure (`x ↠ y`). Two terms are convertible when they have a common reduct,
`Join (ReflTransGen Red)` (`Conv`); by Cslib's confluence of `Red` this is an equivalence relation
(`join_mRed_equivalence`). The stack machine that enumerates conversions is in `ProofSearch.lean`.

## Main definitions

* `Conv`: convertibility.

## Main statements

* `conv_of_mRed`, `conv_app`: a reduction is a conversion; conversion is a congruence.

## References

* [J. R. Hindley, J. P. Seldin,
  *Lambda-Calculus and Combinators: An Introduction*][HindleySeldin2008]
-/

namespace DiagonaLean.Foundations.CombinatoryLogic

open Cslib SKI Relation

/-- Two SKI terms are convertible: they have a common reduct. -/
abbrev Conv (x y : SKI) : Prop := Join (ReflTransGen Red) x y

/-- A reduction is a conversion. -/
theorem conv_of_mRed {x y : SKI} (h : x ↠ y) : Conv x y := ⟨y, h, .refl⟩

/-- Convertibility is a congruence for application. -/
theorem conv_app {x x' y y' : SKI} (hx : Conv x x') (hy : Conv y y') : Conv (x ⬝ y) (x' ⬝ y') :=
  join_mRed_equivalence.trans (join_mRed_head y hx) (join_mRed_tail x' hy)

end DiagonaLean.Foundations.CombinatoryLogic
