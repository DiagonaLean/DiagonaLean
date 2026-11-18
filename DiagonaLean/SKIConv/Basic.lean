/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Cslib.Languages.CombinatoryLogic.Confluence

@[expose] public section

/-! # Convertibility of SKI terms

An instance is a pair of SKI terms. `DecisionProblem` asks whether the two terms are
convertible, that is, whether they have a common reduct under Cslib's reduction `Red`. By
confluence (`join_mRed_equivalence`) this is the equivalence closure of `Red`
(`decisionProblem_iff_eqvGen`), which Hindley and Seldin call weak equality.
`SKIConvProblem` names it.

## References

* [J. R. Hindley, J. P. Seldin,
  *Lambda-Calculus and Combinators: An Introduction*][HindleySeldin2008]
-/

namespace DiagonaLean.SKIConv

open Cslib SKI Relation

/-- `DecisionProblem i` holds iff the two terms of `i` have a common reduct. -/
def DecisionProblem (i : SKI × SKI) : Prop := Join (ReflTransGen Red) i.1 i.2

/-- Convertibility of SKI terms. -/
abbrev SKIConvProblem : SKI × SKI → Prop := DecisionProblem

/-- Two SKI terms have a common reduct iff they are related by `EqvGen Red`. -/
theorem decisionProblem_iff_eqvGen (i : SKI × SKI) : DecisionProblem i ↔ EqvGen Red i.1 i.2 := by
  obtain ⟨x, y⟩ := i
  show Join (ReflTransGen _) x y ↔ EqvGen _ x y
  constructor
  · rintro ⟨c, h₁, h₂⟩
    exact .trans _ _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ h₁)
      (.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ h₂))
  · intro h
    exact join_mRed_equivalence.eqvGen_iff.1
      (EqvGen.mono (fun a b h => ⟨b, .single h, .refl⟩) _ _ h)

end DiagonaLean.SKIConv
