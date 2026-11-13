```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `LangEq`: Language Equality with Commutativity
## Problem Statement
Given two expressions `e₁ e₂ : RExp (α ⊕ α)` over the doubled alphabet, in which every left letter `.inl a` commutes with every right letter `.inr b`, do `e₁` and `e₂` have the same language in the model `TD.pl`, that is, are they equal in `L Σ̈`? `LangEqProblem` fixes the alphabet `Σ = {0, 1}`.
