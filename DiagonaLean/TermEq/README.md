```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `TermEq`: Equality in Pre-Kleene Algebra with Commutativity
## Problem Statement
Given two expressions `e₁ e₂ : RExp (α ⊕ α)` over the doubled alphabet, in which every left letter `.inl a` commutes with every right letter `.inr b` (`DComm`), is `e₁ = e₂` provable in pre-Kleene algebra with these commutations, that is, are `e₁` and `e₂` equal in `T Σ̈`? `TermEqProblem` fixes the alphabet `Σ = {0, 1}`.
