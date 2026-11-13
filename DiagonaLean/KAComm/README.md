```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm`: Kleene Algebra with Commutativity Conditions
## Problem Statement
Given two expressions `e₁ e₂ : RExp (α ⊕ α)` over the doubled alphabet, in which every left letter `.inl a` commutes with every right letter `.inr b` (`DComm`), is `e₁ = e₂` provable in pre-Kleene algebra with these commutations (`TermEq`, equality on `T Σ̈`), provable in Kleene algebra with these commutations (`KATermEq`, equality on `K Σ̈`), or true in the language model (`LangEq`, equality on `L Σ̈`)? `TermEqProblem`, `KATermEqProblem` and `LangEqProblem` fix the alphabet `Σ = {0, 1}`.
