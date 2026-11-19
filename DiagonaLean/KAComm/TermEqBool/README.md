```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.TermEqBool`: Equality on `T Σ̈` over `{0, 1}`
## Problem Statement
Given two expressions `e f : RExp (Bool ⊕ Bool)` over the doubled alphabet, in which every left letter `.inl a` commutes with every right letter `.inr b` (`DComm`), is `e = f` provable in pre-Kleene algebra with these commutations (`RExp.Equiv DComm e f`)? This is equality in the free model `T Σ̈` for `Σ = {0, 1}`. Pre-Kleene algebra has no induction axioms.
