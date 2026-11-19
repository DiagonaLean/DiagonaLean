```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.KATermEqBool`: Equality on `K Σ̈` over `{0, 1}`
## Problem Statement
Given two expressions `e f : RExp (Bool ⊕ Bool)` over the doubled alphabet, in which every left letter `.inl a` commutes with every right letter `.inr b` (`DComm`), is `e = f` provable in Kleene algebra with these commutations (`RExp.KAEquiv DComm e f`)? This is equality in the free model `K Σ̈` for `Σ = {0, 1}`. This is the theory of the paper's title.
