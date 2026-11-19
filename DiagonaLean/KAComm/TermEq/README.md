```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.TermEq`: Equality on `T Σ̈`
## Problem Statement
Given two expressions `e f : RExp (ℕ ⊕ ℕ)` over the doubled alphabet, in which every left letter `.inl a` commutes with every right letter `.inr b` (`DComm`), is `e = f` provable in pre-Kleene algebra with these commutations (`RExp.Equiv DComm e f`)? This is equality in the free model `T Σ̈` for `Σ = ℕ`. Pre-Kleene algebra has no induction axioms.
