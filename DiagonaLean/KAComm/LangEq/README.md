```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.LangEq`: Equality on `L Σ̈`
## Problem Statement
Given two expressions `e f : RExp (ℕ ⊕ ℕ)` over the doubled alphabet, do `e` and `f` have the same language in the model `TD.pl` (`TD.pl (mk e) = TD.pl (mk f)`)? Under `TD.pl`, a left letter `a` denotes `{(a, ε)}` and a right letter `b` denotes `{(ε, b)}`, so every left letter commutes with every right letter. This is equality on `L Σ̈` for `Σ = ℕ`.
