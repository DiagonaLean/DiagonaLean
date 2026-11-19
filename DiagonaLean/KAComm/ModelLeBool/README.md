```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.ModelLeBool`: Inclusion in `L Σ̈` over `{0, 1}`
## Problem Statement
Given two expressions `e f : RExp (Bool ⊕ Bool)` over the doubled alphabet, is the language of `e` contained in the language of `f` in the model `TD.pl` (`TD.pl (mk e) ≤ TD.pl (mk f)`)? Under `TD.pl`, a left letter `a` denotes `{(a, ε)}` and a right letter `b` denotes `{(ε, b)}`, so every left letter commutes with every right letter. This is inclusion in `L Σ̈` for `Σ = {0, 1}`.
