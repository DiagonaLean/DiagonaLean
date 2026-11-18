```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `SKIConv`: Convertibility of SKI Terms
## Problem Statement
Given two SKI terms `x y : SKI`, are they convertible, that is, do they have a common reduct under Cslib's reduction `Red` (`Join (ReflTransGen Red) x y`)? By confluence this is the equivalence closure of `Red` (`decisionProblem_iff_eqvGen`), which Hindley and Seldin call weak equality.
