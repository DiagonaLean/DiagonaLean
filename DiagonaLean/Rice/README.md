```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kshitij Salunke, Aalok Thakkar, Claude Opus
```

# `Rice`: Rice's Problem

## Problem Statement

Fix a set `C : Set (ℕ →. ℕ)` of partial functions. Given a program `c : Nat.Partrec.Code`, is the function it computes in `C` (`c.eval ∈ C`)? The answer depends only on `c.eval`, so programs that compute the same function get the same answer. `C` is non-trivial (`IsNontrivial`) if some program computes a function in `C` and some program computes a function not in `C`; equivalently, `C` contains a partial recursive function and misses one (`isNontrivial_iff`), the hypotheses of Mathlib's `ComputablePred.rice`. Rice's theorem says that the problem is undecidable for every non-trivial `C`.

## Results

* `not_computablePred_rice`: for non-trivial `C`, `RiceProblem C` is not a `ComputablePred` (Mathlib's `ComputablePred.rice`).
* `not_machineDecidable_rice`: for non-trivial `C`, no `SingleTapeTM Bool` decides `RiceProblem C` under any computable encoding of programs, such as `encUnary` (through `Foundations/Computability/MachineBridge.lean`).
* `undecidableRice`, `undecidableRiceCompl`: `HaltProblem` reduces to `RiceProblem C` when the nowhere-defined function is not in `C`, and to its complement when it is.
