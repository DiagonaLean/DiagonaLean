```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `BetaConv`: β-Conversion of λ-Terms
## Problem Statement
Given two locally nameless λ-terms `M N : Term ℕ`, are they β-convertible, that is, do they have a common reduct under Cslib's full β-reduction `FullBeta`? This is `Convertible M N` in `Basic.lean`, which unfolds to `∃ P, ReflTransGen FullBeta M P ∧ ReflTransGen FullBeta N P` (`convertible_iff`, by `Iff.rfl`); partially applied, `Convertible M` is the β-convertibility class of `M`. The one-argument form `DecisionProblem (M, N)` is the same problem (`decisionProblem_mk`). By confluence this is the equivalence closure of `FullBeta` (`convertible_iff_eqvGen`). The relation is `Foundations.LambdaCalculus.Conv` (`Foundations/LambdaCalculus/Conv.lean`, definitions only; its former name `BetaConv` is a deprecated alias). The locally closed terms of `Term ℕ` are the λ-terms up to α-equivalence, and on them this is β-conversion; `FullBeta` takes no step from a term that is not locally closed (`FullBeta.steps_lc_or_rfl`), so on such a term the problem is syntactic equality. Church (1936) proved undecidability for the λI-calculus, where every abstraction uses its variable; this formulation is for the full untyped λ-calculus.

## Results

* `BetaConv.synthFromHalt` (`SynthHardness.lean`): synthetic halting reduction, given a universal code and the race program as arguments.
* `BetaConv.haltHard` (`Undecidable.lean`): β-conversion is halting-hard. The reduction from canonical machines (`canonRed`, `Reductions/HaltCanon_to_BetaConv.lean`) is proved computable (`canonRed_primrec`, through the code `tc`); the constants exist only classically, so `haltHard`, a proposition, obtains them in its proof. From it, `BetaConv.not_computablePred`, `BetaConv.not_machineDecidable` under every computable encoding, and a `HaltHardFact` instance for `hard_reduce_from`.
* `not_machineDecidable_betaConv`, `BetaConv.not_computablePred` (`Undecidable.lean`): the same two negative statements by a machine-level race and the binary encoding `encBeta`.
* `BetaConv.rePred` (`RE.lean`): the problem is recursively enumerable, by a search for a program of the proof search that checks the conversion; with `BetaConv.haltHard`, it is exactly as hard as the halting problem.
