```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `BetaConv`: β-Conversion of λ-Terms
## Problem Statement
Given two locally nameless λ-terms `M N : Term ℕ`, are they β-convertible, that is, do they have a common reduct under Cslib's full β-reduction `FullBeta` (`Join (ReflTransGen FullBeta) M N`)? By confluence this is the equivalence closure of `FullBeta` (`decisionProblem_iff_eqvGen`). The locally closed terms of `Term ℕ` are the λ-terms up to α-equivalence, and on them this is β-conversion; `FullBeta` takes no step from a term that is not locally closed (`FullBeta.steps_lc_or_rfl`), so on such a term the problem is syntactic equality. Church (1936) proved undecidability for the λI-calculus, where every abstraction uses its variable; this formulation is for the full untyped λ-calculus.

## Results

* `BetaConv.synthFromHalt` (`Undecidable.lean`): synthetic halting reduction, given a universal code and the race program as arguments.
* `BetaConv.haltHard` (`Hardness.lean`): β-conversion is halting-hard. The reduction from canonical machines, `BetaConv.fromHaltWith U C …`, is proved computable (`canonRed_primrec`, through the code `tc`); the constants exist only classically, so `haltHard`, a proposition, obtains them in its proof. From it, `BetaConv.not_computablePred`, `BetaConv.not_machineDecidable` under every computable encoding, and a `HaltHardFact` instance for `hard_reduce_from`.
* `not_machineDecidable_betaConv`, `not_computablePred_betaConv` (`Undecidable.lean`): the same two negative statements by a machine-level race and the binary encoding `encBeta`.
