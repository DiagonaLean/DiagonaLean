```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `SKIConv`: Convertibility of SKI Terms
## Problem Statement
Given two SKI terms `x y : SKI`, are they convertible, that is, do they have a common reduct under Cslib's reduction `Red` (`Join (ReflTransGen Red) x y`)? By confluence this is the equivalence closure of `Red` (`decisionProblem_iff_eqvGen`), which Hindley and Seldin call weak equality.

## Results

* `SKIConv.synthFromHalt` (`Undecidable.lean`): synthetic halting reduction, given a universal code and the race program as arguments.
* `SKIConv.haltHard` (`Hardness.lean`): SKI convertibility is halting-hard. The reduction from canonical machines, `SKIConv.fromHaltWith U C …`, is proved computable (`canonRed_primrec`); the constants `U` and `C` exist only classically, so `haltHard`, a proposition, obtains them in its proof. From it, `SKIConv.not_computablePred` and `SKIConv.not_machineDecidable` under every computable encoding, and a `HaltHardFact` instance, so `hard_reduce_from` can start from SKI convertibility.
* `not_machineDecidable_skiConv`, `not_computablePred_skiConv` (`Undecidable.lean`): the same two negative statements by a machine-level race and the binary encoding `encSKI`.
