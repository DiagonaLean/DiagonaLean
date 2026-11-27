```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `SKIConv`: Convertibility of SKI Terms
## Problem Statement
Given two SKI terms `x y : SKI`, are they convertible, that is, do they have a common reduct under Cslib's reduction `Red`? This is `Convertible x y` in `Basic.lean`, which unfolds to `∃ z, ReflTransGen Red x z ∧ ReflTransGen Red y z` (`convertible_iff`, by `Iff.rfl`); partially applied, `Convertible x` is the convertibility class of `x`. The one-argument form `DecisionProblem (x, y)`, which the reductions and the computability statements use, is the same problem (`decisionProblem_mk`). By confluence this is the equivalence closure of `Red` (`convertible_iff_eqvGen`), which Hindley and Seldin call weak equality. The relation is `Foundations.CombinatoryLogic.Conv` (`Foundations/CombinatoryLogic/Conv.lean`, definitions only); the stack machine that enumerates conversions is in `ProofSearch.lean` there.

## Results

* `SKIConv.synthFromHalt` (`SynthHardness.lean`): synthetic halting reduction, given a universal code and the race program as arguments.
* `SKIConv.haltHard` (`Undecidable.lean`): SKI convertibility is halting-hard. The reduction from canonical machines (`canonRed`, `Reductions/HaltCanon_to_SKIConv.lean`) is proved computable (`canonRed_primrec`); the constants `U` and `C` exist only classically, so `haltHard`, a proposition, obtains them in its proof. From it, `SKIConv.not_computablePred` and `SKIConv.not_machineDecidable` under every computable encoding, and a `HaltHardFact` instance, so `hard_reduce_from` can start from SKI convertibility.
* `not_machineDecidable_skiConv`, `SKIConv.not_computablePred` (`Undecidable.lean`): the same two negative statements by a machine-level race and the binary encoding `encSKI`.
* `SKIConv.rePred` (`RE.lean`): the problem is recursively enumerable, by a search for a program of the proof search that checks the conversion; with `SKIConv.haltHard`, it is exactly as hard as the halting problem.
