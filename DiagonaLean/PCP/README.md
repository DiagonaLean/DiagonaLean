```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
```
# `PCP`: Post's Correspondence Problem
## Problem Statement
Given a finite list of tiles `P : Stack` over an alphabet `α`, each tile pairing a `top` word with a `bot`tom word, does there exist a non-empty sequence `A` of tiles from `P` (with repetition) such that `τ1 A = τ2 A`, where `τ1` and `τ2` concatenate the top and bottom words of `A` respectively?

## Layout
* `Basic.lean`: the problem.
* `AlphabetLift.lean`: encoding the tiles by a code (`Foundations/Codes/`) preserves and reflects solvability (`decisionProblem_encode_iff`), so PCP is a functor on codes (`pcpFunctor`) and many-one reduces to PCP over any alphabet with two distinct letters (`pcpAlphabetLift`). An injective renaming of letters is such a code (`pcp_map_iff`).
* `Reductions/MPCP_to_PCP.lean`: `MPCP ⪯ₘ PCP` over the extended alphabet `Ext α` (`mpcpReducesPCP`).
* `Reductions/Halt_to_PCP.lean`: `HaltProblem ⪯ₘ` PCP over `Ext (Alpha ℕ Bool)` (`haltReducesPCP`). See `Reductions/README.md`.
* `Primrec.lean`: tiles and `Ext α` are `Primcodable`, and `mpcpToPcp` and `liftInstance` are primitive recursive.
* `Undecidable.lean`: PCP is `Undecidable` over `Ext (Alpha ℕ Bool)` (`undecidablePCP'`), and over every alphabet with two distinct letters (`undecidablePCP`).
* `MachineLevel.lean`: over any nontrivial `Primcodable` alphabet, PCP is not a computable predicate (`not_computablePred_pcp`), so no Turing machine decides it under any computable encoding (`not_machineDecidable_pcp`).
