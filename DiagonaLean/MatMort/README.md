```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
```
# `MatMort`: The `3 × 3` Matrix Mortality Problem
## Problem Statement
Given a finite set `Ms : Finset (Matrix (Fin 3) (Fin 3) ℤ)` of `3 × 3` integer matrices, does there exist a finite sequence of matrices from `Ms` (with repetition) whose product is the zero matrix? This is `DecisionProblem Ms` in `Basic.lean`.

## Layout
* `Basic.lean`: the problem.
* `Reductions/PCP_to_MatMort.lean`: PCP over `{2, 3}` many-one reduces to matrix mortality (`MatMort.synthFromPCP`). See `Reductions/README.md`.
* `Primrec.lean`: the reduction function `matImage` is primitive recursive (`matImage_primrec`).
* `Undecidable.lean`: matrix mortality is synthetically halting-hard (`MatMort.synthFromHalt`).
* `MachineLevel.lean`: it is not a computable predicate (`not_computablePred_matMort`), so no Turing machine decides it under any computable encoding (`not_machineDecidable_matMort`).
