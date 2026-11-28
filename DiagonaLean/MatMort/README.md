```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
```
# `MatMort`: The `3 × 3` Matrix Mortality Problem
## Problem Statement
Given a finite set `Ms : Finset (Matrix (Fin 3) (Fin 3) ℤ)` of `3 × 3` integer matrices, does there exist a finite sequence of matrices from `Ms` (with repetition) whose product is the zero matrix? This is `DecisionProblem Ms` in `Basic.lean`.

## Layout
* `Basic.lean`: the problem.
* `Reductions/PCP_to_MatMort.lean`: PCP over `{2, 3}` many-one reduces to matrix mortality through `matImage` (`pcp_reducesto_matMort_spec`). See `Reductions/README.md`.
* `Primrec.lean`: the reduction function `matImage` is primitive recursive (`matImage_primrec`).
* `SynthHardness.lean`: matrix mortality is synthetically halting-hard (`MatMort.synthFromHalt`).
* `Undecidable.lean`: the halting reduction `MatMort.fromHalt`, proved computable, and from it `MatMort.haltHard`, `MatMort.not_computablePred` and `MatMort.not_machineDecidable` (no Turing machine decides it under any computable encoding).
* `RE.lean`: matrix mortality is recursively enumerable (`MatMort.rePred`), by a search over lists of matrices for one drawn from the set with product zero; with `MatMort.haltHard`, it is exactly as hard as the halting problem: complete for the r.e. problems (`MatMort.complete`) and many-one equivalent to the matrix game (`Degrees.matMort_equiv_matrixGame`, `Degrees/Matrices.lean`).
