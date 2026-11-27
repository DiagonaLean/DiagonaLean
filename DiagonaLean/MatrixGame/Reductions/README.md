```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `MatrixGame.Reductions`: Zero Reachability in an Alternating Matrix Game Reductions
1. [`MatMort ⪯_s MatrixGame`](#matmort-ₘ-matrixgame)

## `MatMort ⪯_s MatrixGame`
`signGame moves` is the arena where Eve plays `moves` and Adam plays `1` or `-1`. By induction on the deadline, Eve can force zero from `p` within `n` rounds iff some word `w` over `moves` of length at most `n` has `p * w.prod = 0` (`winsWithin_signGame_iff`): Eve plays the first letter of `w`, and either sign of Adam leaves a product that `w.tail` still sends to zero; conversely the play against the reply `1` gives the word. With `forceZero_iff_exists_bound`, `matMort_reducesto_matrixGame_spec` gives `MatMort.DecisionProblem ⪯_s[signGame] MatrixGame.DecisionProblem`, packaged as `MatrixGame.synthFromMatMort`.

### Undecidability
`Undecidable.lean` collects `MatrixGame.synthFromHalt`: the matrix game is synthetically halting-hard, by `undec from MatMort.DecisionProblem`, which composes `MatMort.synthFromHalt` with `MatrixGame.synthFromMatMort`. `MachineLevel.lean` proves `not_computablePred_matrixGame` and `not_machineDecidable_matrixGame` with the same tactic, using `computable_signGame`.
