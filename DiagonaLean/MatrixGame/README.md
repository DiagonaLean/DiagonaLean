```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `MatrixGame`: Zero Reachability in an Alternating Matrix Game
## Problem Statement
Eve and Adam each have a finite set of `3 × 3` integer matrices (an `Arena`). Play starts at the identity. In each round Eve right-multiplies the product by one of her matrices, then Adam right-multiplies it by one of his. Can Eve force the product to reach zero in finitely many rounds? This is `EveForcesZero eve adam` in `Basic.lean` (`ForceZero (eve, adam) 1`), and `DecisionProblem G` on an arena. Zero absorbs every later move. If Adam has no matrices, a legal move by Eve wins.

## Layout
* `Basic.lean`: the game, the problem curried (`EveForcesZero eve adam`) and on arenas (`DecisionProblem`, `decisionProblem_mk`).
* `Search.lean`: `winsWithin G n p` searches for a win within `n` rounds. The move sets are finite, so Eve can force zero iff the search succeeds for some `n` (`forceZero_iff_exists_bound`).
* `Reductions/MatMort_to_MatrixGame.lean`: matrix mortality many-one reduces to the matrix game (`MatrixGame.synthFromMatMort`). See `Reductions/README.md`.
* `SynthHardness.lean`: the matrix game is synthetically halting-hard (`MatrixGame.synthFromHalt`).
* `Undecidable.lean`: it is halting-hard by a reduction proved computable (`MatrixGame.fromHalt`), so halting-hard (`MatrixGame.haltHard`), undecidable (`MatrixGame.not_computablePred`), and no Turing machine decides it under any computable encoding (`MatrixGame.not_machineDecidable`), all stated by `halt_results`; already when Adam's moves are `1` and `-1` (`MatrixGame.not_machineDecidable_signGame`).

## Proof sketch
`signGame moves` gives Eve the matrices `moves` and Adam the two signs `1` and `-1`. Each of Adam's moves only changes the sign of the product. If a word over `moves` has product zero, Eve plays its letters in order and the product ends at zero. Conversely, a winning strategy must win against the Adam who always plays `1`, and Eve's moves along that play form a word with product zero. Within a deadline, Eve can force zero in `n` rounds iff a word of length at most `n` has product zero (`winsWithin_signGame_iff`). Matrix mortality is undecidable (`MatMort/`), so the matrix game is too.

## References
* M. S. Paterson, *Unsolvability in 3 × 3 Matrices* (1970)
