```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `Rabin`: Winner Determination in Rabin's Game
## Problem Statement
Player I chooses a natural number `i`, Player II sees it and replies with `j`, and Player I chooses a final number `k`. Player I wins exactly when `g k = i + j` (`PlayerIWins`). Given a finite program `c : PayoffCode` for a primitive recursive payoff `g = c.eval`, does Player I have a winning strategy? This is `DecisionProblem c` in `Basic.lean`. The programs compute exactly the primitive recursive functions (`PayoffCode.eval_primrec`, `exists_payoffCode`); besides the primitive recursive schemes they have a bounded simulation instruction, which makes the reduction from halting a single constructor.

## Layout
* `Basic.lean`: the game, payoff programs, and the problem.
* `FixedGame.lean`: Rabin's theorem (`rabin_game`). For the primitive recursive rule `rabinFunction`, Player II has a winning strategy, but no computable strategy wins for Player II.
* `Strategies.lean`: Player I wins iff the complement of the range of `g` is finite (`hasWinningI_iff_finite_compl`), so exactly one player has a winning strategy (`winningII_iff_not_hasWinningI`). For computable `g`, a winning Player I has a computable final response (`exists_computable_last`), and Player II wins computably iff the complement of the range contains an infinite computably enumerable set (`computable_winningII_iff_infinite_range`).
* `Reductions/Halt_to_Rabin.lean`: the reduction function `haltToRabin` and its correctness, `HaltProblem ⪯_s[haltToRabin] DecisionProblem` (`halt_reducesto_rabin_spec`). See `Reductions/README.md`.
* `SynthHardness.lean`: winner determination is synthetically halting-hard (`Rabin.synthFromHalt`).
* `Undecidable.lean`: it is undecidable (`Rabin.not_computablePred`), so no Turing machine decides it under any computable encoding (`Rabin.not_machineDecidable`). The proof reduces from self-halting, not from `HaltCanon`, so there is no `HaltReduction` and no `halt_results`.
* `ComputableStrategy.lean`: no Turing machine decides whether Player II has a computable winning strategy, even when it only has to answer on programs for which Player II has a winning strategy (`not_machineDecidable_promised_strategy`). The payoff `cutoff d` agrees with `rabinFunction` until the simulation of `d` halts and is zero afterwards; Player II wins every cutoff game, and wins it computably iff the simulation halts (`cutoff_spec`). A promise problem is not a predicate, so the statement does not use `MachineDecidable`.

## Proof sketch
For program number `e`, `rabinFunction` reserves the opening `2e + 2`. On a final move coding `(e, t)` it runs program `e` on its opening for `t` steps and, if the run returns `j`, scores `2e + 2 + j`. Every computable strategy has a program number, and some bound `t` recovers its reply at its opening, which gives Player I a winning last move. For an opening `i`, only the programs `0, …, i` score in the interval from `i + 1` to `2i + 2`, which has `i + 2` elements, so some number `n` there is not a value of `rabinFunction`; the reply `n - i` wins for Player II.

The halting reduction `haltToRabin` sends a machine and an input to the program that returns `k` when the machine halts within `k` steps, and zero otherwise. If the machine halts by step `t`, Player I opens with `t` and answers `j` with `t + j`. If it runs forever, the payoff is zero and Player II wins with the reply `1`.

## References
* M. O. Rabin, *Effective computability of winning strategies* (1957)
