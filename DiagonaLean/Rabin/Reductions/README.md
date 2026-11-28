```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `Rabin.Reductions`: Winner Determination in Rabin's Game Reductions
1. [`Halt ⪯_s Rabin`](#halt-ₘ-rabin)

## `Halt ⪯_s Rabin`
`haltToRabin` sends a machine and an input to the payoff program `.bounded (dataOf p)`, which returns its argument `k` when the machine halts within `k` steps, and zero otherwise. Player I wins the game of a bounded program iff its test succeeds at some bound (`winner_bounded_iff`): Player I opens with that bound `t` and answers `j` with `t + j`, and a halted simulation stays halted. Otherwise the payoff is zero and the reply `1` wins for Player II (`winningII_of_not_halts`). `halt_reducesto_rabin_spec` gives `HaltProblem ⪯_s[haltToRabin] Rabin.DecisionProblem`, packaged as `Rabin.synthFromHalt`.

### Undecidability
`SynthHardness.lean` states the reduction as `Rabin.synthFromHalt`: winner determination for payoff programs is synthetically halting-hard. `Undecidable.lean` proves `Rabin.not_computablePred` and `Rabin.not_machineDecidable`; they reduce from self-halting through the same bounded programs, not from `HaltCanon`, so there is no `HaltReduction` for Rabin's game yet.
