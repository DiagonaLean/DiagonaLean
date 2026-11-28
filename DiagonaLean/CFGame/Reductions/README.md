```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `CFGame.Reductions`: Active Context-Free Games Reductions
1. [`ListHalt ⪯ₘ CFGame`](#listhalt-ₘ-cfgame)

## `ListHalt ⪯ₘ CFGame`
An instance of `ListHalt` (`Foundations/Computability/ListHalt.lean`) is a program `p` of a list machine on numeric states, a start state `q₀` and a tape. The machine never leaves the finite list `ListHalt.states p q₀`, so it is the renaming by `Subtype.val` of a machine `actOnStates p q₀` on the finite type `ProgStates p q₀` of these states (`act_eq_mapAct`), and the two halt together (`ListMachine.halts_mapCfg_iff`). Juliet wins the simulation game of the machine on `ProgStates p q₀` from the word of a configuration iff the machine halts from it (`Simulation.wins_iff_halts`), and renaming letters injectively does not change the winner (`wins_map_iff`). Renamed to numbers, that game is the game of the machine of `p` on the numeric states (`rules_mapQ`, `target_mapQ`, `cfgWord_mapQ`), which `listToCFGame bl` builds directly on codes (`rulesC`, `targetC`, `cfgWordC`). So `listHalt_reducesto_cfGame_spec` gives `ListHalt.DecisionProblem bl ⪯_s[listToCFGame bl] CFGame.DecisionProblem`, and `listToCFGame bl` is primitive recursive (`listToCFGame_prim`).

### Undecidability
`SynthHardness.lean` composes the link with `ListHalt.synthFromHalt` (`CFGame.synthFromHalt`). `Undecidable.lean` composes it with `ListHalt.fromHalt` (`CFGame.fromHalt`) and states, by `halt_results`, `CFGame.haltHard`, `CFGame.not_computablePred` and `CFGame.not_machineDecidable`: the combined decision problem for context-free games over natural-number letters is halting-hard, undecidable, and not decided by any Turing machine under any computable encoding.
