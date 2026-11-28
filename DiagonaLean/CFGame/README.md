```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `CFGame`: Active Context-Free Games
## Problem Statement
A context-free game is a finite list of rules `a → b :: x` with non-empty right sides and a target language given by a regular expression (`Game`). A letter is a non-terminal if it is the left side of a rule. Juliet and Romeo play on a word: in each round Juliet picks a position holding a non-terminal `a`, and Romeo replaces it by the right side of a rule for `a`. Juliet wins when the word enters the target after some round; a play that never does is won by Romeo. The combined decision problem asks, given a game and a word, whether Juliet has a winning strategy (`DecisionProblem` in `Basic.lean`). Positions of the game are words and the winning condition is reachability, so Juliet wins from `w` iff one of her moves leads into the least set of words that contains the target and is closed under her moves (`Reach`, `Wins`).

## Layout
* `Basic.lean`: games, `Reach`, `Wins` and the problem, and invariance under an injective renaming of letters (`wins_map_iff`).
* `Simulation.lean`: the game of a list machine (`Foundations/Computability/ListMachine.lean`: a deterministic machine whose tape is two lists) and the theorem that Juliet wins from the word of a configuration iff the machine halts from it (`Simulation.wins_iff_halts`).
* `Regular.lean`: regular expressions for finite unions and fixed words, and the languages `A* · m · A*` (`pattern`, `mem_pattern`).
* `Target.lean`: the target of that game as a regular expression (`target`, `mem_target`).
* `Rename.lean`: renaming the states of the machine renames the rules, the target and the configuration words of the game (`rules_mapQ`, `target_mapQ`, `cfgWord_mapQ`).
* `Codes.lean`: regular expressions are `Primcodable`; the rules, target and words of the game on numeric states given directly on codes (`rulesC`, `targetC`, `cfgWordC`), primitive recursive, and equal to the coded constructions.
* `Reductions/ListHalt_to_CFGame.lean`: `ListHalt.DecisionProblem bl ⪯_s DecisionProblem` (`listHalt_reducesto_cfGame_spec`), by a primitive recursive function (`listToCFGame_prim`). See `Reductions/README.md`.
* `SynthHardness.lean`: the combined decision problem is synthetically halting-hard (`CFGame.synthFromHalt`).
* `Undecidable.lean`: the combined decision problem is halting-hard (`CFGame.fromHalt`), and by `halt_results` undecidable and not decided by any Turing machine under any computable encoding (`CFGame.haltHard`, `CFGame.not_computablePred`, `CFGame.not_machineDecidable`).

## Proof sketch
The construction adapts the head encoding of Lemma 4.1 and the objections of Lemma 8.1 of Muscholl, Schwentick and Segoufin to a deterministic machine whose tape grows at `#`. A configuration is the word `$ · left cells · [q,c] · right cells · #`. A move of the head to the right takes three rounds: the head becomes a marker `[q',b,→]`, the next cell (or `#`, which grows the tape) becomes a head `[p,c']` in a state `p` that Romeo chooses, and the marker becomes the written symbol `b`. A wrong state is in the target, so Romeo must choose `p = q'`. Every non-terminal also has a rule to an objection letter. The target accepts a word with one objection exactly when the objection sits where Juliet had to play, and no word with two objections. So Romeo objects to any other move, then objects again at every later move, and Juliet never reaches the target (`not_reach_of_two_le`). Juliet reaches the target exactly when the halt letter appears, that is, when the machine halts.

Only the combined problem is formalized here: the game depends on the machine. The paper also proves undecidability for one fixed game (the data problem), through a universal machine; that is not covered.

## References
* A. Muscholl, T. Schwentick, L. Segoufin, *Active Context-Free Games*, Theory of Computing Systems 39 (2006), Theorem 4.2
