```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `TeamGame`: Team Games with Imperfect Information
## Problem Statement
A team game is a finite game graph over natural numbers: an initial position, a list of actions, edges `(v, a₀, a₁, v')` labelled by one action of each of two players, an observation of each position for each player, and a list of goal positions (`Game`). In each round both players choose an action at the same time and Nature picks any successor along an edge labelled with the pair. Each player sees only its own observations, so a strategy maps the sequence of its observations to an action (`IsPlay`). The reachability problem asks whether the two players have strategies, choosing listed actions, such that every play visits a goal position (`ReachProblem` in `Basic.lean`); the safety problem asks whether they have strategies such that no play visits one (`SafetyProblem`). A play cannot continue from a position with no edge for the chosen actions, so a dead end counts for the team; the games built by the reduction have no dead ends.

## Layout
* `Basic.lean`: games, plays, and the two problems.
* `Machine.lean`: the rows of a list machine (`Foundations/Computability/ListMachine.lean`) as sequences of cells, the local rule that computes a row from the one before (`row_next`), and the tableau of a run, which has a halting head iff the machine halts (`halts_iff_tab`).
* `Construction.lean`: the game of a list machine, with positions and actions as Lean types, in two variants (`Variant`), and the team's winning conditions (`WinReach`, `WinSafety`).
* `Correctness.lean`: the checks as functions of the players' outputs, and the plays that show what safe strategies output.
* `Winning.lean`: the team wins the reachability variant iff the machine halts (`winReach_iff_halts`), and the safety variant iff it does not halt (`winSafety_iff_not_halts`).
* `Coding.lean`: a game given by a successor function on finitely many positions, coded as a `Game ℕ` (`codeGame`, `reachProblem_codeGame_iff`, `safetyProblem_codeGame_iff`).
* `Finite.lean`: the positions and actions of the game of a list machine as finite lists, closed under successors (`succs_closed`).
* `Reductions/Halt_to_TeamGame.lean`: `HaltProblem ⪯_s ReachProblem` (`halt_reducesto_teamReach_spec`) and `HaltProblem ⪯_s Complement SafetyProblem` (`halt_reducesto_not_teamSafety_spec`). See `Reductions/README.md`.
* `SynthHardness.lean`: the reachability problem and the complement of the safety problem are synthetically halting-hard (`TeamGame.synthFromHalt`, `TeamGame.synthComplFromHalt`).

## Proof sketch
Nature picks one of three checks in secret and waits; both players see nothing while it waits. In the Init check, player 1 is triggered at round 1 and must output the initial row of the machine, one cell per round, then `fin`. In the Eq check, both players are triggered at the same round and must output the same row. In the Succ check, player 0 is triggered one round before player 1, and player 1 must output the row after player 0's by the local rule. A position of the game records what the check needs, so a wrong output leads to a failed check. A player's observations after its trigger at round `m` are the same in every check, so its output depends only on `m`. Hence safe strategies output row `m - 1` of the tableau after a trigger at round `m`, by induction on `m` (`rows_of_safe`).

In the safety variant, an output halting head is losing. If the machine halts at row `t`, the Eq check at round `t + 1` reaches a halting head, so the team loses; if it does not halt, outputting the rows of the tableau passes every check. In the reachability variant, every passed check is winning, and player 0 can stop the waiting; this triggers both players for an Eq check that also needs a halting head. Player 0 sees nothing before its stop round `n`, so `n` is fixed by its strategy, and player 1 cannot tell the stop check from the Succ check that triggers player 0 at round `n`; so the stop check forces row `n` to have a halting head. A team that never stops loses to Nature waiting forever.

The statement is a version of the results of Peterson and Reif on multiple-person games, and of Pnueli and Rosner on distributed synthesis. The game follows the outline of the undecidability argument for two players against Nature in a 2010 talk by Berwanger and Kaiser. The talk gives an outline; the complete construction and proofs here, including the stop action of the reachability variant, were written for this library. Only the problems where the game depends on the machine are formalized here; no fixed game is shown undecidable, and there is no machine-level statement.

## References
* G. L. Peterson, J. H. Reif, *Multiple-person alternation*, FOCS 1979
* A. Pnueli, R. Rosner, *Distributed reactive systems are hard to synthesize*, FOCS 1990
* D. Berwanger, Ł. Kaiser, *Information tracking in distributed games*, talk at ACTS 2010 (slides)
