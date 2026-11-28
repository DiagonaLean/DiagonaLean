```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `TeamGame.Reductions`: Team Games with Imperfect Information Reductions
1. [`Halt ⪯_s DecisionProblem`](#halt-ₘ-decisionproblem)
2. [`Halt ⪯_s ¬ DecisionProblemSafety`](#halt-ₘ--decisionproblemsafety)

## `Halt ⪯_s DecisionProblem`
For a machine that never writes a blank and never moves left at the left end of its tape, the machine halts on `w` iff its list machine halts from the initial configuration (`ListMachine.halts_iff` in `Foundations/Computability/ListMachine.lean`). `haltToTeamGame` normalises the machine and its input (`Foundations/Computability/Normalize/`), so that both conditions hold, takes the game of the normalised list machine (`succs`, `observe` in `Construction.lean`), lists its positions and actions (`allPos`, `allMoves` in `Finite.lean`), and codes them as natural numbers with their derived `Encodable` codes (`codeGame` in `Coding.lean`). The reachability variant, `haltToTeamReach`, has the passed check as its goal. The team wins it iff the list machine halts (`winReach_iff_halts`), so `halt_reducesto_teamReach_spec` gives `HaltProblem ⪯_s[haltToTeamReach] DecisionProblem`, packaged as `TeamGame.synthFromHalt`.

## `Halt ⪯_s ¬ DecisionProblemSafety`
The safety variant, `haltToTeamSafety`, has the failed check and the halting head as its bad positions. The team wins it iff the list machine does not halt (`winSafety_iff_not_halts`), so `halt_reducesto_not_teamSafety_spec` gives `HaltProblem ⪯_s[haltToTeamSafety] Complement DecisionProblemSafety`, packaged as `TeamGame.synthComplFromHalt`.

### Undecidability
`SynthHardness.lean` collects `TeamGame.synthFromHalt` (team reachability games over ℕ are synthetically halting-hard) and `TeamGame.synthComplFromHalt` (the complement of team safety games over ℕ is synthetically halting-hard). A machine-level statement (`¬ MachineDecidable`) needs a reduction proved computable. The route is a reduction from `ListHalt`, as for `CFGame`; its open part is a proof that the checker `chk`, which matches on a position and two moves, is primitive recursive.
