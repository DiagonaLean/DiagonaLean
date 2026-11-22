```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `SemiThue`: The Word Problem for String Rewriting Systems
## Problem Statement
Given a string rewriting system (semi-Thue system) `R : SRS T`, a list of rules `l → r` between strings over `T`, and two strings `u` and `v`, does `u` rewrite to `v` in some number of steps, each replacing one occurrence of a left side by its right side? This is `DecisionProblem (R, u, v)` in `Basic.lean`; `ToEmptyProblem (R, u)` is the case `v = []`. The string rewriting systems themselves, and a stack machine checking their derivations, are in `Foundations/Grammar/Rewriting.lean`.

## Layout
* `Basic.lean`: the problem.
* `Reductions/Halt_to_SemiThue.lean`: a machine halts iff its configuration string rewrites to the empty string (`halt_iff_derives`).
* `Undecidable.lean`: `HaltProblem ⪯ₘ` the word problem (`haltReducesSemiThue`), so it is `Undecidable` (`undecidableSemiThue`).
* `MachineLevel.lean`: no Turing machine decides it under any computable encoding (`not_machineDecidable_semiThue`, `not_machineDecidable_toEmpty`).

## Proof sketch
The transition tiles of the MPCP reduction (`MPCP/Reductions/Halt_to_MPCP.lean`) pair a window of a configuration with its successor; read as rules `top → bot`, they rewrite the configuration string `# … q a … #` one machine step at a time. With the absorb tiles (`a h⊥ → h⊥`, `h⊥ a → h⊥`) and a final rule `# h⊥ # → []`, they form `tmRules tm`.

* **Forward** (`derives_of_halts`): each step of the run is one rewrite (`step_block`), from the configuration lemmas of the MPCP reduction; after halting, the absorb rules and the final rule erase the string (`derives_halted`).
* **Backward** (`halts_of_derives`): a configuration string has exactly one state marker, and the left side of every rule contains a marker, so a rewrite happens at the marker (`split_mark`). By determinism of the machine it is the machine's step (`step_inv`), except for an interior right move at the right end, which leaves the marker before `#`: a string from which nothing can be rewritten (`not_derives_stuck`), or the halting marker, when the machine has halted.

The machine is first normalised (`MPCP/Normalize/`), so that it never writes a blank and never moves left at the left end. At machine level, the system is read off the machine's code, as `MPCP.MachineLevel.instC` reads the tiles (`codeRules`, `toEmptyCode`), and is the renaming of the normalised machine's system (`mem_codeRules`); renaming letters injectively keeps derivability (`SRS.derives_map_iff`).

## References
* E. L. Post, *Recursive unsolvability of a problem of Thue* (1947)
* A. A. Markov, *On the impossibility of certain algorithms in the theory of associative systems* (1947)
