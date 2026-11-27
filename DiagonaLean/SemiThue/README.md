```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `SemiThue`: The Word Problem for String Rewriting Systems
## Problem Statement
Given a string rewriting system (semi-Thue system) `R : SRS T`, a finite list of rules `l ⟶ r` between words over `T`, and two words `u` and `v`, does `u` rewrite to `v` in finitely many steps, each replacing one occurrence of a left side by its right side? This is `WordProblem R u v`, that is `u ↠[R] v`, in `Basic.lean`. Partially applied, `WordProblem R u` is the set of words that `u` rewrites to; `ToEmpty R u` is the case `v = []`, and `PosWordProblem R u v` the restriction to systems whose left sides are all non-empty. The one-argument forms `DecisionProblem (R, u, v)`, `ToEmptyProblem (R, u)` and `DecisionProblemPos (R, u, v)`, which the reductions and the computability statements use, are the same problems (`decisionProblem_mk` and its companions, by `Iff.rfl`). The answer depends only on the set of rules (`wordProblem_congr`).

Words (`Word T`, a list of letters), rules (`Rule T`, with fields `lhs` and `rhs`), systems, one step (`u ⭢[R] v`, an inductive relation as Mathlib's `ContextFreeRule.Rewrites`) and derivability (`u ↠[R] v`, Mathlib's `ReflTransGen` of a step) are defined in `Foundations/Rewriting/SRS.lean`; a stack machine checking derivations is in `Foundations/Grammar/Rewriting.lean`.

## Layout
* `Basic.lean`: the problems, curried (`WordProblem`, `ToEmpty`, `PosWordProblem`) and on instances (`DecisionProblem`, `ToEmptyProblem`, `DecisionProblemPos`), and their unfolding into Mathlib's terms (`wordProblem_iff`).
* `Reductions/Halt_to_SemiThue.lean`: a machine halts iff its configuration string rewrites to the empty string (`halt_iff_derives`), so `haltToSemiThue` reduces `HaltProblem` to the word problem over `Alpha ℕ Sym2` and to its restriction (`halt_reducesto_semiThue_spec`, `halt_reducesto_semiThuePos_spec`). See `Reductions/README.md`.
* `Reductions/HaltCanon_to_SemiThue.lean`: the rewriting system of a transition table (`codeRules`, `toEmptyOf`); a machine halts on an input iff the start string of its table rewrites to the empty string (`halts_iff_toEmptyN`). On canonical machines this gives the reductions `canonToEmpty` and `canonWord` from `HaltCanon`, primitive recursive.
* `AlphabetLift.lean`: the restricted problem is a functor on synchronizing codes (`semiThueFunctor`), and `posToWord` returns to the plain word problem.
* `Undecidable.lean`: the word problem is halting-hard, by a reduction from `HaltCanon` proved computable, over `Alpha ℕ Sym2` (`SemiThue.posFromHalt`, for systems with non-empty left sides, and `SemiThue.toEmptyFromHalt`) and over every alphabet with two distinct letters (`SemiThue.fromHaltOver`, `SemiThue.fromHaltBool`). So, by `halt_results`, no Turing machine decides it under any computable encoding (`SemiThue.not_machineDecidable` over every nontrivial alphabet, `SemiThue.Pos.not_machineDecidable`, `SemiThue.ToEmpty.not_machineDecidable`).
* `SynthHardness.lean`: the word problem is synthetically halting-hard over `Alpha ℕ Sym2` (`SemiThue.synthFromHalt`), and over every alphabet with two distinct letters (`SemiThue.synthFromHaltOver`), for instance over `Bool` (`SemiThue.synthFromHaltBool`).
* `RE.lean`: the word problem is recursively enumerable (`SemiThue.rePred`), by a search for a program of the stack machine `srsSys` that checks the derivation; with `SemiThue.haltHard`, it is exactly as hard as the halting problem.

## Proof sketch
The transition tiles of the MPCP reduction (`MPCP/Reductions/Halt_to_MPCP.lean`) pair a window of a configuration with its successor; read as rules `top → bot`, they rewrite the configuration string `# … q a … #` one machine step at a time. With the absorb tiles (`a h⊥ → h⊥`, `h⊥ a → h⊥`) and a final rule `# h⊥ # → []`, they form `tmRules tm`.

* **Forward** (`derives_of_halts`): each step of the run is one rewrite (`step_block`), from the configuration lemmas of the MPCP reduction; after halting, the absorb rules and the final rule erase the string (`derives_halted`).
* **Backward** (`halts_of_derives`): a configuration string has exactly one state marker, and the left side of every rule contains a marker, so a rewrite happens at the marker (`split_mark`). By determinism of the machine it is the machine's step (`step_inv`), except for an interior right move at the right end, which leaves the marker before `#`: a string from which nothing can be rewritten (`not_derives_stuck`), or the halting marker, when the machine has halted.

The machine is first normalised (`Foundations/Computability/Normalize/`), so that it never writes a blank and never moves left at the left end. At machine level, the system is read off a transition table, as `MPCP.Reduction.instOf` reads the tiles (`codeRules`, `toEmptyOf`), and is the renaming of the normalised machine's system (`mem_codeRules`); renaming letters injectively keeps derivability (`Codes.derives_mapRules_iff`, the code theorem `derives_encode_iff` for a one-letter code).

## References
* E. L. Post, *Recursive unsolvability of a problem of Thue* (1947)
* A. A. Markov, *On the impossibility of certain algorithms in the theory of associative systems* (1947)
