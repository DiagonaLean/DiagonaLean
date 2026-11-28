```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
```
# `MPCP`: The Modified Post's Correspondence Problem
## Problem Statement
Given a distinguished tile `c : Tile α` and a finite stack `P : Stack α`, does there exist a sequence `A` of tiles from `c :: P` (with repetition) such that `c.top ++ τ1 A = c.bot ++ τ2 A` where `τ1` and `τ2` concatenate the top and bottom words of `A` respectively?

## Layout
* `Basic.lean`: the problem, `DecisionProblem`, on an instance given as a pair `(c, P)`, and `Solvable c P`, the same predicate curried, which the proofs use (`decisionProblem_iff`); solvability depends only on the set of tiles (`mpcp_congr`).
* `AlphabetLift.lean`: encoding the tiles by a code (`Foundations/Codes/`) preserves and reflects solvability (`decisionProblem_encode_iff`), so MPCP is a functor on codes (`mpcpFunctor`) and many-one reduces to MPCP over any alphabet with two distinct letters (`MPCP.synthAlphabetLift`). An injective renaming of letters is such a code (`mpcp_map_iff`).
* `Reductions/Halt_to_MPCP.lean`: the reduction, for machines that never write a blank and never move left at the left end of the tape (`halt_iff_mpcp`).
* The two conditions are removed by the normalisation of Turing machines in `Foundations/Computability/Normalize/`: `normTM` turns any machine over `Bool` into one over `Bool × Bool` that satisfies them and halts on the encoded input `encInput w` exactly when the original halts on `w` (`halts_normTM_iff`). The reductions to MPCP, PCP and string rewriting all use it.
* `Reductions/HaltCanon_to_MPCP.lean`: the MPCP instance of a transition table, built numerically and primitive recursive (`instOf`); a machine halts on an input iff the instance of its table on that input is solvable (`halts_iff_mpcpN`). On canonical machines the table is primitive recursive, and reading it off gives the reduction `canonInst` from `HaltCanon` (`haltCanon_iff_mpcp`, `canonInst_prim`).
* `SynthHardness.lean`: MPCP is synthetically halting-hard over `Alpha ℕ Sym2` (`MPCP.synthFromHalt`), and over every alphabet with two distinct letters (`MPCP.synthFromHaltOver`), for instance over `Bool` (`MPCP.synthFromHaltBool`).
* `Undecidable.lean`: MPCP over `Alpha ℕ Sym2` is halting-hard, with a reduction proved computable (`MPCP.fromHalt`). Over any alphabet with two distinct letters: `MPCP.fromHaltOver b0 b1 hne`, `MPCP.fromHaltBool`. Hence, over any nontrivial `Primcodable` alphabet, MPCP is halting-hard (`MPCP.haltHard`), undecidable (`MPCP.not_computablePred`), and no Turing machine decides it under any computable encoding (`MPCP.not_machineDecidable`), all stated by `halt_results`.
* `RE.lean`: MPCP is recursively enumerable over every `Primcodable` alphabet (`MPCP.rePred`), by a search over stacks of tiles that complete the start tile; with `MPCP.haltHard`, it is exactly as hard as the halting problem.
