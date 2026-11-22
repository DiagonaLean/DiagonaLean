```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
```
# `MPCP`: The Modified Post's Correspondence Problem
## Problem Statement
Given a distinguished tile `c : Tile α` and a finite stack `P : Stack α`, does there exist a sequence `A` of tiles from `c :: P` (with repetition) such that `c.top ++ τ1 A = c.bot ++ τ2 A` where `τ1` and `τ2` concatenate the top and bottom words of `A` respectively?

## Layout
* `Basic.lean`: the problem; solvability depends only on the set of tiles (`mpcp_congr`).
* `AlphabetLift.lean`: encoding the tiles by a code (`Foundations/Codes/`) preserves and reflects solvability (`decisionProblem_encode_iff`), so MPCP is a functor on codes (`mpcpFunctor`) and many-one reduces to MPCP over any alphabet with two distinct letters (`mpcpAlphabetLift`). An injective renaming of letters is such a code (`mpcp_map_iff`).
* `Reductions/Halt_to_MPCP.lean`: the reduction, for machines that never write a blank and never move left at the left end of the tape (`halt_iff_mpcp`), and `HaltProblem ⪯_s` MPCP over `Alpha ℕ Sym2` (`haltReducesMPCP`).
* The two conditions are removed by the normalisation of Turing machines in `Foundations/Computability/Normalize/`: `normTM` turns any machine over `Bool` into one over `Bool × Bool` that satisfies them and halts on the encoded input `encInput w` exactly when the original halts on `w` (`halts_normTM_iff`). The reductions to MPCP, PCP and string rewriting all use it.
* `Undecidable.lean`: MPCP is synthetically halting-hard over `Alpha ℕ Sym2` (`undecidableMPCP`), and over every alphabet with two distinct letters (`undecidableMPCPOf`), for instance over `Bool` (`undecidableMPCPBool`).
* `MachineLevel.lean`: MPCP is not a computable predicate (`not_computablePred_mpcp`), so no Turing machine decides it under any computable encoding (`not_machineDecidable_mpcp`); the same holds over any nontrivial `Primcodable` alphabet (`not_computablePred_mpcpOf`, `not_machineDecidable_mpcpOf`). `instC` builds the MPCP instance of a machine from its code, on input the code itself, and is primitive recursive (`instC_prim`); a machine halts on its own code iff that instance is solvable (`selfHalt_iff_instC`).
