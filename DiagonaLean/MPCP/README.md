```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
```
# `MPCP`: The Modified Post's Correspondence Problem
## Problem Statement
Given a distinguished tile `c : Tile α` and a finite stack `P : Stack α`, does there exist a sequence `A` of tiles from `c :: P` (with repetition) such that `c.top ++ τ1 A = c.bot ++ τ2 A` where `τ1` and `τ2` concatenate the top and bottom words of `A` respectively?

## Layout
* `Basic.lean`: the problem.
* `Reductions/Halt_to_MPCP.lean`: the reduction, for machines that never write a blank and never move left at the left end of the tape.
* The two conditions are removed by the normalisation of Turing machines in `Foundations/Computability/Normalize/`: `normTM` turns any machine over `Bool` into one over `Bool × Bool` that satisfies them and halts on the encoded input `encInput w` exactly when the original halts on `w` (`halts_normTM_iff`). The reductions to MPCP, PCP and string rewriting all use it.
* `Undecidable.lean`: the composition `HaltProblem ⪯ₘ MPCP`.
* `MachineLevel.lean`: MPCP is not a computable predicate (`not_computablePred_mpcp`), so no Turing machine decides it under any computable encoding (`not_machineDecidable_mpcp`). `instC` builds the MPCP instance of a machine from its code, on input the code itself, and is primitive recursive (`instC_prim`); a machine halts on its own code iff that instance is solvable (`selfHalt_iff_instC`).
