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
* `Normalize/`: removes those two conditions. `normTM` turns any machine over `Bool` into one over `Bool × Bool` that satisfies them and halts on the encoded input `encInput w` exactly when the original halts on `w` (`halts_normTM_iff`). It is used only by the reduction chain from `HaltProblem` through MPCP, here and in `PCP/Reductions/Halt_to_PCP.lean`.
* `Undecidable.lean`: the composition `HaltProblem ⪯ₘ MPCP`.
