```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kshitij Salunke, Aalok Thakkar, Claude Opus
```

# `Rice.Reductions`: Rice's Problem Reductions

1. [`Halt ⪯_s Rice`](#halt-ₘ-rice)

## `Halt ⪯_s Rice`

`HaltProblem` is a search: a machine `M` halts on `w` iff a primitive recursive test of the numeric data of `(M, w)` succeeds for some number of steps (`halt_iff_test` in `Foundations/Computability/HaltSearch.lean`). So `wait n x`, which searches for such a step for the data with code `n` and then returns `x`, is partial recursive (`wait_part`), and some program `w` computes it on `⟪n, x⟫` (`IsWaiter`, `exists_isWaiter`).

Assume that the program `cT` computes a function in `C` and that the nowhere-defined function is not in `C`. The reduction `reduction w cT` sends a `HaltProblem` instance `p` to the program `cT ∘ curry w d`, where `d` is the code of the data of `p`. On input `x` it waits for `p` to halt and then runs `cT` on `x`. If `p` halts, it computes `cT.eval`, which is in `C` (`eval_reduction_of_halts`). If not, it computes the nowhere-defined function, which is not (`eval_reduction_of_not_halts`). The reduction only builds a program from the data of `p`. Its classical ingredients are the finite constants `w` and `cT`.

`halt_reducesto_rice_spec` gives `HaltProblem ⪯_s[reduction w cT] RiceProblem C`, packaged as `Rice.synthFromHalt`.

### Undecidability

`Undecidable.lean` collects `Rice.not_computablePred`: if `C` is non-trivial, then `RiceProblem C` is not a computable predicate (from Mathlib's `ComputablePred.rice`). It also collects `Rice.synthFromHalt`: if `cT` computes a function in `C` and the nowhere-defined function is not in `C`, then `RiceProblem C` is synthetically halting-hard. It also collects `Rice.synthComplFromHalt`: if `cF` computes a function not in `C` and the nowhere-defined function is in `C`, then the complement of `RiceProblem C` is synthetically halting-hard, by the same reduction for the complement of `C`. Every non-trivial `C` falls under one of the two, depending on whether it contains the nowhere-defined function, which is itself computed by a program. Both take the waiter program `w` as an argument.
