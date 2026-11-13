```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `ModelLe.Reductions`: Language Inclusion with Commutativity Reductions
1. [`Halt ⪯ₘ ¬ModelLe`](#halt-ₘ-modelle)

## `Halt ⪯ₘ ¬ModelLe`
`haltRed` sends `(M, w)` to the inequality `(init w)_r R_M∗ ≤ Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ_M` over `ℕ ⊕ ℕ`, with letters renamed to their codes. If `M` halts, the trace string ending in the halted word lies on the left but not on the right; if `M` runs forever, every string on the left either follows the run or lies in the error term. So `M` halts on `w` iff the inequality fails in the language model (`halt_iff_not_modelLe`), which gives `haltReducesNotModelLe : HaltProblem ⪯ₘ Complement ModelLe.DecisionProblem`.

### Undecidability
`Undecidable.lean` collects `undecidable_not_modelLe` and `insepUndecidable_modelLe`. The second uses `kaRed` (`Foundations/KleeneAlgebra/Separation.lean`), which sends machines with output `1` on their own code to inequalities provable in pre-Kleene algebra and machines with output `0` to inequalities that fail in the language model, so every theory between `Provable` and `ModelLe` separates the inseparable pair (`insepUndecidable_of_between`).
