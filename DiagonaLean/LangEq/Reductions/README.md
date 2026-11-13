```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `LangEq.Reductions`: Language Equality with Commutativity Reductions
1. [`Halt ⪯ₘ ¬LangEq`](#halt-ₘ-langeq)

## `Halt ⪯ₘ ¬LangEq`
`haltRed` sends `(M, w)` to the inequality `(init w)_r R_M∗ ≤ Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ_M`, which fails in the language model iff `M` halts on `w` (`halt_iff_not_modelLe`, in `Foundations/KleeneAlgebra/Separation.lean`). Since `e ≤ f` iff `e + f = f`, `haltEqRed` turns it into an equality instance. Equality in the language model is co-r.e., so the reduction lands in the complement: `haltReducesNotLangEq` over `ℕ`. Substituting the code `1ⁿ0` for the letter `n` gives `haltReducesNotLangEqBool` over `Σ = {0, 1}`, since an injective substitution preserves and reflects language equality (`pl_sb_eq_iff`).

### Undecidability
`Undecidable.lean` collects `undecidable_not_langEq`, `undecidable_not_langEq_bool` and `langEq_separated`.
