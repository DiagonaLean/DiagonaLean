```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.LangEq.Reductions`: Equality on `L Σ̈` Reductions
1. [`Halt ⪯ₘ ¬LangEq`](#halt-ₘ-langeq)

## `Halt ⪯ₘ ¬LangEq`
Since `e ≤ f` iff `e + f = f`, `haltEqRed` turns the inequality `haltRed (M, w)` of `ModelLe` into an equality instance (`modelLe_iff_langEq`). Equality in the language model is co-r.e., so the reduction lands in the complement.

`halt_reducesto_not_langEq_spec` gives `HaltProblem ⪯ₘ[haltEqRed] Complement LangEqProblem`, packaged as `haltReducesNotLangEq`.

### Undecidability
`Undecidable.lean` collects `undecidableNotLangEq` and the machine-level statement `not_machineDecidable_langEq`: no Turing machine decides equality of languages under `encNat`, the binary digits of the code of a pair of expressions. It is Theorem 18 (`not_machineDecidable_eq_between`, `KAComm/KleeneAlgebra/Between.lean`) with the predicate taken to be equality of languages. `not_machineDecidable_langEq_of_conv` extends it to any encoding that a machine computes from `encNat`.
