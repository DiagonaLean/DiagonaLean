```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.LangEq.Reductions`: Equality on `L Σ̈` Reductions
1. [`Halt ⪯_s ¬LangEq`](#halt-ₘ-langeq)

## `Halt ⪯_s ¬LangEq`
Since `e ≤ f` iff `e + f = f`, `haltEqRed` turns the inequality `haltRed (M, w)` of `ModelLe` into an equality instance (`modelLe_iff_langEq`). Equality in the language model is co-r.e., so the reduction lands in the complement.

`halt_reducesto_not_langEq_spec` gives `HaltProblem ⪯_s[haltEqRed] Complement LangEqProblem`, packaged as `KAComm.LangEq.synthComplFromHalt`.

### Undecidability
`Undecidable.lean` collects `KAComm.LangEq.synthComplFromHalt` and the machine-level statement `not_machineDecidable_langEq`: no Turing machine decides equality of languages under `encNat`, the binary digits of the code of a pair of expressions. It is Theorem 18 (`not_machineDecidable_eq_between`, `KAComm/KleeneAlgebra/Between.lean`) with the predicate taken to be equality of languages. `not_machineDecidable_langEq_of_conv` extends it to any encoding that a machine computes from `encNat`. Since the code has a primitive recursive decoder, it is also not a computable predicate (`not_computablePred_langEq`, by `not_computablePred_of_bitsPair`), so no machine decides it under any computable encoding.
