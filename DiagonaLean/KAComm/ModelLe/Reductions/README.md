```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.ModelLe.Reductions`: Inclusion in `L Σ̈` Reductions
1. [`Halt ⪯_s ¬ModelLe`](#halt-ₘ-modelle)

## `Halt ⪯_s ¬ModelLe`
`haltRed` sends `(M, w)` to the inequality `(init w)_r R_M∗ ≤ Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ_M` over `ℕ ⊕ ℕ`, with letters renamed to their codes. If `M` halts, the trace string ending in the halted word lies on the left but not on the right; if `M` runs forever, every string on the left either follows the run or lies in the error term. So `M` halts on `w` iff the inequality fails in the language model (`halt_iff_not_modelLe`, in `KAComm/KleeneAlgebra/Separation.lean`).

`halt_reducesto_not_modelLe_spec` gives `HaltProblem ⪯_s[haltRed] Complement ModelLeProblem`, packaged as `KAComm.ModelLe.synthComplFromHalt`.

### Undecidability
`SynthHardness.lean` collects `KAComm.ModelLe.synthComplFromHalt`. `Undecidable.lean` collects the machine-level statement `not_machineDecidable_modelLe`: no Turing machine decides inclusion of languages under `encNat`, the binary digits of the code of a pair of expressions. It is Theorem 18 (`not_machineDecidable_between`, `KAComm/KleeneAlgebra/Between.lean`) with the predicate taken to be inclusion of languages. `not_machineDecidable_modelLe_of_conv` extends it to any encoding that a machine computes from `encNat`. Since the code has a primitive recursive decoder, it is also not a computable predicate (`KAComm.ModelLe.not_computablePred`, by `not_computablePred_of_bitsPair`), so no machine decides it under any computable encoding.
