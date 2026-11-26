```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.ModelLeBool.Reductions`: Inclusion in `L Σ̈` over `{0, 1}` Reductions
1. [`Halt ⪯_s ¬ModelLeBool`](#halt-ₘ-modellebool)

## `Halt ⪯_s ¬ModelLeBool`
`haltRedB` replaces each letter `n` of the inequality `haltRed (M, w)` of `ModelLe` by the word `1ⁿ0` (`sbI`, `KAComm/KleeneAlgebra/BinarySubst.lean`). The substitution preserves inclusion in the language model (`pl_sb_le`) and, being injective on words, reflects it (`pl_le_of_sb`). So `M` halts on `w` iff the inequality over `{0, 1}` fails in the language model.

`halt_reducesto_not_modelLeBool_spec` gives `HaltProblem ⪯_s[haltRedB] Complement ModelLeBoolProblem`, packaged as `KAComm.ModelLeBool.synthComplFromHalt`.

### Undecidability
`Undecidable.lean` collects `KAComm.ModelLeBool.synthComplFromHalt` and the machine-level statement `not_machineDecidable_modelLeBool`: no Turing machine decides inclusion of languages under `encBool`, the binary digits of the code of a pair of expressions. It is Theorem 18 (`not_machineDecidable_between_bool`, `KAComm/KleeneAlgebra/Between.lean`) with the predicate taken to be inclusion of languages. `not_machineDecidable_modelLeBool_of_conv` extends it to any encoding that a machine computes from `encBool`.
