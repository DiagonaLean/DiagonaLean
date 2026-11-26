```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.LangEqBool.Reductions`: Equality on `L Σ̈` over `{0, 1}` Reductions
1. [`Halt ⪯_s ¬LangEqBool`](#halt-ₘ-langeqbool)

## `Halt ⪯_s ¬LangEqBool`
`haltEqRedB` replaces each letter `n` of the equality `haltEqRed (M, w)` of `LangEq` by the word `1ⁿ0` (`sbI`, `KAComm/KleeneAlgebra/BinarySubst.lean`). An injective substitution preserves and reflects language equality (`pl_sb_eq_iff`).

`halt_reducesto_not_langEqBool_spec` gives `HaltProblem ⪯_s[haltEqRedB] Complement LangEqBoolProblem`, packaged as `KAComm.LangEqBool.synthComplFromHalt`.

### Undecidability
`Undecidable.lean` collects `KAComm.LangEqBool.synthComplFromHalt` and the machine-level statement `not_machineDecidable_langEqBool`: no Turing machine decides equality of languages under `encBool`, the binary digits of the code of a pair of expressions. It is Theorem 18 (`not_machineDecidable_eq_between_bool`, `KAComm/KleeneAlgebra/Between.lean`) with the predicate taken to be equality of languages. `not_machineDecidable_langEqBool_of_conv` extends it to any encoding that a machine computes from `encBool`.
