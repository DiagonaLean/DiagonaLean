```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.KATermEqBool.Reductions`: Equality on `K Σ̈` over `{0, 1}` Reductions
1. [`Halt ⪯_s KATermEqBool`](#halt-ₘ-katermeqbool)

## `Halt ⪯_s KATermEqBool`
For a `HaltProblem` instance `p`, the program `curry C ⟨p⟩` runs a race: it searches for a halting run of `p` and for a proof that the instance of its own machine holds, and returns `1` if the halting run comes first and `0` otherwise. Its machine writes its own code on the tape and then runs a fixed interpreter. The reduction `reductionB B C` sends `p` to the instance of that machine on empty input, with each letter `n` replaced by the word `1ⁿ0` (`sbI`, `KAComm/KleeneAlgebra/BinarySubst.lean`). Its only classical ingredients are finite constants: the interpreter's table and tape symbols (`Base`) and the code `C` from Mathlib's recursion theorem. The race and the instance live in `KAComm/KleeneAlgebra/Race.lean`, shared with `TermEqBool`; the flag `ka = true` selects Kleene algebra.

`halt_reducesto_kaTermEqBool_spec` gives `HaltProblem ⪯_s[reductionB B C] KATermEqBoolProblem`, packaged as `KAComm.KATermEqBool.synthFromHalt`.

### Undecidability
`Undecidable.lean` collects `KAComm.KATermEqBool.synthFromHalt`, which takes the reduction's constants as arguments, and the machine-level statement `not_machineDecidable_kaTermEqBool`: no Turing machine decides the problem under `encBool`, the binary digits of the code of a pair of expressions. Its proof runs the same race against an assumed decider (`not_machineDecidable_of_family`). `not_machineDecidable_kaTermEqBool_of_conv` extends it to any encoding that a machine computes from `encBool`.
