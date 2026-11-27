```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.KATermEq.Reductions`: Equality on `K Σ̈` Reductions
1. [`Halt ⪯_s KATermEq`](#halt-ₘ-katermeq)

## `Halt ⪯_s KATermEq`
For a `HaltProblem` instance `p`, the program `curry C ⟨p⟩` runs a race: it searches for a halting run of `p` and for a proof that the instance of its own machine holds, and returns `1` if the halting run comes first and `0` otherwise. Its machine writes its own code on the tape and then runs a fixed interpreter. The reduction `reduction B C` sends `p` to the instance (`rInst`) of that machine on empty input. Its only classical ingredients are finite constants: the interpreter's table and tape symbols (`Base`) and the code `C` from Mathlib's recursion theorem. The race and the instance live in `KAComm/KleeneAlgebra/Race.lean`, shared with `TermEq`; the flag `ka = true` selects Kleene algebra.

`halt_reducesto_kaTermEq_spec` gives `HaltProblem ⪯_s[reduction B C] KATermEqProblem`, packaged as `KAComm.KATermEq.synthFromHalt`.

### Undecidability
`SynthHardness.lean` collects `KAComm.KATermEq.synthFromHalt`, which takes the reduction's constants as arguments. `Undecidable.lean` collects the machine-level statement `not_machineDecidable_kaTermEq`: no Turing machine decides the problem under `encNat`, the binary digits of the code of a pair of expressions. Its proof runs the same race against an assumed decider (`not_machineDecidable_of_family`). `not_machineDecidable_kaTermEq_of_conv` extends it to any encoding that a machine computes from `encNat`. `not_machineDecidable_kaTermEq_eqRed` is not a reduction from `HaltProblem`: it uses computable inseparability (`Halt/Inseparable.lean`). `eqRed` (`KAComm/KleeneAlgebra/Separation.lean`) sends machines that output `1` on their own code to provably equal pairs and machines that output `0` to pairs with different languages, so no machine decides the problem on these instances (`not_machineDecidable_selfEq`). `Hardness.lean` proves it halting-hard (`KAComm.KATermEq.haltHard`), from canonical machines, so it is not a computable predicate (`KAComm.KATermEq.not_computablePred`) and no machine decides it under any computable encoding (`KAComm.KATermEq.not_machineDecidable`).
