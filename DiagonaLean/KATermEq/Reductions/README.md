```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KATermEq.Reductions`: Equality in Kleene Algebra with Commutativity Reductions
1. [`Halt ⪯ₘ KATermEq`](#halt-ₘ-katermeq)

## `Halt ⪯ₘ KATermEq`
For a `HaltProblem` instance `p`, the program `curry C ⟨p⟩` runs a race: it searches for a halting run of `p` and for a proof that the instance of its own machine holds, and returns `1` if the halting run comes first and `0` otherwise. Its machine writes its own code on the tape and then runs a fixed interpreter. The reduction `reduction B C` sends `p` to the instance (`rInst`) of that machine on empty input. Its only classical ingredients are finite constants: the interpreter's table and tape symbols (`Base`) and the code `C` from Mathlib's recursion theorem. The race and the instance are shared with the other Kleene algebra problems and live in `Foundations/KleeneAlgebra/Race.lean`, with the flag `ka := true`.

`halt_reducesto_kaTermEq_spec` gives `HaltProblem ⪯ₘ[reduction B C] _` over `ℕ`, packaged as `haltReducesKATermEq`. Substituting the code `1ⁿ0` for the letter `n` (`Foundations/KleeneAlgebra/BinarySubst.lean`) moves the reduction to `Σ = {0, 1}`: `haltReducesKATermEqBool`.

### Conditional Form
`haltReducesKATermEqOfFamily` is Theorem 19 as stated in the paper: given a `SmullyanFamily`, machines `N p` that race a halting run of `p` against evidence for their own instance `eqRed (N p)`, the map `eqRed ∘ N` is a reduction. The family has to be built from the data of `p` with the recursion theorem; the reduction above does not use it.

### Undecidability
`Undecidable.lean` collects `undecidable_kaTermEq` (over `ℕ`), `undecidable_kaTermEq_bool` (over `{0, 1}`), the machine-level statements `not_machineDecidable_kaTermEq_nat` and `not_machineDecidable_kaTermEq_bool` (no Turing machine decides `K Σ̈` equality under the encoding of a pair of expressions as the binary digits of its code, by reduction from `self_halt_undecidable`), and `kaTermEq_separated` (`K Σ̈` equality separates the computably inseparable pair `SelfOut true`, `SelfOut false`).
