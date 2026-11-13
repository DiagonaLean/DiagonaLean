```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm.Reductions`: Kleene Algebra with Commutativity Conditions Reductions
1. [`Halt ⪯ₘ TermEq` and `Halt ⪯ₘ KATermEq`](#halt-ₘ-termeq-and-halt-ₘ-katermeq)
2. [`Halt ⪯ₘ ¬LangEq`](#halt-ₘ-langeq)
3. [`Halt ⪯ₘ ¬ModelLe`](#halt-ₘ-modelle)
4. [No Turing machine decides `TermEq` or `KATermEq`](#no-turing-machine-decides-termeq-or-katermeq)

## `Halt ⪯ₘ TermEq` and `Halt ⪯ₘ KATermEq`
For a `HaltProblem` instance `p`, the program `curry C ⟨p⟩` runs a race: it searches for a halting run of `p` and for a proof that the instance of its own machine holds, and returns `1` if the halting run comes first and `0` otherwise. Its machine writes its own code on the tape and then runs a fixed interpreter. The reduction `reduction B C` sends `p` to the instance (`rInst`) of that machine on empty input. Its only classical ingredients are finite constants: the interpreter's table and tape symbols (`Base`) and the code `C` from Mathlib's recursion theorem.

`halt_reducesto_termEq_spec` and `halt_reducesto_kaTermEq_spec` give `HaltProblem ⪯ₘ[reduction B C] _` over `ℕ`, packaged as `haltReducesTermEq`, `haltReducesKATermEq` and the theorems `undecidable_termEq`, `undecidable_kaTermEq`. Substituting the code `1ⁿ0` for the letter `n` (`BinarySubst.lean`) moves the result to `Σ = {0, 1}`: `undecidable_termEq_bool` and `undecidable_kaTermEq_bool`.

### Supporting Results
| File | Contents |
|---|---|
| `Instance.lean` | `rInst`, the instance of a machine on empty input |
| `InstanceCode.lean` | `instCode`, computing that instance primitive recursively |
| `ExprCode.lean` | `rc`, expressions as natural numbers |
| `ProofSearch.lean` | `Checks`, provable equality as a search over a primitive recursive test |
| `BinarySubst.lean` | substituting `1ⁿ0` for letters, on terms, languages and codes |

## `Halt ⪯ₘ ¬LangEq`
`undecidable_not_langEq_bool` (`Halt_to_TermEqBool.lean`) shows that the failure of equality on `L Σ̈` is undecidable over `{0, 1}`, and `undecidable_not_langEq` (`SelfOut_to_Eq.lean`) over `ℕ`. Equality in the language model is co-r.e., so the reduction lands in its complement.

## `Halt ⪯ₘ ¬ModelLe`
`SelfOut b M` holds when `M` halts on its own code with output `[b]`; no Turing machine decides a set containing `SelfOut true` and disjoint from `SelfOut false` (`selfOut_inseparable`). The reduction `kaRed` sends a machine to a pair of expressions over `ℕ ⊕ ℕ`: machines with output `1` give inequalities provable in pre-Kleene algebra, machines with output `0` give inequalities that fail in the language model. `sepReducesOfBetween` shows this separates the pair for every theory between `Provable` and `ModelLe`, which covers Kleene algebra with the commutativity hypotheses, since the language model satisfies them. `undecidable_not_modelLe` packages the many-one reduction `haltReduces : HaltProblem ⪯ₘ Complement ModelLe`.

`SelfOut_to_Eq.lean` turns the inequalities into equalities through `e ≤ f ↔ e + f = f`, for any factoring `l = g ∘ l'` of the language map (`LangFactor`), which gives Theorem 18 of the paper for `T Σ̈`, `K Σ̈` and `L Σ̈` as separation statements. The machine-level statements in these two files (`not_machineDecidable_of_between`, `not_machineDecidable_eqVia_of_computes`) assume a Turing machine computing `kaRed` from `encodeBoolTM M`; that machine is not constructed.

## No Turing machine decides `TermEq` or `KATermEq`
A decider `D` for equality, under the encoding of a pair of expressions as the binary digits of its code, would decide "`M` halts on its own code", contradicting `self_halt_undecidable`: from the code of `M`, a machine `R` computes the instance of the race program (`exists_computer`), and `D` decides that instance. The theorems are `not_machineDecidable_termEq_bool` and `not_machineDecidable_kaTermEq_bool` over `{0, 1}`, and the `_nat` versions over `ℕ` (`SelfHalt_to_TermEq.lean`).

`Sigma1.lean` states the same argument on a machine's own code, following Smullyan, conditional on a `SmullyanFamily` built with the recursion theorem. The results above do not use it.
