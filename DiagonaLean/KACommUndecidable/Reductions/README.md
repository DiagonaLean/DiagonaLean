```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KACommUndecidable.Reductions`: Reductions to Kleene Algebra with Commutativity
1. [`Halt ⪯ₘ TermEq` and `Halt ⪯ₘ KATermEq`](#halt-ₘ-termeq-and-halt-ₘ-katermeq)
2. [`Halt ⪯ₘ ¬ModelLe`](#halt-ₘ-modelle)
3. [`Halt ⪯ₘ ¬LangEq`](#halt-ₘ-langeq)

## `Halt ⪯ₘ TermEq` and `Halt ⪯ₘ KATermEq`
For a `HaltProblem` instance `p`, the program `curry C ⟨p⟩` runs a race: it searches for a halting run of `p` and for a proof that the instance of its own machine holds, and returns `1` if the halting run comes first and `0` otherwise. Its machine writes its own code on the tape and then runs a fixed interpreter. The reduction `reduction B C` sends `p` to the instance (`rInst`) of that machine on empty input. Its only classical ingredients are finite constants: the interpreter's table and tape symbols (`Base`) and the code `C` from Mathlib's recursion theorem. The race and the instance are shared by both problems and live in `KACommUndecidable/KleeneAlgebra/Race.lean`; the flag `ka` selects pre-Kleene algebra (`false`) or Kleene algebra (`true`).

`halt_reducesto_termEq_spec` and `halt_reducesto_kaTermEq_spec` give `HaltProblem ⪯ₘ[reduction B C] _` over `ℕ`, packaged as `haltReducesTermEq` and `haltReducesKATermEq`. Substituting the code `1ⁿ0` for the letter `n` (`KACommUndecidable/KleeneAlgebra/BinarySubst.lean`) moves the reductions to `Σ = {0, 1}`: `haltReducesTermEqBool` and `haltReducesKATermEqBool`.

## `Halt ⪯ₘ ¬ModelLe`
`haltRed` sends `(M, w)` to the inequality `(init w)_r R_M∗ ≤ Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ_M` over `ℕ ⊕ ℕ`, with letters renamed to their codes. If `M` halts, the trace string ending in the halted word lies on the left but not on the right; if `M` runs forever, every string on the left either follows the run or lies in the error term. So `M` halts on `w` iff the inequality fails in the language model (`halt_iff_not_modelLe`, in `KACommUndecidable/KleeneAlgebra/Separation.lean`), which gives `haltReducesNotModelLe : HaltProblem ⪯ₘ Complement ModelLe.DecisionProblem`.

## `Halt ⪯ₘ ¬LangEq`
Since `e ≤ f` iff `e + f = f`, `haltEqRed` turns the inequality of `haltRed` into an equality instance. Equality in the language model is co-r.e., so the reduction lands in the complement: `haltReducesNotLangEq` over `ℕ`. Substituting the code `1ⁿ0` for the letter `n` gives `haltReducesNotLangEqBool` over `Σ = {0, 1}`, since an injective substitution preserves and reflects language equality (`pl_sb_eq_iff`).

## The machine-level results
The statements `¬ MachineDecidable …` over `ℕ` and `{0, 1}` in `Undecidable.lean` use the race program of the first section, run against an assumed decider. Those on the instances `eqRed M` (`not_machineDecidable_termEq`, `not_machineDecidable_kaTermEq`) are not reductions from `HaltProblem`: they use computable inseparability (`Halt/Inseparable.lean`): no machine decides a set of machines that contains those that output `1` on their own code and excludes those that output `0`. `kaRed` (`KACommUndecidable/KleeneAlgebra/Separation.lean`) sends the first kind of machine to inequalities provable in pre-Kleene algebra and the second to inequalities that fail in the language model, and `eqRed` does the same for equalities. So no machine decides any relation between the two on these instances (`not_machineDecidable_selfEq`), and none decides it on all instances if a machine computes `kaRed` (`not_machineDecidable_of_between`).

`Undecidable.lean` in the parent folder collects the results.
