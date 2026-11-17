```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KACommUndecidable`: Kleene Algebra with Commutativity Conditions is Undecidable

A formalisation of A. Azevedo de Amorim, C. Zhang and M. Gaboardi, *Kleene algebra with commutativity conditions is undecidable* (arXiv:2411.15979, `AmorimZhangGaboardi2024` in `bibliography.bib`). How much of the paper is formalised, with the caveats and open work, is in [`STATUS.md`](STATUS.md).

## Problem Statement
An instance is a pair of expressions `e₁ e₂ : RExp (α ⊕ α)` over the doubled alphabet, in which every left letter `.inl a` commutes with every right letter `.inr b` (`DComm`). The paper asks four questions about such a pair, from the most syntactic to the most semantic:

| Problem | Question | Lean |
|---|---|---|
| Equality on `T Σ̈` | Is `e₁ = e₂` provable in pre-Kleene algebra with these commutations? | `TermEq.DecisionProblem`, `TermEqProblem` over `{0, 1}` |
| Equality on `K Σ̈` | Is `e₁ = e₂` provable in Kleene algebra with these commutations? This is the theory of the title. | `KATermEq.DecisionProblem`, `KATermEqProblem` over `{0, 1}` |
| Equality on `L Σ̈` | Do `e₁` and `e₂` have the same language in the model `TD.pl`? | `LangEq.DecisionProblem`, `LangEqProblem` over `{0, 1}` |
| Inclusion in `L Σ̈` | Is the language of `e₁` contained in that of `e₂`? | `ModelLe.DecisionProblem` |

Each problem keeps its own namespace, so its results read as `TermEq.Reduction.undecidableTermEq`, `LangEq.Reduction.undecidableNotLangEq` and so on.

## Layout
* `Basic.lean`: the four problems.
* `Reductions/Halt_to_X.lean`: a reduction from `HaltProblem` to each problem (to its complement for `LangEq` and `ModelLe`); see `Reductions/README.md`.
* `Undecidable.lean`: the headline results, side by side.
* `KleeneAlgebra/`: the algebra, the encoding of Turing machines as terms (`KleeneAlgebra/MachineEncoding/`) and the race program.

The interpreter the race program relies on is in `Foundations/Computability/`.

## Results
* **`T Σ̈` and `K Σ̈`.** `undecidableTermEq` and `undecidableKATermEq` (over `ℕ`) and their `Bool` versions (over `{0, 1}`) are `Undecidable`, given finite constants that are only known to exist: the interpreter's table `B` and the race program `C`. They are arguments, since a compiled definition cannot extract them from an existence proof. Without them, the results are stated at the level of machines: `not_machineDecidable_termEq_nat`, `not_machineDecidable_termEq_bool` and the `kaTermEq` versions say that no Turing machine decides these problems.
* **`L Σ̈`.** Language equality and language inclusion are co-r.e., so the reductions land in the complement: `undecidableNotLangEq`, `undecidableNotLangEqBool` and `undecidableNotModelLe` take no arguments.
* **Any theory in between.** The machine-level results on the instances `eqRed M` rest on computable inseparability (`Halt/Inseparable.lean`): `kaRed` sends machines that output `1` on their own code to inequalities provable in pre-Kleene algebra, and machines that output `0` to inequalities false in the language model. So no machine decides any relation between pre-Kleene algebra provability and the language model on the instances `eqRed M` (`not_machineDecidable_selfEq`). On all instances, `KleeneAlgebra/Between.lean` proves the paper's general Theorem 18 with no hypothesis, using the interpreter's instances instead of `kaRed`: no machine decides any predicate between provability in pre-Kleene algebra and the language model, for inequalities (`not_machineDecidable_between`) and equations (`not_machineDecidable_eq_between`), and no machine decides equality on any `X` through which the language map factors (`not_machineDecidable_eqVia`; `not_machineDecidable_eqOn` given a machine computing `l'`). So no machine decides equality or inclusion of languages either (`not_machineDecidable_langEq_nat`, `not_machineDecidable_modelLe_nat`).

## Where the paper's results are
Files under `KleeneAlgebra/` unless stated otherwise.

| Paper | File |
|---|---|
| Example 1 (a pre-Kleene algebra that is not a Kleene algebra) | `PreKleeneNotKleene.lean` |
| Theorem 5, the doubled alphabet and its language model | `Doubled.lean` |
| Theorem 6, Corollary 7: **false as stated** (counterexample at `e = 1∗`) | `FiniteLangCounterexample.lean` |
| Theorem 6, Corollaries 7 and 8, Theorem 9: repaired | `FiniteLangExpansion.lean`, `BoundedOutput.lean`, `Representable.lean` |
| Theorem 9, pre-Kleene algebras | `PreKleene.lean` |
| Definition 13, Lemma 14, Lemma 35: the transition term of a machine | `MachineEncoding/Transition.lean`, `MachineEncoding/MachineTerms.lean` |
| Theorem 15, soundness | `Soundness.lean`, `MachineEncoding/LanguageSoundness.lean`, `MachineEncoding/Halting.lean` |
| Theorem 16, completeness | `Completeness.lean`, `MachineEncoding/TraceCompleteness.lean` |
| Theorem 18, undecidability | `Between.lean`, `Separation.lean`, `Instance.lean`, `FreeKA.lean`; here `Reductions/` and `Undecidable.lean` |
| Theorem 19, the race program | `Race.lean` |
| Definition 20, Lemma 21, Theorem 22, Lemma 34: representable relations | `Representable.lean` |
| Definitions 23 and 25, Lemmas 24 and 26: derivatives and finite-state terms | `Automata.lean`, `Syntax.lean` |
| Lemma 27, the expansion lemma | `Expansion.lean` |
| Definition 28, Lemmas 29–31: bounded-output terms | `BoundedOutput.lean` |
| Definition 32, Lemmas 33 and 34: single-step representability | `SingleStep.lean` |
