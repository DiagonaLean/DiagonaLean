```
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
```
# Kleene algebra with commutativity is undecidable

A formalization of de Amorim, Zhang and Gaboardi, *Kleene algebra with commutativity conditions is
undecidable* (arXiv:2411.15979; the PDF is in `../Kleene Algebra/`).

## The main results

No Turing machine decides provable equality on `T Σ̈` or `K Σ̈`, in
`Reductions/SelfHalt_to_TermEq.lean`:

```lean
theorem not_machineDecidable_termEq_bool :
    ¬ MachineDecidable encBool fun i : InstB => Equiv DComm i.1 i.2
theorem not_machineDecidable_kaTermEq_bool :
    ¬ MachineDecidable encBool fun i : InstB => KAEquiv DComm i.1 i.2
```

`InstB` is the alphabet `{0, 1}` of the paper. There are also `_nat` versions over `ℕ`. `L Σ̈` is not
covered at this level. See `GAPS.md`.

## The layout

* `Basic.lean`: the instances (`EqInstance`) and the decision problems `TermEq.DecisionProblem`,
  `KATermEq.DecisionProblem` and `LangEq.DecisionProblem`, as in `PCP/Basic.lean`, with
  `TermEqProblem`, `KATermEqProblem` and `LangEqProblem` over `{0, 1}`.
* The files directly in this folder: pre-Kleene algebra, the free algebras, the language model,
  automata, and the completeness theorems of the paper's §2, §4 and §5.
* `MachineEncoding/`: Turing machine runs as terms, and Theorems 15 and 16.
* `Reductions/`: the reductions and the undecidability theorems. See its `README.md`.

General computability results are in `../Foundations/Computability/`, which imports nothing from
this folder.

## Other files

* `definitions-ledger.html`: every statement beside the paper's text.
* `TODO.md`, `GAPS.md`, `CHECKLIST.md`: the plan, what is open, and where results are.
