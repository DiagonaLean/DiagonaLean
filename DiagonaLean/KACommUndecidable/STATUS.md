```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# Status of the formalisation

How much of *Kleene algebra with commutativity conditions is undecidable* (arXiv:2411.15979) is formalised, and what is still open. Assessed on 2026-11-16, updated 2026-11-17; update it when a gap below is closed.

The paper's main result, from its abstract: *"the equational theory of Kleene algebra with commutativity conditions on primitives (or atomic terms) is undecidable … our results hold even for weaker theories that do not support the induction axioms of Kleene algebra."*

## Claim by claim

| Paper's claim | Lean | Status |
|---|---|---|
| Kleene algebra with commutativity conditions is undecidable | `KATermEq.Reduction.not_machineDecidable_kaTermEq_nat`, `…_bool` | **Done, no hypotheses** |
| …even for weaker theories without the induction axioms | `TermEq.Reduction.not_machineDecidable_termEq_nat`, `…_bool` (pre-Kleene algebra) | **Done, no hypotheses** |
| Any theory between pre-Kleene algebra and the language model (Theorem 18, general form) | `not_machineDecidable_of_between` | Conditional on a machine computing `kaRed`, not yet supplied. The paper also assumes its map `η` is computable. |
| Equality of languages, `L Σ̈` | `LangEq.Reduction.undecidableNotLangEq` (`Undecidable`, for the complement) | No machine-level result |
| Theorem 6, Corollary 7 | `FiniteLangCounterexample.lean`, `FiniteLangExpansion.lean` | False as stated (counterexample at `e = 1∗`); a repaired version is proved |

The headline statement:

```lean
theorem not_machineDecidable_kaTermEq_bool :
    ¬ MachineDecidable encBool fun i : InstB => KAEquiv DComm i.1 i.2
```

* **The problem:** two expressions over `{0, 1}` doubled into four letters, under the hypotheses that every left letter commutes with every right letter (`DComm`): a fixed, finite set of commutativity conditions on primitives.
* **"Decides":** no `SingleTapeTM Bool` outputs `[true]` on the binary encoding of the pair exactly when the equation is provable.
* **The encoding** `encBool` (and `encNat` over `ℕ`) is injective (`encNat_injective`), so the statement cannot hold for a trivial reason.
* **Axioms:** only `propext`, `Classical.choice` and `Quot.sound`; no `sorry` and no `native_decide`.

## Caveats

1. **The definition of the theory has not been checked against the paper line by line.** `KAEquiv` is the pre-Kleene theory `Equiv` plus right unfolding (`e∗ e ≤ e∗`) and both induction rules, closed under congruence, and it is proved sound for Mathlib's `KleeneAlgebra` (`eval_ka_sound`). The axioms of `Equiv` should still be compared with the paper's definition of pre-Kleene algebra.
2. **The `Undecidable` forms take arguments.** `undecidableTermEq B C hB hC` and `undecidableKATermEq B C hB hC` need the interpreter's constants `B` and the race program `C`, which are only known to exist, so a compiled definition cannot obtain them itself. The statements without them are the machine-level theorems above.

## Resolved

* **The machine encoding used to drop halting transitions** (until 2026-11-17). `encodeBoolTM` omitted every transition that halts, so two machines that differ only in what they write as they halt had the same code, and statements whose input is a machine code (`selfOut_inseparable`, `not_machineDecidable_selfEq`, and `not_machineDecidable_termEq` / `not_machineDecidable_kaTermEq` on the instances `eqRed M`) could hold for that reason alone. The code now records every transition, and `outputs_iff_of_code_eq` (`Foundations/Computability/CodeSim.lean`) proves that machines with the same code behave the same, so these statements now mean what they say. This also removes the obstacle to a machine computing `kaRed`, which used to be impossible because `kaRed` differs on two machines with the same code.

## Open work

1. Supply a machine that computes `kaRed`, which makes `not_machineDecidable_of_between`, the paper's general form of Theorem 18, unconditional.
2. Compare `Equiv` and `KAEquiv` with the paper's definitions (caveat 1).
3. Optionally, a machine-level result for `L Σ̈`; it is not part of the paper's main claim.
