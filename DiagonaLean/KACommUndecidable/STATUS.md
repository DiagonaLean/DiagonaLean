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
| Any theory between pre-Kleene algebra and the language model (Theorem 18, general form) | `not_machineDecidable_between` (inequalities), `not_machineDecidable_eq_between` (equations), `not_machineDecidable_eqVia` (any `X` the language map factors through), all in `KleeneAlgebra/Between.lean` | **Done, no hypotheses**, over `ℕ` (`encNat`) |
| Theorem 18 on `X` itself | `not_machineDecidable_eqOn` | Given a machine computing `l'` on expression codes, which is the paper's hypothesis that `l'` is computable |
| Equality and inclusion of languages, `L Σ̈` | `not_machineDecidable_langEq_nat`, `not_machineDecidable_modelLe_nat`; `undecidableNotLangEq` (`Undecidable`, for the complement) | **Done, no hypotheses** |
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

1. **The `Undecidable` forms take arguments.** `undecidableTermEq B C hB hC` and `undecidableKATermEq B C hB hC` need the interpreter's constants `B` and the race program `C`, which are only known to exist, so a compiled definition cannot obtain them itself. The statements without them are the machine-level theorems above.

## Resolved

* **The theories match the paper** (checked 2026-11-17 against Section 2 and Definition 12 of arXiv:2411.15979v1).
  * `Equiv` (`KleeneAlgebra/Free.lean`) has exactly the paper's pre-Kleene algebra equations: the semiring laws (associativity, commutativity, units, zeros, both distributive laws), idempotence `x + x = x`, and left unfolding `x∗ = 1 + x x∗`, closed under congruence. The paper's list of equations omits idempotence, but its text says "idempotent semiring", so idempotence is part of its definition.
  * The commutation hypotheses `DComm` are the paper's `Σ̈ = Σ ⊕ Σ` for discrete `Σ`: every left letter commutes with every right letter. The paper's relation is also reflexive, which only adds the trivial equations `x x = x x`. The paper builds `T X` as `T' (S X)`, while `Equiv` adds `x y = y x` for each commuting pair; with congruence and associativity these give the same theory.
  * `KAEquiv` (`KleeneAlgebra/FreeKA.lean`) follows Mathlib's `KleeneAlgebra`, which adds right unfolding `e∗ e ≤ e∗` to the paper's Kleene algebra (pre-Kleene algebra with left and right induction). `PaperKAEquiv` is the paper's theory exactly, and `kaEquiv_iff_paperKAEquiv` proves the two equal, deriving right unfolding from left induction (`paperKAEquiv_kstar_mul_le`).
  * The paper writes `x ≤ y` for `y + x = x`, which is reversed; with that reading its induction axioms would not be Kozen's. The Lean files use the standard `x + y = y`, which is what the paper's arguments use.

* **The machine encoding used to drop halting transitions** (until 2026-11-17). `encodeBoolTM` omitted every transition that halts, so two machines that differ only in what they write as they halt had the same code, and statements whose input is a machine code (`selfOut_inseparable`, `not_machineDecidable_selfEq`, and `not_machineDecidable_termEq` / `not_machineDecidable_kaTermEq` on the instances `eqRed M`) could hold for that reason alone. The code now records every transition, and `outputs_iff_of_code_eq` (`Foundations/Computability/CodeSim.lean`) proves that machines with the same code behave the same, so these statements now mean what they say. This also removes the obstacle to a machine computing `kaRed`, which used to be impossible because `kaRed` differs on two machines with the same code.

* **Theorem 18 in general form used to be conditional** (until 2026-11-17) on a machine computing `kaRed`. `KleeneAlgebra/Between.lean` now proves it without one. The paper reduces from the inseparable pair `SelfOut true`, `SelfOut false` through its map `η`; the proof here reduces from the same pair, but sends a machine `M` to the interpreter's instance for a program that simulates `M` on its own code and returns its output bit (`outBit`, `Foundations/Computability/OutBit.lean`). That instance's code is primitive recursive in the code of `M`, so a machine computes the reduction. The statements that take a machine computing `kaRed` or `eqRed` (`not_machineDecidable_of_between`, `not_machineDecidable_eqVia_of_computes`, `not_machineDecidable_eqOn_of_computes`) remain, for any encoding under which one exists.

## Open work

1. Optionally, prove `kaRed` itself computable, which would make the `…_of_computes` statements unconditional and follow the paper's proof more closely. The main cost is recomputing the derived `Encodable Letter` codes on numbers.
2. Optionally, `{0, 1}` versions of the Theorem 18 statements (via `sbI` and `instCodeB`, as for the headline results).
