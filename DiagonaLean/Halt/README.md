```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
```
# `Halt`: The Turing Machine Halting Problem
## Problem Statement
Does there exist a Turing machine (TM) `D`, a single-tape machine over `Bool` (`SingleTapeTM Bool`), that satisfies the following specification?

The specification: it takes as input an encoding of a different TM `D'` and an input to `D'`, `w`, and outputs `true` on the tape if `D'` halts on input `w`, and `false` if it does not halt on input `w`.

No such decider `D` exists, which means that the halting problem is *undecidable*.

## Proof Outline
The main result is:
```
theorem halt_undecidable : ¬ ∃ D : SingleTapeTM Bool, IsHaltDecider D
```
where `IsHaltDecider D` asserts that for every TM `M` and input `w`, `D` outputs `[true]` from input `encodePair (encodeBoolTM M) w` if `M` halts on `w`, and `[false]` otherwise.

### Encodings
TMs over `Bool` are encoded as binary strings, as described in [HopcroftMotwaniUllman2006], by `encodeBoolTM`:
```
encodeBoolTM : EncodableTM Bool → List Bool
```
The encoding records the initial state index and the transition table, with a row for every state and every tape symbol. A halting transition still writes and moves, so it is recorded too, with successor index `0`; states have indices from `1`. So the code determines the machine's behaviour: machines with the same code halt on the same inputs and produce the same outputs (`halts_iff_of_code_eq` and `outputs_iff_of_code_eq` in `Foundations/Computability/CodeSim.lean`).

States, tape symbols, and directions are assigned unary indices separated by `true`. A transition `δ(q, x) = (q', sym, dir)` is encoded as five unary fields separated by single `true` bits. The full transition table is encoded as a sequence of transition encodings separated by `[true, true]`. The machine encoding prepends the initial state index. The number of consecutive `true` bits indicates nesting depth:

| Separator | Occurrence |
|---|---|
| `[true]` | between fields within a transition |
| `[true, true]` | between transitions in the table |
| `[true, true, true]` | between initial state and transition count |
| `[true, true, true, true]` | between transition count and transition table |

The full TM encoding is:
```
q₀ ++ [true,true,true] ++ n ++ [true,true,true,true] ++ transition_table
```

Pairs of inputs are encoded via:
```
encodePair (a b : List Bool) : List Bool := a ++ [true, true] ++ b
```

`Encoding.lean` also defines decodings, shows that the encodings satisfy `decode*(encode* w) = some w`, and proves that the encodings are injective. The proof of the undecidability of the halting problem does not need these facts.

### Diagonalization
#### Self-Halting
The self-halting problem asks whether a TM `M` halts when run on its own encoding `encodeBoolTM M`. It is undecidable:

```
theorem self_halt_undecidable : ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D
```

Assume `D` is a self-halt decider. Construct `diagTM D`, which on input `w`:
1. Simulates `D` on `w` (treating `w` as an encoding of a TM).
2. If `D` outputs `[true]`, loops forever.
3. If `D` outputs `[false]`, halts immediately.

Now consider running `diagTM D` on `encodeBoolTM (diagTM D)`:
- If `diagTM D` halts on `encodeBoolTM (diagTM D)`: by `IsSelfHaltDecider`, `D` outputs `[true]`, so by construction `diagTM D` loops (`diagTM_loops_of_outputs_true`). This is a contradiction.
- If `diagTM D` does not halt on `encodeBoolTM (diagTM D)`: by `IsSelfHaltDecider`, `D` outputs `[false]`, so by construction `diagTM D` halts (`diagTM_halts_of_outputs_false`). This is also a contradiction.

This proves `self_halt_undecidable`.

#### Halting
A halt decider for `(M, w)` yields a self-halt decider, by setting `w` to the encoding of `M`.

```
theorem self_halt_decider_if_halt_decider {D} (h : IsHaltDecider D) :
    ∃ D' : SingleTapeTM Bool, IsSelfHaltDecider D'
```

The machine `D'` is `pairSelfTM` composed with `D`, where `pairSelfTM` maps tape `encodeBoolTM M` to `encodePair (encodeBoolTM M) (encodeBoolTM M)` before handing off to `D`.

By the contrapositive of this theorem and `self_halt_undecidable`, no TM is a halt decider (`halt_undecidable`). ∎

## Computable inseparability
`Inseparable.lean` proves a second diagonal fact: no machine decides a set that contains every machine halting on its own code with output `1` (`SelfOut true`) and no machine halting on its own code with output `0` (`SelfOut false`) (`selfOut_inseparable`). It is a proof technique for statements `¬ MachineDecidable enc p` (`not_machineDecidable_of_separation`), used by the Kleene algebra results, not a notion of undecidability: a function that separates the two sets says nothing about machines in neither, so it does not give `SynthHaltReduction p`.
