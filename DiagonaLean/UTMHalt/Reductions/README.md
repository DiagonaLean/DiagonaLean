```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 4.6, Akhilesh Balaji
```
# `UTMHalt.Reductions`: Universal Turing Machine Halting Problem Reductions
1. [`Halt ⪯ₘ UTMHalt`](#halt-ₘ-utmhalt)

## `Halt ⪯ₘ UTMHalt`
The reduction follows from the definition of universality. For a weakly universal machine `U` (`IsWeaklyUniversal U`), `halt_iff_weakutmhalt` uses `hU M w` to show that `M` halts on `w` exactly when `WeakUTMHalts U hU M w`. For a universal machine `U` (`IsUniversal U`), `halt_iff_utmhalt` uses `(hU M w).left` to show that `M` halts on `w` exactly when `UTMHalts U hU M w`.

If a machine `D` satisfies `IsHaltDeciderFor U D` for a weakly universal `U`, then `isHaltDecider_of_isHaltDeciderFor` shows that `D` is a general halt decider: on input `encodePair (encodeBoolTM M) w`, the universality of `U` transfers the answer of `D` to `Halts M w`.

### Supporting results
| Theorem | Statement |
|---|---|
| `IsWeaklyUniversalWrt.exists_halts` | `U` halts on at least one input (witnessed by `haltTM`) |
| `IsWeaklyUniversalWrt.exists_not_halts` | `U` diverges on at least one input (witnessed by `loopTM`) |
| `isHaltDecider_of_isHaltDeciderFor` | a machine with `IsHaltDeciderFor U D` is a decider for `HaltProblem` |

### Undecidability
`Undecidable.lean` collects `not_exists_haltDeciderFor_of_isWeaklyUniversal`: for a weakly universal machine `U`, no machine `D` satisfies `IsHaltDeciderFor U D`. Its proof applies `isHaltDecider_of_isHaltDeciderFor` and contradicts `halt_undecidable`. No universal machine is constructed, so this is a statement about machines, not a many-one reduction to `UTMHaltProblem`.
