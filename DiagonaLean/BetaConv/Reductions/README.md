```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `BetaConv.Reductions`: β-Conversion of λ-Terms Reductions
1. [`Halt ⪯_s BetaConv`](#halt-ₘ-betaconv)

## `Halt ⪯_s BetaConv`
The translation `tr` (`Foundations/LambdaCalculus/Translation.lean`) sends an SKI term to a λ-term, with `S`, `K` and `I` as the closed terms `λxyz.xz(yz)`, `λxy.x` and `λx.x`. SKI reduction becomes β-reduction (`tr_mRed`), and `tr TT` and `tr FF` are not β-convertible (`not_betaConv_tr_TT_FF`). The translation does not reflect convertibility (`tr_not_reflect`: `S ⬝ K` and `K ⬝ I` have no common SKI reduct, while their translations both β-reduce to `λyz.z`), so translating the `SKIConv` reduction does not directly give a reduction to β-conversion.

The λ-instance `linst U c n` is the translation of the SKI instance `inst U c n` of `SKIConv`. It β-reduces to `tr FF` when the program `c` outputs `1` on `n`, and to `tr TT` when `c` outputs `0`. For a `HaltProblem` instance `p` with data `d`, the race program `C` runs the race of `Foundations/Computability/ProofRace.lean`: it searches for a halting run of `p` and for a proof that `linst U C d` is β-convertible to `tr FF`, and returns `1` if the halting run comes first and `0` otherwise. The race searches for β-conversion proofs, not SKI-conversion proofs. The reduction `reduction U C` sends `p` to `(linst U C d, tr FF)`. Its only classical ingredients are the finite constants `U` and the code `C` from Mathlib's recursion theorem.

For locally closed terms, β-convertibility is `∃ k, Checks k ..` for a primitive recursive proof checker `Checks` (`Foundations/LambdaCalculus/ProofSearch.lean`, `betaConv_iff_checks`), a stack machine whose entries record conversions and, so that no substitution is computed, facts about local closure, opening and closing, all built from constructors.

`halt_reducesto_betaConv_spec` gives `HaltProblem ⪯_s[reduction U C] BetaConvProblem`, packaged as `BetaConv.synthFromHaltWith`.

### Undecidability
`Undecidable.lean` collects `BetaConv.synthFromHalt`, which takes the reduction's constants as arguments, and the machine-level statement `not_machineDecidable_betaConv`: no Turing machine decides β-conversion under the encoding of a pair of terms as the binary digits of the pair of their codes (`encBeta`, injective by `encBeta_injective`). Its proof runs the same race on the code of a machine and reduces from `self_halt_undecidable` (`not_machineDecidable_of_race` in `Foundations/Computability/ProofRace.lean`). It also collects `not_machineDecidable_betaConv_sepRed`: β-conversion separates the computably inseparable pair `SelfOut true`, `SelfOut false`, through `sepRed`, which applies the instance `linst` to a reader program (`Foundations/Computability/OutputSearch.lean`) that returns the output bit of a machine on its own code. `Hardness.lean` proves it halting-hard (`BetaConv.haltHard`), from canonical machines, so it is not a computable predicate (`BetaConv.not_computablePred`) and no machine decides it under any computable encoding (`BetaConv.not_machineDecidable`).
