```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `SKIConv.Reductions`: Convertibility of SKI Terms Reductions
1. [`Halt ⪯ₘ SKIConv`](#halt-ₘ-skiconv)

## `Halt ⪯ₘ SKIConv`
Fix a universal code `u` and its SKI translation `U = u.toSKI` (Cslib's `Nat.Partrec.Code.toSKI_correct`). For a program `c` and input `n`, the instance `inst U c n = U ⬝ toChurch ⟪c, n⟫ ⬝ (K ⬝ FF) ⬝ TT` reduces to `FF` when `c` outputs `1` on `n`, and to `TT` when `c` outputs `0`. `TT` and `FF` are not convertible (Cslib's `TF_nequiv`).

For a `HaltProblem` instance `p` with data `d`, the race program `C` runs a race on input `d`: it searches for a halting run of `p` and for a proof that `inst U C d` is convertible to `FF`, and returns `1` if the halting run comes first and `0` otherwise. The reduction `reduction U C` sends `p` to `(inst U C d, FF)`. Its only classical ingredients are the finite constants `U` and the code `C` from Mathlib's recursion theorem. The race and the instance live in `Foundations/CombinatoryLogic/Race.lean`.

Convertibility is `∃ k, Checks k ..` for a primitive recursive proof checker `Checks` (`Foundations/CombinatoryLogic/ProofSearch.lean`), a stack machine over pairs of term codes whose instructions are the rules of SKI conversion (`conv_iff_checks`). It follows `KAComm/KleeneAlgebra/ProofSearch.lean`.

`halt_reducesto_skiConv_spec` gives `HaltProblem ⪯ₘ[reduction U C] SKIConvProblem`, packaged as `haltReducesSKIConv`.

### Undecidability
`Undecidable.lean` collects `undecidableSKIConv`, which takes the reduction's constants as arguments, and the machine-level statement `not_machineDecidable_skiConv`: no Turing machine decides convertibility under the encoding of a pair of terms as the binary digits of the pair of their codes (`encSKI`, injective by `encSKI_injective`). Its proof runs the same race on the code of a machine and reduces from `self_halt_undecidable` (`not_machineDecidable_of_race` in `Foundations/Computability/ProofRace.lean`). It also collects `not_machineDecidable_skiConv_sepRed`: convertibility separates the computably inseparable pair `SelfOut true`, `SelfOut false`, through `sepRed`, which applies the instance `inst` to a reader program (`Foundations/Computability/OutputSearch.lean`) that returns the output bit of a machine on its own code.
