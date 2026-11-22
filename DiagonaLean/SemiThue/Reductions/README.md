```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `SemiThue.Reductions`: The Word Problem for String Rewriting Systems Reductions
1. [`Halt ⪯_s SemiThue`](#halt-ₘ-semithue)

## `Halt ⪯_s SemiThue`
The transition tiles of the MPCP reduction (`MPCP/Reductions/Halt_to_MPCP.lean`) pair a window of a configuration with its successor; read as rules `top → bot`, they rewrite the configuration string `# … q a … #` (`block`) one machine step at a time. With the absorb tiles (`a h⊥ → h⊥`, `h⊥ a → h⊥`), which let the halting marker swallow the tape around it, and a final rule `# h⊥ # → []`, they form the string rewriting system `tmRules tm`. For a machine that never writes a blank and never moves left at the left end, `tm` halts on `w` iff `block (initCfg w)` rewrites to the empty string (`halt_iff_derives`).

* **Forward** (`derives_of_halts`): each step of the run is one rewrite (`step_block`), from the configuration lemmas of the MPCP reduction; after halting, the absorb rules and the final rule erase the string (`derives_halted`).
* **Backward** (`halts_of_derives`): a configuration string has exactly one state marker, and the left side of every rule contains a marker, so a rewrite happens at the marker (`split_mark`). By determinism of the machine it is the machine's step (`step_inv`), except for an interior right move at the right end, which leaves the marker before `#`: a string from which nothing can be rewritten (`not_derives_stuck`), or the halting marker, when the machine has halted.

The reduction `haltToSemiThue` first normalises the machine and its input (`Foundations/Computability/Normalize/`), so that both conditions hold, then takes `tmRules` of the normalised machine and renames its states to their codes, over the fixed alphabet `Alpha ℕ Sym2`. Renaming letters injectively keeps derivability (`Codes.derives_mapRules_iff`, the code theorem `derives_encode_iff` for the synchronizing code `unit ∘ g`), so `halt_reducesto_semiThue_spec` gives `HaltProblem ⪯_s[haltToSemiThue] SemiThue.DecisionProblem`, packaged as `SemiThue.synthFromHalt`. Every rule of the system has a non-empty left side (`haltToSemiThue_lhs_ne`), so the same function reduces to the restricted problem `DecisionProblemPos` (`halt_reducesto_semiThuePos_spec`, `SemiThue.synthPosFromHalt`).

### Undecidability
`Undecidable.lean` collects `SemiThue.synthFromHalt`: the word problem is synthetically halting-hard over `Alpha ℕ Sym2`, from `SemiThue.synthFromHalt`. On systems with non-empty left sides the word problem is a functor on synchronizing codes (`semiThueFunctor` in `AlphabetLift.lean`), so `SemiThue.synthPosFromHaltOver b0 b1 hne` lifts `SemiThue.synthPosFromHalt` to every alphabet with two distinct letters `b0` and `b1`. `SemiThue.synthFromPos` sends a system with an empty left side to an instance without solution, which gives `SemiThue.synthFromHaltOver b0 b1 hne` for the plain word problem, and `SemiThue.synthFromHaltBool` over `Bool`.
