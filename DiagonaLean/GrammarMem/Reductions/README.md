```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `GrammarMem.Reductions`: Membership for Grammar Codes Reductions
1. [`Halt ⪯_s GrammarMem`](#halt-ₘ-grammarmem)

## `Halt ⪯_s GrammarMem`
The reduction goes through the word problem for string rewriting systems (`SemiThue/Reductions/Halt_to_SemiThue.lean`): `SemiThue.Reduction.haltToSemiThue` sends a machine and an input to a rewriting system over `Alpha ℕ Sym2` and a start string that rewrites to the empty string iff the machine halts (`halt_reducesto_semiThue_spec`).

A fresh start symbol `0` with the rule `[0] → start string`, and the other symbols numbered from `1` (`gSym`), turn the rewriting system into a grammar code (`ofSRS`, in `MachineLevel.lean`). When every rule has a non-empty left side, a derivation from `[0]` must begin with the start rule and never meets `0` again (`SRS.derives_start`), so the empty word is in the language iff the start string rewrites to the empty string (`emptyWord_ofSRS_iff`). The systems of `haltToSemiThue` have non-empty left sides (`haltToSemiThue_lhs_ne`).

The reduction `haltToGrammarMem` sends a machine and an input to the grammar code of `haltToSemiThue` and the empty word. `halt_reducesto_grammarMem_spec` gives `HaltProblem ⪯_s[haltToGrammarMem] GrammarMem.DecisionProblem`, packaged as `GrammarMem.synthFromHalt`.

### Undecidability
`Undecidable.lean` collects `GrammarMem.synthFromHalt`: membership for grammar codes is synthetically halting-hard, over any type of terminals, from `GrammarMem.synthFromHalt`. The grammar codes of the reduction are not shown to be of type 0 there; the machine-level statement for type 0 codes, `not_machineDecidable_emptyWord_type0`, is in `MachineLevel.lean`, where the codes of `gCode` are of type 0 (`isType0_gCode`).
