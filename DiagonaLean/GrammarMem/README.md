```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `GrammarMem`: Membership for Grammar Codes
## Problem Statement
Given a grammar code `g` and a terminal word `w`, is `w` in the language of `g`? A grammar code (`GrammarCode T`) is a start symbol and a list of rewriting rules over terminals `T` and numbered nonterminals, with no condition on the rules. Its language is the set of terminal words that the start symbol rewrites to (`GrammarCode.language`). The problem is `DecisionProblem (g, w)` in `Basic.lean`; `EmptyWordProblem g` is the case of the empty word. `IsType0` is Chomsky's condition for unrestricted (type 0) grammars, that every left side contains a nonterminal.

Every context-free grammar code is a grammar code of type 0 with the same language (`language_toGrammarCode`, `isType0_toGrammarCode`).

## Layout
* `Basic.lean`: the problem, type 0, and context-free codes as grammar codes.
* `MachineLevel.lean`: the grammar code of a rewriting system (`ofSRS`), its language and type (`emptyWord_ofSRS_iff`, `isType0_ofSRS`).
* `Reductions/Halt_to_GrammarMem.lean`: `HaltProblem ⪯_s` membership for grammar codes (`GrammarMem.synthFromHalt`). See `Reductions/README.md`.
* `Hardness.lean`: membership for grammar codes is halting-hard, by a reduction from `HaltCanon` proved computable (`GrammarMem.fromHalt`), already for the empty word and type 0 codes (`GrammarMem.emptyWordFromHalt`). So no Turing machine decides whether the empty word is in the language of a type 0 grammar code (`GrammarMem.EmptyWord.not_machineDecidable`), nor membership for grammar codes (`GrammarMem.not_machineDecidable`), under any computable encoding.
* `Undecidable.lean`: membership for grammar codes is synthetically halting-hard (`GrammarMem.synthFromHalt`).

## Proof sketch
The reduction goes through the word problem for string rewriting systems (`SemiThue/`): a machine halts iff its configuration string rewrites to the empty string. A fresh start symbol `0` with the rule `[0] → start string`, and the other symbols numbered from `1`, turn the rewriting system into a grammar code (`ofSRS`). When every rule has a non-empty left side, a derivation from `[0]` must begin with the start rule and never meets `0` again (`SRS.derives_start` in `Foundations/Grammar/Rewriting.lean`), so the empty word is in the language iff the start string rewrites to the empty string (`emptyWord_ofSRS_iff`). The grammar codes of the halting reduction are of type 0 (`isType0_ofSRS`, `isType0_canonGCode`), so the machine-level results for the empty word hold already for type 0 grammar codes, which is Chomsky's class of unrestricted grammars. The `SynthHaltReduction` statement is for all grammar codes.

## References
* N. Chomsky, *On certain formal properties of grammars* (1959)
* J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*
