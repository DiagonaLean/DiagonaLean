```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `GrammarMem`: Membership for Unrestricted Grammars
## Problem Statement
Given an unrestricted (type 0) grammar and a terminal word `w`, is `w` in the language of the grammar? A grammar is given by its code (`GrammarCode T`): a start symbol and a list of rewriting rules over terminals `T` and numbered nonterminals. Its language is the set of terminal words that the start symbol rewrites to (`GrammarCode.language`). `IsType0` is Chomsky's condition that every left side contains a nonterminal. The problem is `DecisionProblem (g, w)` in `Basic.lean`; `EmptyWordProblem g` is the case of the empty word.

Every context-free grammar code is a grammar code of type 0 with the same language (`language_toGrammarCode`, `isType0_toGrammarCode`).

## Layout
* `Basic.lean`: the problem, type 0, context-free codes as grammar codes, and a fresh start symbol (`Start.derives_start`).
* `Undecidable.lean`: `HaltProblem ⪯ₘ` membership (`haltReducesGrammarMem`), so it is `Undecidable` (`undecidableGrammarMem`).
* `MachineLevel.lean`: no Turing machine decides whether the empty word is in the language of a type 0 grammar code (`not_machineDecidable_emptyWord_type0`), nor membership for grammar codes (`not_machineDecidable_grammarMem`), under any computable encoding.

## Proof sketch
The reduction goes through the word problem for string rewriting systems (`SemiThue/`): a machine halts iff its configuration string rewrites to the empty string. A fresh start symbol `0` with the rule `[0] → start string`, and the other symbols numbered from `1`, turn the rewriting system into a grammar code (`ofSRS`). When every rule has a non-empty left side, a derivation from `[0]` must begin with the start rule and never meets `0` again (`Start.derives_start`), so the empty word is in the language iff the start string rewrites to the empty string (`emptyWord_ofSRS_iff`). The grammar codes are of type 0 (`isType0_gCode`), so the result holds for type 0 grammars, which is Chomsky's class of unrestricted grammars.

## References
* N. Chomsky, *On certain formal properties of grammars* (1959)
* J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*
