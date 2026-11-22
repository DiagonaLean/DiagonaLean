```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 4.6, Akhilesh Balaji
```
# `EmpCFG.Reductions`: Deciding the Emptiness of the Intersection of CFGs
1. [`PCP ⪯_s EmpCFG`](#pcp-ₘ-empcfg)

## `PCP ⪯_s EmpCFG`
Given a PCP instance `P : Stack α`, construct two single-nonterminal grammars `topCFG P` and `botCFG P` over the terminal alphabet `α ⊕ Tile α`, where `α`-symbols sit on the `.inl` side and tile markers on the `.inr` side.

Each grammar has two rules per tile `t ∈ P`:

| Grammar | Recursive rule | Base rule |
|---|---|---|
| `topCFG` | `S → t.top.inl ++ S ++ [⌊t⌋]` | `S → t.top.inl ++ [⌊t⌋]` |
| `botCFG` | `S → t.bot.inl ++ S ++ [⌊t⌋]` | `S → t.bot.inl ++ [⌊t⌋]` |

where `⌊t⌋` denotes `Sum.inr t`. The recursive rule shape forces outer tiles to sit at the outer ends: a derivation from `S` tracing tiles `t₁, t₂, …, tₖ` produces the canonical string,
```
τ(A).map Sum.inl ++ A.reverse.map Sum.inr
```
where `τ` is either `τ1` (for `topCFG`) or `τ2` (for `botCFG`).

### Forward Direction (`PCP.DecisionProblem P → IntersectionNonempty (topCFG P) (botCFG P)`)
Given a PCP solution `A` with `τ1 A = τ2 A`, both grammars derive the same canonical string `canonString Tile.top A = canonString Tile.bot A`. Hence, the intersection is nonempty.

### Backward Direction (`IntersectionNonempty (topCFG P) (botCFG P) → PCP.DecisionProblem P`)
The language characterization (`mem_language_iff_canonString`) shows that every word in `(genCFG proj P).language` is `canonString proj A` for some nonempty `A ⊆ P`. This is proved via the `Form` invariant: any string reachable from `[S]` is either in the intermediate form
```
embedA (τProj proj A) ++ [S] ++ embedT A.reverse
```
or the terminal form `embedA (τProj proj A) ++ embedT A.reverse`. The invariant is preserved by each `Produces` step by case analysis on the applied rule.

Given a word `w` in both languages, we get stacks `A_top` and `A_bot` with `canonString Tile.top A_top = canonString Tile.bot A_bot`. The `.inl`/`.inr` split lemma (`list_inl_inr_split`) uniquely decomposes the shared word, forcing `τ1 A_top = τ2 A_bot` and `A_top = A_bot`; hence, a PCP solution.

Both directions together are `pcp_iff_nempcfg`: `PCP.DecisionProblem P ↔ IntersectionNonempty (topCFG P) (botCFG P)`. Its negation, with `IntersectionEmpty`, is `npcp_iff_empcfg`. The reduction `pcpToEmpCFG` sends `P` to `(topCFG P, botCFG P)`, `pcp_reducesto_empCFG_spec` states `PCP.DecisionProblem ⪯_s[pcpToEmpCFG] EmpCFG.DecisionProblem`, and `EmpCFG.synthFromPCP` packages the two.

### Undecidability
`Undecidable.lean` collects `EmpCFG.synthFromHaltTerm b0 b1 hne`: the nonemptiness of the intersection of two CFGs (`EmpCFG.DecisionProblem`) is synthetically halting-hard over the alphabet `Term α` for any `α` with two distinct letters `b0` and `b1`. It is obtained with `reduce_from_pcp` from `EmpCFG.synthFromPCP`. Encoding the terminals of both grammars by a synchronizing code preserves and reflects non-emptiness of the intersection (`Foundations.Codes.intersection_encode_iff`), so `AlphabetLift.lean` reduces the problem over any countable alphabet to the problem over any alphabet `α` with two distinct letters (`empCFGLift`, `empCFGLift_spec`, `EmpCFG.synthAlphabetLift`). Starting from the countable alphabet `Term Bool`, `Undecidable.lean` also collects `EmpCFG.synthFromHaltOver b0 b1 hne`, undecidability over `α` itself, and `EmpCFG.synthFromHaltBool`, over `Bool`.

### Machine level
Mathlib's `ContextFreeGrammar` has its type of nonterminals as a field, so it is not `Primcodable` and no statement about machines can be made about it. `MachineLevel.lean` states the results for grammar codes (`Foundations.Grammar.CFGCode`: a start symbol and a list of rules over numbered nonterminals). The construction `genCFG` is written once as a presentation polymorphic in the name of its nonterminal (`genPres`): with the name `()` it presents `genCFG` itself (`toCFG_genPres_unit`), and with `0` it is a code, the renaming of the first, with the same language (`language_toCFG_genPres_zero`, from `Foundations.Grammar.language_map_toCFG`). The codes of a PCP instance are primitive recursive in it (`empCode_prim`), so PCP many-one reduces to the problem on codes (`pcp_reducesto_empCFGCode_spec`, `EmpCFG.synthCodeFromPCP`), and `not_computablePred_empCFGCode` and `not_machineDecidable_empCFGCode` follow from `PCP.MachineLevel.not_computablePred_pcp`; `not_computablePred_empCFGCode_empty` and `not_machineDecidable_empCFGCode_empty` are the same for the emptiness of the intersection.
