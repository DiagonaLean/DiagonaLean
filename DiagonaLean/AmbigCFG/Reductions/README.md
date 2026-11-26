```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 4.6, Akhilesh Balaji
```
# `AmbigCFG.Reductions`: Deciding the ambiguity of CFGs
1. [`PCP ⪯_s AmbigCFG`](#pcp-ₘ-ambigcfg)

## `PCP ⪯_s AmbigCFG`
Given a PCP instance `P : Stack α`, construct a context-free grammar `P.toGrammar` such that `PCP.DecisionProblem P ↔ AmbigCFG.DecisionProblem P.toGrammar` (`pcp_iff_ambigcfg`).

The grammar `P.toGrammar` has three nonterminals:

| Nonterminal | Role |
|---|---|
| `S` | fresh start symbol |
| `A` | generates top-word encodings |
| `B` | generates bottom-word encodings |

The terminal alphabet is `α ⊕ Fin P.length`: original symbols on the `.inl` side and one index token `aᵢ` per tile on the `.inr` side.

The rules are:
```
S → A    S → B

A → top(i).inl ++ A ++ [aᵢ]     (for each tile i)
A → top(i).inl ++ [aᵢ]

B → bot(i).inl ++ B ++ [aᵢ]     (for each tile i)
B → bot(i).inl ++ [aᵢ]
```
A derivation from `A` tracing tiles `i₁, i₂, …, iₖ` produces:
```
encodeA [i₁, …, iₖ] = τ1([i₁, …, iₖ]).inl ++ [aᵢₖ, …, aᵢ₁]
```
and symmetrically from `B` with `τ2`. The index tokens appear in reverse order because the recursive rule adds `aᵢ` to the right at each step.

### Forward Direction (`ambiguous_if_pcp`)
Given a solution `A` with `τ1 A = τ2 A`, find an index list `is` with `is.map (P[·]) = A`. Then `encodeA is = encodeB is` (since `τ1` and `τ2` agree on `A`). Build two distinct parse trees:
```
S → A → encodeA is      (via buildA is)
S → B → encodeB is      (via buildB is)
```
Both yield the same word but have different root rules (`S → A` vs `S → B`), so the grammar is ambiguous.

### Backward Direction (`pcp_if_ambiguous`)
Two distinct `S`-rooted parse trees with equal yield are obtained from `ptS_inv`. They cannot both go via `S → A` or both via `S → B` because:
- **`A`-subtrees are determined by their yield** (`ptA_yield_inj`): by the canonical form `ptA_char`, every `A`-tree equals `buildA is` for some `is`, and by `buildA_yield` its yield is `encodeA is`, which is injective (`encodeA_injective`).
- **`B`-subtrees are determined by their yield** (`ptB_yield_inj`): similarly via `buildB` and `idxOf_encodeB`.

So one tree goes via `S → A` (child yielding `encodeA is₁`) and the other via `S → B` (child yielding `encodeB is₂`). Equal yields give `encodeA is₁ = encodeB is₂`. The **cross-equality lemma** (`encodeA_eq_encodeB_cross`) then forces `is₁ = is₂` and `τ1 (is₁.map P[·]) = τ2 (is₁.map P[·])`, witnessing a PCP solution.

### Auxiliary lemmas

| Lemma | Statement |
|---|---|
| `encodeA_eq_encodeB_iff` | `encodeA is = encodeB is ↔ τ1 A = τ2 A` |
| `encodeA_eq_encodeB_cross` | `encodeA is = encodeB js → is = js ∧ τ1 A = τ2 A` |
| `encodeA_injective` | `encodeA` is injective |
| `ptA_char` / `ptB_char` | every `A`/`B`-tree is canonical |
| `ptA_yield_inj` / `ptB_yield_inj` | `A`/`B`-trees determined by yield |
| `rule_shape` | every rule has one of six explicit shapes |

An instance bundles the grammar with the number of tiles of the PCP instance (`AmbigCFGInstance`), so that all instances share one type. The reduction `pcpToAmbigCFG` sends `P` to `⟨P.length, Stack.toGrammar P⟩`, `pcp_reducesto_ambigCFG_spec` states `PCP.DecisionProblem ⪯_s[pcpToAmbigCFG] (fun G => AmbigCFG.DecisionProblem G.2)`, and `AmbigCFG.synthFromPCP` packages the two.

### Undecidability
`Undecidable.lean` collects `AmbigCFG.synthFromHaltOver b0 b1 hne`: CFG ambiguity is synthetically halting-hard over any alphabet with two distinct letters `b0` and `b1`. It is obtained with `reduce_from_pcp` from `AmbigCFG.synthFromPCP`.

### Machine level
Mathlib's `ContextFreeGrammar` is not `Primcodable`, so `MachineLevel.lean` states the results for grammar codes over the terminals `α ⊕ ℕ` (`Foundations.Grammar.CFGCode`). The construction is written once as a presentation polymorphic in the names of its three nonterminals and in the terminals that index the tiles (`ambPres`): with `PCPNonterm` and `Fin n` it presents `Stack.toGrammar` (`toCFG_ambPres_abs`), and with `0, 1, 2` and numbers it is the code `ambCode`, the renaming of the first (`ambCode_eq_map`). `Rename.lean` proves that injective renamings of terminals and nonterminals keep and reflect ambiguity (`decisionProblem_map_iff`): renaming maps parse trees to parse trees (`ParseTree.rename`) and their yields to the renamed yields, and is injective on trees when it is injective on the rules (`ParseTree.rename_inj`); the converse renames back with left inverses. The code is primitive recursive in the PCP instance (`ambCode_prim`), so PCP many-one reduces to the ambiguity of codes (`pcp_reducesto_ambigCFGCode_spec`, `AmbigCFG.synthCodeFromPCP`), and `not_computablePred_ambigCFGCode` and `not_machineDecidable_ambigCFGCode` follow from `PCP.MachineLevel.not_computablePred_pcp`.
