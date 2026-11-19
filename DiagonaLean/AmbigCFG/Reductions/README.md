```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 4.6, Akhilesh Balaji
```
# `AmbigCFG.Reductions`: Deciding the ambiguity of CFGs
1. [`PCP ⪯ₘ AmbigCFG`](#pcp-ₘ-ambigcfg)

## `PCP ⪯ₘ AmbigCFG`
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

An instance bundles the grammar with the number of tiles of the PCP instance (`AmbigCFGInstance`), so that all instances share one type. The reduction `pcpToAmbigCFG` sends `P` to `⟨P.length, Stack.toGrammar P⟩`, `pcp_reducesto_ambigCFG_spec` states `PCP.DecisionProblem ⪯ₘ[pcpToAmbigCFG] (fun G => AmbigCFG.DecisionProblem G.2)`, and `pcpReducesAmbigCFG` packages the two.

### Undecidability
`Undecidable.lean` collects `undecidableAmbigCFG b0 b1 hne`: CFG ambiguity is `Undecidable` over any alphabet with two distinct letters `b0` and `b1`. It is obtained with `reduce_from_pcp` from `pcpReducesAmbigCFG`.
