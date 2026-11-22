```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 4.6, Akhilesh Balaji
```
# `MatMort.Reductions`: The `3 × 3` Matrix Mortality Problem
1. [`PCP ⪯ₘ MatMort`](#pcp-ₘ-matmort)

## `PCP ⪯ₘ MatMort`
Given a PCP instance `K : Stack S23` (tiles over `{2, 3} = Fin 2`), define the matrix set
```
H(K) = {S, T} ∪ {W(liftS23 t.top, liftS23 t.bot)   | t ∈ K}
              ∪ {W(liftS23 t.top, 1 :: liftS23 t.bot) | t ∈ K}
```
where:
**`S`** (initialization):
```
S = [[1, 0, 1],
     [0, 0, 0],
     [0, 0, 0]]
```
Left-multiplying by `[a, b, c]` projects the first coordinate and produces `a · [1, 0, 1]`.

**`T`** (termination):
```
T = [[ 1, -1, 0],
     [-1,  1, 0],
     [ 0,  0, 0]]
```
Left-multiplying by `[a, b, c]` produces `(a - b) · [1, -1, 0]`, which is zero iff `a = b`.

**`W(U, V)`** (tile matrix): for words `U, V` over `{1, 2, 3}` with integer values `q = wordToInt U`, `p = 10^|U|`, `s = wordToInt V`, `r = 10^|V|`:
```
W(U, V) = [[p, 0, 0],
            [0, r, 0],
            [q, s, 1]]
```
Left-multiplying by `[wordToInt X, wordToInt Y, 1]` appends `U` to the first coordinate and `V` to the second: `[wordToInt X, wordToInt Y, 1] · W(U, V) = [wordToInt(X ++ U), wordToInt(Y ++ V), 1]`.

Integers are encoded in base 10 using digits `{1, 2, 3}` (so no leading-zero ambiguity), lifted from `{2, 3}` via `liftS23`. The extra `1` prefix in `W(U, 1 :: V)` marks the start tile: the starting vector `[1, 0, 1]` puts a `1` in front of the top words, and the marked tile supplies the matching `1` on the bottom. In Lean, `markedBot` and `markedW` give the bottom word and matrix of a tile with a marker flag, and `tileMats K` is the set of all of them, so `H(K) = matImage K = {S, T} ∪ tileMats K`.

A sequence of `W`-matrices from `H(K)` left-multiplied by `[1, 0, 1]` accumulates the concatenation of top-words in coordinate 0 and bottom-words in coordinate 1 (`row_mul_prod`, `concatenation_mortal`).

### Forward direction (`matmort_of_pcp`)
Given a solution `A = [t₀, t₁, …, tₖ]` with `τ1 A = τ2 A`, build the matrix sequence:
```
S · W(top(t₀), 1 :: bot(t₀)) · W(top(t₁), bot(t₁)) · ⋯ · W(top(tₖ), bot(tₖ)) · T
```
The product with `[1, 0, 1]` yields `[n, n, 1]` for some `n > 0` (since `τ1 A = τ2 A` and both encode to equal integers). By `S_prod_T_eq_zero`, `S · (W-product) · T = 0`.

### Backward direction (`pcp_of_matmort`)
Step 1 (`mortal_extract`): given a set `Ws` of `W`-matrices and any sequence from `{S, T} ∪ Ws` with `[1, 0, 1] · product = 0`, extract a contiguous `W`-only subsequence `Run` satisfying `[1, 0, 1] · Run.prod = [h, h, 1]` for some `h > 0`. The proof is an induction on the sequence that keeps the invariant `ExtractInv` on the current row vector: it is either a nonzero multiple of `[a, b, 1]` reached from `[1, 0, 1]` by the `W`-matrices read since the last `S`, or a nonzero multiple of `[e, f, 0]` with `e > 0 > f`. `S` restores the first form (`ExtractInv.mul_S`), a `W`-matrix keeps either form (`ExtractInv.mul_W'`), and `T` either finds the run, when `a = b`, or moves to the second form (`ExtractInv.mul_T`). Under the invariant the first coordinate is nonzero, so the empty product cannot give zero.

Step 2 (`mortal_iff_exists_prod_of_Ws`): equivalence between mortality and the existence of a `W`-sequence with equal coordinates.

Step 3 (`pcp_if_exists_prod`): from a `W`-sequence with `[1, 0, 1] · prod = [h, h, 1]`, recover the tile sequence. Each matrix is the matrix of a marked or unmarked tile (`exists_marked_of_mem_tileMats`), and the product computes `1` followed by the top words and the marked bottom words (`wProd_markedW`). The base-10 encoding makes `wordToInt` injective (`wordToInt_injective`), so the two words are equal. Removing every `1` from both leaves the lifted top and bottom words, since lifted words contain no `1` (`bots_eq_of_word`); `liftS23` is injective, so `τ1 A = τ2 A`.

The main result is `pcp_iff_matmort`: for any PCP instance `K` over alphabet `{2, 3}`, `K` has a solution iff the matrix set `H(K)` is mortal. `pcp_reducesto_matMort_spec` restates it as `PCP.DecisionProblem ⪯ₘ[matImage] MatMort.DecisionProblem`, and `pcpReducesMatMort` packages it as a many-one reduction.

### Undecidability
- `undecidableMatMort`: mortality of finite sets of `3 × 3` integer matrices is `Undecidable`, by reduction from PCP over `{2, 3}`.
- `not_computablePred_matMort`, `not_machineDecidable_matMort` (`MachineLevel.lean`): it is not a computable predicate, so no Turing machine decides it under any computable encoding. They follow from `PCP.MachineLevel.not_computablePred_pcp` along `pcpReducesMatMort`, whose function `matImage` is primitive recursive (`matImage_primrec`).
