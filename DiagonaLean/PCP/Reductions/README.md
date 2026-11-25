```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
```
# `PCP.Reductions`: Post's Correspondence Problem Reductions
1. [`MPCP ⪯_s PCP`](#mpcp-ₘ-pcp)
2. [`Halt ⪯_s PCP`](#halt-ₘ-pcp)

## `MPCP ⪯_s PCP`
Given an MPCP instance `(c, R)` (a distinguished tile `c` and a stack `R`), we construct a PCP instance `mpcpToPcp c R` such that `MPCP.Solvable c R ↔ PCP.DecisionProblem (mpcpToPcp c R)` (`mpcp_iff_pcp`). `mpcp_reducesto_pcp_spec` restates it as the many-one reduction `MPCP.DecisionProblem ⪯_s[fun x => mpcpToPcp x.1 x.2] PCP.DecisionProblem` on pairs `(c, R)`.

### Alphabet Extension
The alphabet `α` is extended with two fresh markers, `Ext α = α | ⋕ | ₹`, where `{⋕,₹} ∩ α = ∅` by construction. A letter `a : α` is lifted to `↟a : Ext α`.

### Interleaving Functions
Two functions interleave `⋕` into a word:
```
hashL [a₀, …, aₙ] = [⋕, ↟a₀, ⋕, ↟a₁, …, ⋕, ↟aₙ]
hashR [a₀, …, aₙ] = [↟a₀, ⋕, ↟a₁, ⋕, …, ↟aₙ, ⋕]
```
They satisfy the duality
```
hashL x ++ [⋕] = ⋕ :: hashR x
```
This identity (`hashL_snoc_eq`) is what allows the end tile to close a solution.

### Tile Construction
Three tile roles are assigned:

| Tile | Top | Bottom | Role |
|---|---|---|---|
| `tileStart c` | `₹ :: hashL c.top` | `₹ :: ⋕ :: hashR c.bot` | Forces every solution to start here |
| `tileReg t` | `hashL t.top` | `hashR t.bot` | Encodes one MPCP card |
| `tileEnd` | `[⋕, ₹]` | `[₹]` | Closes the match via `hashL_snoc_eq` |

The reduced instance is thus:
```
mpcpToPcp c R = tileStart c :: regsOf (c :: R) ++ [tileEnd]
```
Here, `regsOf` filters out empty cards (which would otherwise produce spurious solutions).

### Forward Direction (`mpcp_to_pcp_solution`)
Given an MPCP solution `A` with `c.top ++ τ1 A = c.bot ++ τ2 A`, the PCP solution is `tileStart c :: regsOf A ++ [tileEnd]`. Its two rows are
```
τ1 = ₹ :: hashL c.top ++ τ1 A ++ [⋕, ₹]
τ2 = ₹ :: ⋕ :: hashR c.bot ++ τ2 A ++ [₹]
```
Since `c.top ++ τ1 A = c.bot ++ τ2 A` and `hashL_snoc_eq` converts the trailing `[⋕, ₹]` on the top into the leading `⋕` on the bottom, the two sides match.

### Backward Direction (`pcp_to_mpcp_solution`)
`match_start`: any matching PCP solution must begin with `tileStart c`. The argument is by character analysis:
- All tile tops begin with `₹` (start tile), `⋕` (regular or end tile), or are empty.
- All tile bottoms begin with `₹` (start or end tile), `↟a` (regular tile), or are empty.
- A regular tile as the first tile would force `τ1` to begin with `⋕` and `τ2` to begin with `↟a`, which cannot match.
- The end tile as the first tile forces an immediate contradiction.

(`pcp_to_mpcp_solution_gen`): after stripping the start tile, the residual satisfies
```
hashL c.top ++ τ1 B' = ⋕ :: hashR c.bot ++ τ2 B'
```
The generalized lemma proceeds by induction on the remaining stack, maintaining a matching state `(u, v)` for accumulated tops and bottoms:
- Start tile midstream: ruled out by `hashL_append_rupee_ne`.
- End tile: `hashR_append_rupee_inj` forces `u = v`, closing the match with an empty MPCP solution.
- Regular tile `tileReg s`: extend `u ← u ++ s.top` and `v ← v ++ s.bot` and recurse.

## `Halt ⪯_s PCP`
`Halt_to_PCP.lean` composes `Halt ⪯_s MPCP` with `MPCP ⪯_s PCP`. The machine is first normalized (`Foundations/Computability/Normalize/`) so that it meets the side conditions of the MPCP reduction, and the states of the machine are encoded as natural numbers (`pcpRed`, `pcpRed_iff`). `AlphabetLift` then lifts the instance to the fixed alphabet `Ext (Alpha ℕ Bool)`. The reduction function is `haltToPcp`, `halt_reducesto_pcp_spec` gives `HaltProblem ⪯_s[haltToPcp] PCP.DecisionProblem`, and `PCP.synthFromHalt` packages it.

### Undecidability
`Undecidable.lean` collects `PCP.synthFromHalt`, which states that PCP over the fixed alphabet `Ext (Alpha ℕ Bool)` is synthetically halting-hard, and `PCP.synthFromHaltOver b0 b1 hne`, which transports it along `PCP.synthAlphabetLift` to any alphabet with two distinct letters `b0` and `b1`. `MachineLevel.lean` collects the halting reductions `PCP.fromHalt` and `PCP.fromHaltOver`, from `MPCP.fromHalt` along `mpcpToPcp` and `liftInstance`, which are primitive recursive (`mpcpToPcp_primrec`, `liftInstance_primrec`), and from them `PCP.haltHard`, `PCP.not_computablePred` and `PCP.not_machineDecidable` (`halt_results`): over any nontrivial `Primcodable` alphabet, PCP is halting-hard, not a computable predicate, and no Turing machine decides it under any computable encoding.
