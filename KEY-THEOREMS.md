# Key definitions, theorems and tactics

A map of what you reach for when proving a problem undecidable in DiagonaLean: the notions,
the theorems that connect them, the tactics, and the pitfalls that cost time. Names are as on
`feat/phase3` (2026-11-23); `scripts/rename-packages.tsv` lists the former names (their deprecated
aliases were removed on 2026-11-27). The rules a result must follow are in [CONTRIBUTING.md](CONTRIBUTING.md).

## 1. Two layers of reductions

Every reduction is a function plus a proof that it reduces `p` to `q`. The two layers differ in how
the function's computability is certified.

| notation | definition | kind | meaning |
|---|---|---|---|
| `p ⪯_s[f] q` | `ReducesVia f p q` | `Prop` | `∀ x, p x ↔ q (f x)`; nothing about `f` |
| `p ⪯_s q` | `SynthReduction p q` | data | synthetic: `f` is computable because Lean compiles it (checked by `#check_reductions`) |
| `p ⪯[f] q` | `ComputablyReducesVia f p q` | `Prop` | `Computable f ∧ p ⪯_s[f] q` |
| `p ⪯ q` | `ComputableReduction p q` | data | proved: carries `Computable f`, kernel-checked |
| — | `ManyOneReducible p q` (Mathlib) | `Prop` | `∃ f, p ⪯[f] q` (`manyOneReducible_iff_exists`) |

`_s` reads "no proof of computability attached". Reductions are data (`Type`), so they are `def`s,
never `theorem`s; the correctness proof inside is the theorem (`src_reducesto_tgt_spec`).

**Halting reductions.**

| | synthetic | proved |
|---|---|---|
| source | `HaltProblem` (machines `EncodableTM Bool × List Bool`, not `Primcodable`) | `HaltCanon` (canonical machines `CanonTM × List Bool`, `Primcodable`) |
| reduction | `SynthHaltReduction P := HaltProblem ⪯_s P` | `HaltReduction P := HaltCanon ⪯ P` |
| hardness | — | `HaltHard P := Nonempty (HaltReduction P)` (a `Prop`, allowed) |

Files: `Synthetic/Definitions.lean`, `Synthetic/HaltReduction.lean`,
`Foundations/Computability/ComputableReduction.lean`, `Foundations/Computability/HaltCanon.lean`.

## 2. Moving between the layers

| from | to | by |
|---|---|---|
| `s : p ⪯_s q`, `h : Computable s.f` | `p ⪯ q` | `ComputableReduction.ofSynth s h` |
| `c : p ⪯ q` | `p ⪯_s q` | `c.toSynth` |
| `h : p ⪯[f] q` | `p ⪯ q` | `ComputableReduction.ofRed h`; back: `c.red` |
| `h : HaltReduction P` | `SynthHaltReduction P` | `h.toSynthHalt` (through the fixed bridge `synthHaltToCanon : HaltProblem ⪯_s HaltCanon`) |
| `h : HaltReduction p`, `r : p ⪯ q` | `HaltReduction q` | `h.trans r` |
| `h : SynthHaltReduction p`, `r : p ⪯_s q` | `SynthHaltReduction q` | `h.comp r` (`SynthHaltReduction.comp`) |
| `p ⪯_s q`, `q ⪯_s r` | `p ⪯_s r` | `SynthReduction.trans`; also `.refl`, `.compl` |

One synthetic step makes a chain synthetic. A proved halting reduction can only come from a proved
root (from `HaltCanon`); proving the last link computable does not upgrade a synthetic root.

## 3. From hardness to "no machine decides it"

| theorem | statement |
|---|---|
| `HaltHard.not_computablePred` | `HaltHard P → ¬ ComputablePred P` |
| `HaltHard.not_machineDecidable` | `HaltHard P → Computable enc → ¬ MachineDecidable enc P` |
| `haltHard_iff` | `HaltHard P ↔ ManyOneReducible HaltCanon P` |
| `not_computablePred_haltCanon` | `¬ ComputablePred HaltCanon` |
| `not_computablePred_of_reduces` | `r : p ⪯_s q`, `Computable r.f`, `¬ ComputablePred p` → `¬ ComputablePred q` |
| `not_computablePred_of_selfHalt` | a computable map of machine codes that reduces self-halting gives `¬ ComputablePred` (the older route; new results go through `HaltHard`) |
| `not_machineDecidable_of_not_computablePred` | `Computable enc → ¬ ComputablePred P → ¬ MachineDecidable enc P` |
| `not_computablePred_of_bitsPair` | for an encoding `bitsPair (c a) (c b)` (the binary digits of a pair of codes) with a primitive recursive decoder `d` of `c`: `¬ MachineDecidable` under it gives `¬ ComputablePred` (used for SKI, β and KAComm; decoders `skcDec`, `tcDec`, `rcDec` from `TaggedCode.decode`, and `rcbDec` for KAComm over `Bool`, `KleeneAlgebra/BoolCode.lean`) |
| `machineDecidable_iff` | `MachineDecidable enc P ↔ ComputablePred P`, for a computable `enc` with a computable decoder `dec` (`dec (enc x) = some x`; `MachineBridge.lean`) |
| `ComputableReduction.manyOneReducible` | `p ⪯ q → ManyOneReducible p q` |
| `REPred.of_reduces`, `REPred.of_manyOneReducible` | r.e.-ness pulls back along reductions |

## 4. Alphabets: functors on codes

A problem whose instances are built from letters is a `CodeFunctor` (`Foundations/Codes/Functor.lean`):
encoding the letters by a good code preserves and reflects the problem. Then

| theorem | gives |
|---|---|
| `CodeFunctor.lift b0 b1 hne` | `F.Prob (over α) ⪯_s F.Prob (over β)` for two distinct letters of `β` |
| `CodeFunctor.undecidableOf` | a synthetic halting reduction over every alphabet with two letters |
| `CodeFunctor.not_computablePred_lift` | `¬ ComputablePred` over every nontrivial `Primcodable` alphabet |
| `CodeFunctor.manyOneEquiv` | the problem is many-one equivalent over any two nontrivial alphabets |
| `CodeFunctor.computableLift`, `haltReductionOf`, `haltHard_lift` | the proved versions, given `Computable (F.liftMap b0 b1)` (`ComputableLift.lean`) |

Functors in use: `mpcpFunctor`, `pcpFunctor`, `semiThueFunctor` (synchronizing codes, systems with
non-empty left sides), `ambCodeFunctor`. The letters are data, so a definition takes `b0 b1 hne`
explicitly (`…Over b0 b1 hne`); `Nontrivial α` is enough only for `Prop` results.

## 5. Tactics and commands

| tactic | use |
|---|---|
| `synth_reduce_from h with f [unfold \| using spec \| using fwd bwd]` | closes `SynthHaltReduction q` from a synthetic halting reduction `h` to `p` and a function `f` with `p ⪯_s[f] q`: the link is built from `f` and its correctness, with no bundled definition. With no `using`, leaves `forward` (`x`, `hp`) and `backward` (`x`, `hq`). `f` is checked at tactic time to be a compiled program. `h` may be a problem, found as `synthFromHalt`/`synthFromHaltBool` in its namespace. (`Foundations/Computability/ReduceFrom.lean`) |
| `hard_reduce_from h with f …` | the same forms for `HaltReduction q`, `HaltHard q`, `¬ ComputablePred q`, `¬ MachineDecidable enc q`: the link is `⟨f, Computable f, proof⟩`, `Computable f` closed by `fun_prop` or left open. `h` is a `HaltReduction`, `HaltHard p` (not for the data goal), `¬ ComputablePred p`, or a problem registered with `HaltSource` (data) / `HaltHardFact` (a proposition). `reduce_from h with …` picks between the two by the goal. Applied terms after `with`/`using` need parentheses. (`Foundations/Computability/ReduceFrom.lean`) |
| `hard_reduce_from h with f₁ using s₁, via r, with f₂ …` | a chain: links separated by commas, each `with f …` or `via r`, composed in order; also for `synth_reduce_from` and `reduce_from`. On a hard goal one computability goal per function or synthetic link, tagged `computable_f` (or `computable_i`). Every link but the last needs `using`. (`Foundations/Computability/ReduceFrom.lean`) |
| `upgrade s` | from a synthetic halting reduction `s : SynthHaltReduction q`, proves `HaltReduction q`, `HaltHard q`, `¬ ComputablePred q` or `¬ MachineDecidable enc q`: cuts the chain of `s` at the last problem with a proved halting reduction (`foo` for `synthFoo`, same explicit arguments; a hypothesis; `HaltSource`), and upgrades the synthetic links after it, one `Computable f` goal per link tried with `fun_prop` (tags as for chains). Errors name the chain when no cut exists, and a link whose types are not `Primcodable`. (`Foundations/Computability/Upgrade.lean`) |
| `reduce_from h via r` | closes `SynthHaltReduction q`, `HaltReduction q`, `HaltHard q`, `¬ ComputablePred q`, `¬ MachineDecidable enc q` from a halting reduction `h` to `p` and a link `r : p ⪯_s q` or `p ⪯ q`. The goal picks the layer. A synthetic link is upgraded with `ofSynth`, and its `Computable r.f` is closed by `fun_prop` when the link's function has a lemma. A synthetic `h` with a proved goal is an error. (`Foundations/Computability/ReduceFrom.lean`) |
| `halt_results P from r` | a command: from `r : HaltReduction P`, states the theorems `haltHard`, `not_computablePred` and `not_machineDecidable` in the current namespace. `halt_results P over_letters from r` states them over every nontrivial alphabet, from `r b0 b1 hne` (`HaltHard.of_letters`); `halt_results Name for …` puts them under `Name`. (`Foundations/Computability/HaltResults.lean`) |
| `code_lift F from h` | lifts `h` over the source alphabet to the goal's alphabet. A halting reduction `h` goes through `reduce_from h via` the lift (synthetic `F.lift` or proved `F.computableLift`, by the goal), so every `reduce_from` goal works, e.g. `HaltReduction (@MPCP.DecisionProblem α)` from `MPCP.fromHalt`; `h : ¬ ComputablePred` gives `¬ ComputablePred` and `¬ MachineDecidable`; `code_lift F` alone proves `ManyOneEquiv`. Needs `hne : b0 ≠ b1` in context for a halting reduction. (`Foundations/Codes/Tactic.lean`) |
| `reduce_from_pcp over_letters b0 b1 with f …` | `synth_reduce_from (PCP.synthFromHaltOver b0 b1 _) with f …`, the letters and `b0 ≠ b1` found automatically; `via R` is the older form |
| `fun_prop` | `Primrec`, `PrimrecPred`, `Computable` goals, from registered lemmas (`Foundations/Computability/Prim.lean`, `IntPrim.lean`, `MatrixPrim.lean`, `FinsetPrim.lean`) |
| `derive_primrec f [inst…]` | command: states `Primrec fun x : A₁ × A₂ => f x.1 x.2`, proves it by `unfold f; fun_prop`, registers it as `f_prim` with `@[fun_prop]` |
| `primrec_rec` | tactic for structural recursion on `ℕ`, `List`, or a type with `derive_primcodable`: `@[fun_prop] theorem f_primrec : Primrec f := by primrec_rec` |
| `derive_primcodable T` | command: `Primcodable T` for an inductive type (fields `T`, `List T`, `Option T`, `Primcodable` data), with constructor lemmas and `T.primrec_of_eqns` |
| `tm_computes F`, `tm_computer F` | a Turing machine computing a function (`Foundations/Computability/Computer.lean`) |
| `#check_reductions` (`local`) | checks every reduction's dependency closure for escape hatches; run by CI on the whole library |

## 6. Problems and their predicates

Every problem has a one-argument predicate `X.DecisionProblem` (an object of the category of
problems); proofs may use a curried form. MPCP: `MPCP.Solvable c P` (curried, used by the proofs)
and `MPCP.DecisionProblem (c, P)` (`decisionProblem_iff`, by `rfl`). Headline abbreviations at a
fixed type remain (`HaltProblem`, `MPCProblem`, `PCProblem`, KAComm `…BoolProblem`); the
duplicates `MatMortProblem`, `AmbigCFGProblem` and `EmpCFGProblem` were removed.

**Package names** live in the target's namespace: `Tgt.synthFromSrc` (a link), `Tgt.synthFromHalt`
(a halting reduction), `…Over b0 b1 hne`, `…Bool`, `synthCompl…` (the complement),
`X.synthAlphabetLift`; proved versions drop `synth` (`MPCP.fromHalt`, `MPCP.haltHard`).

**Proved halting reductions** (`HaltReduction`, 2026-11-23): the root `MPCP.fromHalt` (over
`Alpha ℕ Sym2`, through `canonInst = instOf c.start c.table w`, `MPCP/Hardness.lean`), and from it
`MPCP.fromHaltOver`/`…Bool`, `PCP.fromHalt`/`…Over`/`…Bool`, `MatMort.fromHalt`,
`EmpCFG.codeFromHaltTerm`, `AmbigCFG.codeFromHaltSum` (fixed terminal shapes) and, lifted to grammar
codes over every alphabet with two letters, `EmpCFG.codeFromHaltOver`, `AmbigCFG.codeFromHaltOver`.
Each problem states its consequences with `halt_results` (`X.haltHard`, `X.not_computablePred`,
`X.not_machineDecidable`, with a prefix such as `SemiThue.Pos.` or `EmpCFG.Code.` for a second
problem in the namespace). A second root from `HaltCanon`,
on the same table construction: `SemiThue.posFromHalt`/`…Over`, `SemiThue.fromHaltOver`/`…Bool`,
`SemiThue.toEmptyFromHalt` (`SemiThue/Hardness.lean`, through `canonToEmpty`), and from it
`GrammarMem.emptyWordFromHalt`, `GrammarMem.fromHalt`. Constructions on tables share
`MPCP.MachineLevel.SameTable` (same lookup, same state numbers) and `CanonTM.sameTable`. Still only
synthetic: the grammar problems on
Mathlib's `ContextFreeGrammar` (not `Primcodable`), and KAComm, Rice (their reductions take
classically obtained constants). Their `¬ ComputablePred` results are kernel-checked all the same.
SKI and β are halting-hard all the same (`SKIConv.haltHard`, `BetaConv.haltHard`, in their
`Hardness.lean`): `HaltHard` is a
proposition, so the constants are obtained inside its proof, and the reduction from canonical
machines (`SKIConv.fromHaltWith U C …`, through `dataCanon` and `ProofRace.haltCanon_iff` in
`Foundations/Computability/CanonRace.lean`) is proved computable for each choice of them.

## 7. Pitfalls that cost time

* **`abbrev` link functions.** `fun_prop` unfolds reducible definitions before it looks up a
  lemma, so a lemma about an `abbrev` never fires. Make link functions `def`s with a
  `@[fun_prop]` lemma (`matImage` was an `abbrev` until 2026-11-23).
* **State `Primrec` lemmas uncurried for `fun_prop`.** `Primrec₂ f` is not what `fun_prop`
  matches; `derive_primrec` states `Primrec fun x => f x.1 x.2`. Keep a `Primrec₂` corollary if
  callers want one (`mpcpToPcp_primrec := mpcpToPcp_prim`).
* **`variable`s end with their namespace.** Re-opening `namespace Reduction` after an `end`
  needs the `variable {α} [Primcodable α]` again.
* **`Nat.pair` on literals** makes unification evaluate huge numbers: `attribute [local
  irreducible] Nat.pair` (as in `KAComm/KleeneAlgebra/Between.lean`).
* **Aliases.** An old name for data is `@[deprecated New (since := …)] abbrev old := @New`. An
  `alias` of a lemma breaks field notation on terms typed with the old name; restate the lemma.
* **Deprecations inside macros** are reported at the macro's call site, not at the name.
* **Packages declared from another namespace** use `def _root_.DiagonaLean.Tgt.synthFromSrc`,
  which keeps the file's `variable`s and `open`s.
* **Existence claims.** `∃ f, p ⪯_s[f] q` and `Nonempty (p ⪯_s q)` are vacuous and rejected;
  `HaltHard P` and `∃ f, p ⪯[f] q` (= `ManyOneReducible`) are meaningful and allowed.
* **No `native_decide`, `partial`, `implemented_by`, `sorry`, `noncomputable`** anywhere a
  reduction depends on (CONTRIBUTING 4).

## 8. Checking your work

* `lake build` for the library; `lake env lean scripts/ReduceFromTest.lean` (and the other
  `scripts/*Test.lean`) for the tests.
* `scripts/ci-local.sh` runs everything CI runs (about 4 minutes: build, metaprogram and layering
  checks, lint, `fun_prop` tests, `#check_reductions` and its tests); `--style-only` checks the
  100-character limit on added lines in seconds.
* Run the full check once per coherent batch of changes, not after every small edit; it is the
  `reductions` step that takes the time.
