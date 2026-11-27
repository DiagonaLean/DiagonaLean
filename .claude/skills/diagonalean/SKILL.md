---
name: diagonalean
description: How to write, prove and check Lean 4 code in the DiagonaLean library (undecidability by many-one reductions, on Mathlib and Cslib) — the two layers of reductions (synthetic `⪯_s`, proved `⪯`), the tactics `reduce_from` (with chains of links), `upgrade`, `code_lift`, `fun_prop`, `derive_primrec`, `primrec_rec`, `derive_primcodable`, the command `halt_results`, the key theorems from hardness to "no Turing machine decides it", how to define a problem (objects, one-step relations, Mathlib closures, the curried problem and its pinned unfolding), Primcodable/Primrec proofs, naming of packages, and the compliance rules that `#check_reductions` and CI enforce. Use it for any work in this repository — a new undecidable problem or a change to how one is defined, a new reduction or link, a `Primrec`/`Computable` proof, an alphabet change, a renaming or refactor, a review of a DiagonaLean PR, or fixing a CI failure — even when the request does not name the skill or a tactic.
---

# Working in DiagonaLean

DiagonaLean proves problems undecidable by many-one reductions from the halting problem. A result
is only trusted if CI can check it, so most of what follows is about stating results the way the
checks expect and proving computability with the library's automation instead of by hand.

Read `KEY-THEOREMS.md` (repository root) when you need a name: it is the catalogue of notions,
bridges, theorems and tactics, with files. `CONTRIBUTING.md` has the nine rules a result must
follow. Private planning notes (`*.private.md`, `Synthetic/NOTIONS.md`) are the user's and are
never committed.

## 1. The model to keep in mind

A reduction is **data**: a function and a proof, in `Type`. So it is a `def`, never a `theorem`.

* `p ⪯_s[f] q` (`ReducesVia`): `f` reduces `p` to `q`; a `Prop`. Its theorem is the correctness
  part, named `src_reducesto_tgt_spec`.
* `p ⪯_s q` (`SynthReduction`): synthetic. `f` is computable only in the sense that Lean compiles
  it; `#check_reductions` verifies nothing classical hides in its dependencies.
* `p ⪯[f] q` (`ComputablyReducesVia`) and `p ⪯ q` (`ComputableReduction`): proved. They carry
  `Computable f`, checked by the kernel.
* `SynthHaltReduction P = HaltProblem ⪯_s P`; `HaltReduction P = HaltCanon ⪯ P`;
  `HaltHard P = Nonempty (HaltReduction P)` (a `Prop`).

Why two sources: `HaltProblem`'s machines bundle a type of states, so it is not `Primcodable` and
`Computable` cannot be stated from it. `HaltCanon` (canonical machines, states `Fin n`) is
`Primcodable`, so proved reductions start there. One synthetic step makes a chain synthetic, and a
proved goal needs a proved *root*; proving the last link computable does not fix a synthetic root.

A claim that a reduction merely exists (`Nonempty (p ⪯_s q)`, `∃ f, p ⪯_s[f] q`) is classically
trivial and is rejected by the check. `∃ f, p ⪯[f] q` (Mathlib's `ManyOneReducible`) and
`HaltHard P` include computability and are fine.

## 2. Defining a problem

A result is only as good as the definition of its problem, and a reader audits that definition by
reading `X/Basic.lean`. These rules keep that file short, textbook-shaped and checked. SemiThue
(`Foundations/Rewriting/SRS.lean`, `SemiThue/Basic.lean`) is the model; SKIConv and BetaConv follow
it.

**Where definitions live.**
* `X/Basic.lean` imports only Mathlib, Cslib, other `Basic.lean` files and definition-only
  `Foundations/` files: never proof search, stack machines, `Primcodable` instances or the
  `derive_*` commands. (SKI and λ used to import 200- and 600-line proof searches.)
* A relation that several problems share lives in a definition-only file, apart from what is proved
  about it: `Rewriting/SRS.lean` vs `Grammar/Rewriting.lean`, `CombinatoryLogic/Conv.lean` vs
  `ProofSearch.lean`. `Primcodable` instances go in their own file (`Rewriting/Primcodable.lean`).
  Measure the import closure of a `Basic.lean` after a change; one transitive import took
  `GrammarMem/Basic.lean` from 5 modules to 11.

**Objects.**
* Named fields, not tuples, for the pieces of an instance: `Rule` has `lhs`/`rhs`, `Tile` has
  `top`/`bot`. A role gets a reducible name, `abbrev Word T := List T`, so the `List` API applies.
  An instance of three or more components gets one too: `abbrev Instance T := SRS T × Word T × Word T`.
* A finite collection that reductions read is a `List`, not a `Finset` (`Finset.toList` is
  noncomputable); a `_congr` theorem says that only the set matters (`wordProblem_congr`).

**Steps and closures.** A rewriting relation has three ingredients: the root rules (what rewrites),
the context (where), and the closure (what the question asks).
* Keep them visibly apart. Cslib's λ-calculus is the model: `Beta` is the redex, `Xi` the compatible
  closure, `ReflTransGen` the iteration. Where one inductive mixes them (Cslib's `SKI.Red`, KAComm's
  `Equiv`), the docstring says which constructors play which part.
* One step is an `inductive` with one constructor per textbook rule, as Mathlib's
  `ContextFreeRule.Rewrites` and Cslib's `SKI.Red`. Prefer the textbook form for the definition
  (`p ++ ρ.lhs ++ q ⭢[R] p ++ ρ.rhs ++ q`), and state the other form as a lemma: `SRS.step_iff`,
  the existential, which proofs use when an endpoint is not a variable (`cases` cannot unify
  `p ++ l ++ q` with `encode c u`).
* Never hand-roll iteration or symmetry: `ReflTransGen` (derivability), `TransGen` (at least one
  step), `EqvGen` (equality modulo the rules), `Join (ReflTransGen r)` (a common reduct, Cslib's
  `MJoin`), each through an `abbrev`, so `.tail`, `.trans`, `head_induction_on` and `cases_head`
  apply unchanged. The exception is an equational theory, a deduction system with congruence over
  a syntax that Mathlib cannot close generically (KAComm's `Equiv`, `KAEquiv`).
* The closure in the definition is the one the question asks; prove the textbook's other form. A
  directed question (does `u` reach `v`?) is `ReflTransGen`. An undirected one, for a confluent
  system, is `Join`, which the reductions produce, with `EqvGen` as a theorem from confluence
  (`convertible_iff_eqvGen`); for a system that is not confluent, `EqvGen`. Never `ReflTransGen`
  for an undirected question.
* Notation: a relation without parameters gets Cslib's `@[reduction_sys "x"]` (`⭢x`, `↠x`); one
  with a parameter gets `scoped notation:50 u:51 " ⭢[" R "] " v:51`, so `++` and `::` bind tighter.
  Notation only abbreviates existing names. Check once that goals print with it.
* Proofs: induct on `ReflTransGen` with `tail`, or `head_induction_on` from the source;
  `cases_head` for the first step; lift a step through context (`Step.append_left`,
  `append_right`), then derivations (`Derives.append`).

**The question.**
* The curried problem comes first, named for the problem (`WordProblem R u v`, `Convertible x y`):
  an `abbrev` when it wraps a relation, a `def` when it adds content (`PosWordProblem`). Variants
  are its specialisations (`ToEmpty R u := WordProblem R u []`). Partially applied it is a set
  (`WordProblem R u`, the words that `u` rewrites to).
* Then, under the heading "The problem on instances, for the reductions and the computability
  statements", the one-argument `DecisionProblem` in one line, by projections, and
  `@[simp] theorem decisionProblem_mk … := Iff.rfl` right after it. Projections give the cleanest
  goals: `Function.uncurry` leaves `simp` stuck, and a pattern match shows `match` in every goal
  that unfolds the problem (tested 2026-11-27).
* A transparency theorem states the curried problem in upstream terms, by `Iff.rfl`
  (`wordProblem_iff`, `convertible_iff`). Pin it and `decisionProblem_mk` in
  `scripts/HeadlineTest.lean`, generated from the compiled types; the module docstring names them as
  the way to audit the definition.
* **Results are stated on the one-argument problem only.** A partially applied curried problem
  type-checks as a different, weaker claim: `Undecidable (DecisionProblem x)` for a curried
  `DecisionProblem` says "convertibility to a fixed `x` is undecidable". A genuine parameter of the
  problem (Rice's set `C`) is the one exception.

**Names.**
* No relation named like a problem namespace (`Foundations.LambdaCalculus.BetaConv` became `Conv`);
  no Mathlib name with another meaning (`Rewrites` is one step in Mathlib); words `u v`, rules
  `l r` or `ρ`.
* A namespace follows the role of its file, never the file's name: `X.Reduction` in `Reductions/`,
  `X.AlphabetLift`, `X` for results. (`X.MachineLevel` outlived its file; its old names are aliases
  in `DiagonaLean/Aliases/MachineLevel.lean`.)

## 3. Adding an undecidable problem: the workflow

1. **The problem.** `X/Basic.lean`, following §2: the curried problem first, then the one-argument
   predicate `X.DecisionProblem : Inst → Prop` in one line, with `decisionProblem_mk` and the
   transparency theorem pinned in `scripts/HeadlineTest.lean`. Never write `fun x => … x.1 x.2` at
   use sites.
2. **The link.** `X/Reductions/Src_to_X.lean`:
   * the function, a `def` (not an `abbrev`, see §6), e.g. `srcToX`;
   * correctness, `theorem src_reducesto_x_spec : Src.DecisionProblem ⪯_s[srcToX] X.DecisionProblem`.
   No bundled package `X.synthFromSrc := ⟨srcToX, spec⟩` is needed: the tactics take the function
   and the spec. Define one only if several results compose it.
3. **Computability of the link** (needed for the proved layer and for machine-level results):
   `derive_primrec srcToX` if `fun_prop` can read its body, or a hand-stated
   `@[fun_prop] theorem srcToX_primrec : Primrec srcToX` (with `primrec_rec` for structural
   recursion). Instances need `Primcodable`: `derive_primcodable` for inductive types.
4. **The results.** The synthetic one in `X/SynthHardness.lean`, the proved ones in
   `X/Undecidable.lean` (MatMort is the model). Constructions, including the link from
   `HaltCanon` (`X/Reductions/HaltCanon_to_X.lean`), stay in `Reductions/`:
   ```lean
   def X.synthFromHalt : SynthHaltReduction X.DecisionProblem := by
     synth_reduce_from (Src.synthFromHaltOver b0 b1 hne) with srcToX using src_reducesto_x_spec

   def X.fromHalt : HaltReduction X.DecisionProblem := by
     hard_reduce_from (Src.fromHaltOver b0 b1 hne) with srcToX using src_reducesto_x_spec

   halt_results X.DecisionProblem from X.fromHalt   -- X.haltHard, …
   ```
   `hard_reduce_from` closes `Computable srcToX` with its `fun_prop` lemma. From PCP,
   `reduce_from_pcp over_letters b0 b1 with srcToX using spec` does the synthetic one.
5. **Alphabets.** If instances are built from letters, give a `CodeFunctor` and use
   `code_lift F from h` for every nontrivial alphabet (`…Over b0 b1 hne`, `…Bool`).
6. **Register it.** Import the new modules from `DiagonaLean.lean`: the check covers only what the
   root imports. Update the folder's `README.md`.
7. **Check.** §7.

Names: packages in the target's namespace, `Tgt.synthFromSrc`, `Tgt.synthFromHalt`,
`…Over b0 b1 hne`, `…Bool`, `synthCompl…` for a complement, `X.synthAlphabetLift`; proved versions
drop `synth` (`MPCP.fromHalt`). The letters are data, so a `def` takes them explicitly; it cannot
extract them from `Nontrivial α` (a `Prop`).

## 4. The tactics, and what they need from you

* **`reduce_from h via r`** reads the goal to choose the layer. It leaves `Computable r.f` (when it
  upgrades a synthetic link) and `Computable enc` only if `assumption` and `fun_prop` fail. Before
  `fun_prop` it reduces `r.f` to the *named* function `r` was built from (`unfoldField`), so a
  `@[fun_prop]` lemma on that function is all it needs. The source may also be a negative result
  `h : ¬ ComputablePred p`; it then proves `¬ ComputablePred q` and `¬ MachineDecidable enc q`
  (through `ComputableReduction.not_computablePred`, or `not_computablePred_of_reduces` for a
  synthetic link) and nothing else. `h` and `r` are arbitrary terms (applied
  definitions, hypotheses, `.trans` chains), not only names. The bare correctness theorem is not a
  reduction; pass `⟨_, spec⟩`, or on a synthetic goal use `with` (next).
* **`synth_reduce_from h with f …`** (synthetic goals `SynthHaltReduction q` only; proved goals take
  `reduce_from … via`): the link is built from the function and its correctness, as the original
  `reduceFromPCP` did, with no bundled `synthFromX` definition needed. `with f` leaves `forward`
  (`x`, `hp : p x`) and `backward` (`x`, `hq : q (f x)`); `with f unfold` also unfolds both problems
  one step; `with f using spec` (`spec : p ⪯_s[f] q`) or `with f using fwd bwd` closes the link with
  a known theorem; `synth_reduce_from h via r` composes a bundled link. `f` must be a program (no
  `noncomputable`, `implemented_by`, `extern`, `opaque`, `partial`, `unsafe`, classical choice): the
  tactic says so. The source `h` may be a **problem** (`@SemiThue.DecisionProblem Bool`): it is
  found in the problem's namespace as `synthFromHalt` or `synthFromHaltBool` (no explicit
  arguments), by name, in `reduce_from … via` too.
  `reduce_from_pcp over_letters b0 b1 with f using spec` (also `using fwd bwd`, `with f`, `with f
  unfold`) is the same with PCP as the source, the letters and `b0 ≠ b1` automatic.
* **`hard_reduce_from h with f …`** is the same for hard goals (`HaltReduction q`, `HaltHard q`,
  `¬ ComputablePred q`, `¬ MachineDecidable enc q`): the link is `⟨f, computable, proof⟩`,
  `Computable f` is tried with `fun_prop` and left open if it fails (stated on `f`, no unfolding of a
  bundled link). The source is a proved `HaltReduction`, the fact `HaltHard p` (not for the data
  goal `HaltReduction q`), `¬ ComputablePred p` (for the two negative goals), or a problem with a
  `HaltSource` / `HaltHardFact` instance (registered: MPCP, PCP and SemiThue over `Bool`, MatMort;
  `instance : HaltSource P := ⟨fromHalt…⟩` next to the `HaltReduction`). `reduce_from h with …`
  chooses between the two tactics by the goal.
* **Chains.** The three tactics take several links separated by commas, each `with f …` or
  `via r`, composed in order:
  ```lean
  hard_reduce_from MPCP.fromHalt via mpcpLink,
    with (liftInstance 0 1) using (pcp_alphabet_lift_spec 0 1 hne),
    with matImage using pcp_reducesto_matMort_spec
  ```
  Every link but the last needs `using` (the intermediate problem is read from it). On a hard goal
  each function or synthetic `via` link gets a `Computable` goal, tagged `computable_f` for a named
  `f` (`computable_i` otherwise; plain `computable` for one link). A synthetic goal accepts a proved
  source.
* **`upgrade s`** (`s : SynthHaltReduction q`) proves the hard goals about `q` from the synthetic
  result: it cuts the chain of `s` at the last problem with a proved halting reduction (the
  counterpart `foo` of `synthFoo` with the same explicit arguments, a hypothesis
  `HaltReduction p`, or `HaltSource p`) and upgrades the links after it, one `Computable f` goal
  per link, tried with `fun_prop`. "Synthetic first, computable later": write the synthetic chain,
  then `def X.fromHalt : HaltReduction X := by upgrade X.synthFromHalt`. It cannot help where no
  problem of the chain has a proved root (SKI, β, KAComm, Rice) or a link's types are not
  `Primcodable` (grammars of Mathlib); the errors say which.
* **`code_lift F from h`**: a halting reduction `h` is composed with the lift by `reduce_from`
  (synthetic `F.lift` or proved `F.computableLift`, chosen by the goal), so it proves every goal
  `reduce_from` does, over any alphabet with two letters (`hne : b0 ≠ b1` in the context); a source
  `h : ¬ ComputablePred` gives `¬ ComputablePred` / `¬ MachineDecidable`; `code_lift F` alone
  proves `ManyOneEquiv`. Its side goal `map_computable` is closed by unfolding `F.liftMap` and
  `fun_prop`.
* **`fun_prop`** proves `Primrec`, `PrimrecPred` and `Computable`. It decomposes an application
  before trying a lemma, and it unfolds reducible definitions. Coverage: `Prim.lean` (lists,
  options, `ℕ`, `Bool`, folds, `Nat.iterate`), `IntPrim.lean`, `MatrixPrim.lean`, `FinsetPrim.lean`.
  When it fails, its message names the operation without a lemma; add the lemma in compositional
  form to the matching `*Prim.lean` file, with a test in `scripts/FunPropTest.lean`.
* **`derive_primrec f [instances]`** is a command: it states the uncurried
  `Primrec fun x : A × B => f x.1 x.2`, proves it by `unfold f; fun_prop`, and registers `f_prim`
  with `@[fun_prop]`. Derive the helpers first (the definitions `f` calls), then `f`.
* **`primrec_rec`**: `@[fun_prop] theorem f_primrec : Primrec f := by primrec_rec` for structural
  recursion on `ℕ`, `List`, or a `derive_primcodable` type.
* **`derive_primcodable T`**: `Primcodable T` plus constructor lemmas, for an inductive type whose
  fields are `T`, `List T`, `Option T` or `Primcodable` data.

Commands that add declarations are allowed only by name (`Synthetic/MetaprogramCheck.lean`);
never use `run_cmd`, `#eval`, `initialize`, `addDecl` or `debug.` options in the library.

### Stating the results: `halt_results`

Once a problem has a proved halting reduction, one command states its consequences:

```lean
halt_results P from r        -- r : HaltReduction P
halt_results P from h        -- h : HaltHard P, when the reduction takes classical constants
```

declares, in the current namespace,

| theorem | statement |
|---|---|
| `haltHard` | `HaltHard P` |
| `not_computablePred` | `Undecidable P` (`¬ ComputablePred P` by definition) |
| `not_machineDecidable` | `{enc} → Computable enc → ¬ MachineDecidable enc P` |

**Where.** In `X/Undecidable.lean`, the file that defines the `HaltReduction`, after the `def`, inside `namespace DiagonaLean.X`, so the names are
`X.haltHard`, `X.not_computablePred` and `X.not_machineDecidable`. Add
`import DiagonaLean.Foundations.Computability.HaltResults`: so far only the root imports it.

**How.** For a new problem with a reduction over every pair of letters and one over `Bool`:

```lean
namespace DiagonaLean.X

variable {α : Type} [Primcodable α] [Nontrivial α]

-- over every nontrivial alphabet, from `fromHaltOver b0 b1 hne : HaltReduction …`
halt_results (@DecisionProblem α) over_letters from fromHaltOver

-- a second statement in the same namespace needs a name: `X.OverBool.not_computablePred`
halt_results OverBool for (@DecisionProblem Bool) from fromHaltBool

end DiagonaLean.X
```

* `over_letters`: the source is the function itself, `fromHaltOver`, not applied to letters. The
  letters come from `Nontrivial α` (`HaltHard.of_letters`), which is possible because the three
  statements are propositions. The reduction stays data and still takes `b0 b1 hne`.
* `Name for`: a second problem (`halt_results Pos for (@DecisionProblemPos α) …`) or a second
  alphabet. Without it Lean reports "already declared". `MPCP`, `SemiThue` and `GrammarMem` already
  have a hand-written `haltHard`, so a new call there needs a name.
* The section's `variable`s become arguments when `P` mentions them. `P` may be a lambda:
  `halt_results (fun c : CFGCode (α ⊕ ℕ) => …) over_letters from …`.
* A source of the wrong kind or for another problem reports a type mismatch, once per theorem.

**When not to use it.**

* There is only a synthetic reduction (`SynthHaltReduction`): it proves none of the three. Make the
  chain proved from a `HaltCanon` root first, by hand or with `upgrade`.
* There is only `HaltHard P` and no `HaltReduction P`: use `.not_computablePred` and
  `.not_machineDecidable` on the fact.
* The result is `¬ ComputablePred` with no halting reduction (SKI, β, KAComm, Rice), or about a
  complement: state it by hand or with `hard_reduce_from`.
* `P` has no `Primcodable` instance type (`HaltProblem`): `HaltReduction P` cannot be stated.
* Every problem with a `HaltReduction` already uses it (2026-11-25): MPCP, PCP, MatMort, SemiThue
  (`SemiThue.Pos.`, `SemiThue.ToEmpty.`), GrammarMem (`GrammarMem.EmptyWord.`), EmpCFG and AmbigCFG
  on grammar codes (`EmpCFG.Code.`, `AmbigCFG.Code.`). The former wrappers
  (`not_computablePred_pcp` and the like) were deleted, not aliased; do not add new ones.

The generated docstrings are generic. Put the citation for the result on the `HaltReduction`
`def`. Tests: `scripts/HaltResultsTest.lean`.

## 5. Compliance: what the checks reject

From `CONTRIBUTING.md`, in short; follow it exactly, because these are what make a synthetic result
mean something:

* results stated with the library's notions (`SynthHaltReduction`, `⪯_s`, `MachineDecidable`),
  reducing from the library's `HaltProblem`, `HaltCanon` or `PCP.DecisionProblem`;
* every reduction and result a compiled `def`: no `noncomputable`, `unsafe`, `partial`,
  `implemented_by`, `extern`, `opaque`, `axiom`, `sorry`, or `native_decide` (use `decide`)
  anywhere in its dependency closure;
* no existence claims about synthetic reductions, no reductions wrapped in another type;
* every module imported from `DiagonaLean.lean`;
* a new reduction structure or relation registered in `reductionStructs` / `reductionRelations`
  (`⪯_s[f]` is there, `⪯[f]` must not be), with a cheating case in `scripts/CheckReductionsTest.lean`;
* every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`
  (`scripts/CheckAxioms.lean`): no `axiom`, `sorry` or `native_decide`, in the proved layer too.
  A work-in-progress file may use `sorry` only if listed in `sorryAllowances`
  (`Synthetic/AxiomCheck.lean`); code outside the list that uses it is still reported.

Style: lines at most 100 characters (`scripts/ci-local.sh --style-only`), module docstrings with
`## Main statements` and `## References` (`bibliography.bib`), docstrings on every declaration.
When wrapping prose, never split a backticked code span across lines.

## 6. Pitfalls (each cost real time)

* **`with` and `using` take one term each**: an applied function or lemma needs parentheses,
  `with (liftInstance b0 b1) using (pcp_alphabet_lift_spec b0 b1 hne)`; without them the
  arguments are read as the next command.
* **No bundled link only for the tactics**: build the reduction from the function and its
  `_spec` (`hard_reduce_from h with f using spec`) rather than defining `X.synthFromY := ⟨f, spec⟩`;
  the bundled links of the library were deleted where nothing else used them.
* **`abbrev` link functions defeat `fun_prop`**: it unfolds them before looking up their lemma.
  Use `def` + `@[fun_prop]` lemma.
* **`Primrec₂ f` lemmas are not what `fun_prop` matches**; state or derive the uncurried form and
  keep `Primrec₂` as a corollary.
* **`whnf` unfolds too far**: to expose a structure field, reduce the projection and the
  structure's definition only (as `ReduceFrom.unfoldField` does), so named functions stay folded.
* **`variable`s are scoped to the namespace block**: after `end Reduction … namespace Reduction`,
  restate them.
* **`Nat.pair` on literals** blows up unification: `attribute [local irreducible] Nat.pair`.
* **Renaming**: keep the old name as `@[deprecated New (since := "YYYY-MM-DD")] abbrev old := @New`,
  removed once no active branch uses it (the aliases of the phase 3 renaming went on 2026-11-27),
  and move use sites from the build's deprecation warnings (`scripts/rename_packages.py uses`
  does this from `scripts/rename-packages.tsv`). A warning inside a macro expansion points at the
  macro call; check the token before replacing it. When an alias replaces a declaration, move its
  docstring to the new declaration. An `alias` of a lemma breaks field notation under the old
  type name; restate the lemma instead.
* **Dot notation through an `abbrev` looks in the abbreviated type**: `SRS` is `List`, so `R.letters`
  looks for `List.letters`, and `h.tail` fails on `h : WordProblem R u v`. Write the full name.
* **Attribute-registered lemmas have uses that no text search finds**: `letters_prim` is used by
  `fun_prop` through `@[fun_prop]`. Before retiring a declaration, build without it.
* **After adding an import to `DiagonaLean.lean`**, rebuild the root before testing a scratch file
  with `lake env lean`; it reads the old root otherwise.
* **Every new file costs about 3.7 s of CPU** to load its imports (measured 2026-11-27). Split a
  file when it removes imports or separates roles, not otherwise.
* **Machine-level negative results** go through `HaltHard.not_computablePred` /
  `.not_machineDecidable` from a proved root, not through a second self-halting construction.

## 7. Checking, economically

* While editing: `lake build <Module>` for the file at hand; `lake env lean scripts/XTest.lean`
  for a test file.
* Before committing a batch: `scripts/ci-local.sh` (about 4 minutes; build, metaprogram and
  layering checks, lint, `fun_prop` tests, `#check_reductions` and its tests).
* Run the full check once per coherent batch — for a mechanical change across many folders, apply
  it everywhere, check once, then split the commits by folder. Running it after every small step
  multiplies the 4 minutes without catching more.
* Dry-run any rewriting script on all the shapes it will meet (nested namespaces, `@name`,
  `name.field`, macro calls, docstrings, Markdown code blocks) before applying it.

## 8. Working with this user

Commit only when asked; do not open a PR before a phase's substantial changes are done locally.
Report wall-clock and line counts as evidence when asked how long something took, and give
assessments without padding.
