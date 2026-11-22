---
name: diagonalean
description: How to write, prove and check Lean 4 code in the DiagonaLean library (undecidability by many-one reductions, on Mathlib and Cslib) — the two layers of reductions (synthetic `⪯_s`, proved `⪯`), the tactics `reduce_from`, `code_lift`, `fun_prop`, `derive_primrec`, `primrec_rec`, `derive_primcodable`, the key theorems from hardness to "no Turing machine decides it", Primcodable/Primrec proofs, naming of packages, and the compliance rules that `#check_reductions` and CI enforce. Use it for any work in this repository — a new undecidable problem, a new reduction or link, a `Primrec`/`Computable` proof, an alphabet change, a renaming or refactor, a review of a DiagonaLean PR, or fixing a CI failure — even when the request does not name the skill or a tactic.
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

## 2. Adding an undecidable problem: the workflow

1. **The problem.** `X/Basic.lean`: one-argument predicate `X.DecisionProblem : Inst → Prop`. If
   proofs want a curried form, define it separately (as `MPCP.Solvable c P`) with a bridge lemma
   by `rfl`; never write `fun x => … x.1 x.2` at use sites.
2. **The link.** `X/Reductions/Src_to_X.lean`:
   * the function, a `def` (not an `abbrev`, see §5), e.g. `srcToX`;
   * correctness, `theorem src_reducesto_x_spec : Src.DecisionProblem ⪯_s[srcToX] X.DecisionProblem`;
   * the package, `def X.synthFromSrc : Src.DecisionProblem ⪯_s X.DecisionProblem := ⟨srcToX, src_reducesto_x_spec⟩`.
   Inside another namespace, declare it as `def _root_.DiagonaLean.X.synthFromSrc`, which keeps the
   file's `variable`s and `open`s.
3. **Computability of the link** (needed for the proved layer and for machine-level results):
   `derive_primrec srcToX` if `fun_prop` can read its body, or a hand-stated
   `@[fun_prop] theorem srcToX_primrec : Primrec srcToX` (with `primrec_rec` for structural
   recursion). Instances need `Primcodable`: `derive_primcodable` for inductive types.
4. **The result.** `X/Undecidable.lean`, a `def` the compiler accepts:
   ```lean
   def X.synthFromHalt : SynthHaltReduction X.DecisionProblem := by
     reduce_from (Src.synthFromHaltOver b0 b1 hne) via X.synthFromSrc
   ```
   With a proved source (`MPCP.fromHalt`, or another `HaltReduction`), the same tactic proves
   `HaltReduction`, `HaltHard`, `¬ ComputablePred` and `¬ MachineDecidable enc` goals, upgrading
   the link through its `fun_prop` lemma.
5. **Alphabets.** If instances are built from letters, give a `CodeFunctor` and use
   `code_lift F from h` for every nontrivial alphabet (`…Over b0 b1 hne`, `…Bool`).
6. **Register it.** Import the new modules from `DiagonaLean.lean`: the check covers only what the
   root imports. Update the folder's `README.md`.
7. **Check.** §6.

Names: packages in the target's namespace, `Tgt.synthFromSrc`, `Tgt.synthFromHalt`,
`…Over b0 b1 hne`, `…Bool`, `synthCompl…` for a complement, `X.synthAlphabetLift`; proved versions
drop `synth` (`MPCP.fromHalt`). The letters are data, so a `def` takes them explicitly; it cannot
extract them from `Nontrivial α` (a `Prop`).

## 3. The tactics, and what they need from you

* **`reduce_from h via r`** reads the goal to choose the layer. It leaves `Computable r.f` (when it
  upgrades a synthetic link) and `Computable enc` only if `assumption` and `fun_prop` fail. Before
  `fun_prop` it reduces `r.f` to the *named* function `r` was built from (`unfoldField`), so a
  `@[fun_prop]` lemma on that function is all it needs. `h` and `r` are arbitrary terms (applied
  definitions, hypotheses, `.trans` chains), not only names. The bare correctness theorem is not a
  reduction; pass `⟨_, spec⟩`.
* **`code_lift F from h`** picks the lifting theorem from the goal's head; `code_lift F` alone
  proves `ManyOneEquiv`. A data goal needs `hne : b0 ≠ b1` in the context. Its side goal
  `map_computable` is closed by unfolding `F.liftMap` and `fun_prop`.
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

## 4. Compliance: what the checks reject

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
* headline results depend only on `propext`, `Classical.choice`, `Quot.sound`
  (`#print axioms`).

Style: lines at most 100 characters (`scripts/ci-local.sh --style-only`), module docstrings with
`## Main statements` and `## References` (`bibliography.bib`), docstrings on every declaration.
When wrapping prose, never split a backticked code span across lines.

## 5. Pitfalls (each cost real time)

* **`abbrev` link functions defeat `fun_prop`**: it unfolds them before looking up their lemma.
  Use `def` + `@[fun_prop]` lemma.
* **`Primrec₂ f` lemmas are not what `fun_prop` matches**; state or derive the uncurried form and
  keep `Primrec₂` as a corollary.
* **`whnf` unfolds too far**: to expose a structure field, reduce the projection and the
  structure's definition only (as `ReduceFrom.unfoldField` does), so named functions stay folded.
* **`variable`s are scoped to the namespace block**: after `end Reduction … namespace Reduction`,
  restate them.
* **`Nat.pair` on literals** blows up unification: `attribute [local irreducible] Nat.pair`.
* **Renaming**: keep the old name as `@[deprecated New (since := "YYYY-MM-DD")] abbrev old := @New`
  and move use sites from the build's deprecation warnings (`scripts/rename_packages.py uses`
  does this from `scripts/rename-packages.tsv`). A warning inside a macro expansion points at the
  macro call; check the token before replacing it. When an alias replaces a declaration, move its
  docstring to the new declaration. An `alias` of a lemma breaks field notation under the old
  type name; restate the lemma instead.
* **Machine-level negative results** go through `HaltHard.not_computablePred` /
  `.not_machineDecidable` from a proved root, not through a second self-halting construction.

## 6. Checking, economically

* While editing: `lake build <Module>` for the file at hand; `lake env lean scripts/XTest.lean`
  for a test file.
* Before committing a batch: `scripts/ci-local.sh` (about 4 minutes; build, metaprogram and
  layering checks, lint, `fun_prop` tests, `#check_reductions` and its tests).
* Run the full check once per coherent batch — for a mechanical change across many folders, apply
  it everywhere, check once, then split the commits by folder. Running it after every small step
  multiplies the 4 minutes without catching more.
* Dry-run any rewriting script on all the shapes it will meet (nested namespaces, `@name`,
  `name.field`, macro calls, docstrings, Markdown code blocks) before applying it.

## 7. Working with this user

Commit only when asked; do not open a PR before a phase's substantial changes are done locally.
Report wall-clock and line counts as evidence when asked how long something took, and give
assessments without padding.
