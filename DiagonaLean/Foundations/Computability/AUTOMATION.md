# Automating computability proofs

A plan for proving `Primrec`, `Computable` and machine-level computability automatically, for functions on arbitrary inductive types. Written on 2026-11-18, last updated 2026-11-22; update it as milestones land. M1–M8 and M13 for nested `List T` are done, and M12 is decided (see *Milestones*). `derive_primrec` states and proves the `fun_prop` lemma of a definition, and every reduction in the library from PCP onward, together with Halt → MPCP, is primitive recursive (see *Applied*). What remains is in *What's next*.

A guided tour of what the automation proves, one tactic call per function, is in `examples/Automation.lean` at the repository root (run it with `lake env lean examples/Automation.lean`).

## Why

Two kinds of side goal come up again and again in DiagonaLean:

* **`Primrec f` or `Computable f`** (Mathlib's notions). These are needed, for example, so that `exists_computes` can turn a function on codes into a machine.
* **`∃ R : SingleTapeTM Bool, ComputesReduction R enc₁ enc₂ f`**: a Turing machine computes the reduction on encoded inputs. This is what the `¬ MachineDecidable` results need.

Both kinds of proof are bookkeeping: the function is built from computable pieces, so it is computable. Written by hand they are long and brittle, and they are repeated for every type. Each recursive type (expressions `RExp`, SKI terms, λ-terms, machine data) gets a hand-made code: `rc`, `skc`, `tc`, `dataC`. Each recursive function on such a type gets about 40 lines of table boilerplate (`subT`, `subV`, `subT_succ`, `length_subT`, `subT_get`, a commuting square, a `Primrec` proof). The aim is for all of this to be derived.

## What "correct" means

A statement `Primrec f` is only as meaningful as the encodings behind it.

* **The decoder must be primitive recursive.** Mathlib's `Primcodable` asks for exactly this. With a merely injective code, an encoding can carry hidden information, and "primitive recursive on codes" then says little about `f`.
* **Then the choice of encoding does not matter.** `Primrec` is invariant under primitive recursive isomorphisms, so all reasonable encodings give the same results.

DiagonaLean's codes `rc`, `skc` and `tc` are injective, but there is no proof yet that their decoders are primitive recursive. Closing that gap is part of this plan.

## What cannot be done

* **No complete algorithm.** Deciding whether a given function is computable or primitive recursive is impossible: totality alone is Π⁰₂-complete. A Lean function built with `Classical.choice` is not a program at all.
* **No single internal theorem.** "Every choice-free Lean definition is computable" is true, by a normalization argument about Lean's type theory. But it is a theorem *about* Lean, not one that can be proved inside Lean once and for all.

So every method below is *sound but incomplete*. It works on one definition at a time and produces a certificate that the kernel checks. The general part is the theory of encodings and recursion, proved once; the per-definition part is automated.

## Design

There are four layers. Each one uses the one below it.

```
4. certifying translation   kernel term of a definition ──▶ proof of Computable / Primrec
3. tactics                  fun_prop (composition) · primrec_rec (structural recursion) · tm_computes
2. deriving                 inductive T  ──▶  T ≃ WType … ,  Primcodable T
1. foundation               Theorem A (encoding) · Theorem B (recursion), for W-types, proved once
```

### Layer 1: the foundation (W-types, proved once)

Almost every inductive type is a **W-type**: the type of well-founded trees whose nodes are labelled by *shapes*, each shape having a fixed set of children. For example, `RExp X` has these shapes:

| Shape | Children |
|---|---|
| `zero`, `one` | 0 |
| `sym x`, one shape per letter `x` | 0 |
| `star` | 1 |
| `plus`, `mul` | 2 |

Mathlib has `WType β`, `WType.elim`, `WType.equivSigma` and `Encodable (WType β)` (`Mathlib/Data/W/Basic.lean`, assuming `Encodable α`, `Fintype (β a)` and `Encodable (β a)`). It has no `Primcodable` instance and no computability results for W-types.

**Theorem A (encoding).** If the shapes are `Primcodable` and each shape has finitely many children, then the W-type has a `Primcodable` encoding, with primitive recursive encode and decode.

* *Proof idea:* encode a node as `Nat.pair (code of shape) (code of the list of children's codes)`, the way `rc` does. A child's code is smaller than its parent's (`lt_pair_tag`), so decoding is a course-of-values recursion.
* *Instance diamond:* Mathlib's `Encodable (WType β)` uses a depth-stratified `Σ` encoding, which is not shaped for this proof. Either prove that encoding primitive recursive, which is hard, or state the new encoding on a type synonym, or replace Mathlib's instance upstream. Two different `Encodable` instances on the same type would make lemmas fail to apply.

**Theorem B (recursion).** The paramorphism, a fold whose step also sees the children themselves, preserves primitive recursion:

```
Primrec step  →  Primrec (fun t => paraW step t)
step : (shape, children, results on children) → γ,   γ Primcodable
```

It comes with a version with parameters (`fun (p, t) => paraW (step p) t`) and a course-of-values version, where the step sees the results on all smaller codes. The proof is the `subT`/`subV` table construction, done once in general. Mathlib's `Primrec.nat_strong_rec` is the `ℕ` case.

**Corollaries.**

* `List`, `ℕ`, `Option` and binary trees are W-types, so their recursors become special cases of Theorem B. This is a sanity check against Mathlib's existing `Primrec.list_rec` and `Primrec.nat_rec`.
* `Computable` versions follow through `Primrec.to_comp`.

### Layer 2: deriving, for each inductive type

A command or deriving handler, `deriving PrimcodableW`, reads an inductive type's constructors and generates:

1. the shape type and the arity of each shape;
2. the equivalence `T ≃ WType β`, with proofs that the two sides are inverse, by induction;
3. `Primcodable T`, by transporting Theorem A along the equivalence (`Primcodable.ofEquiv`);
4. a `@[fun_prop]` lemma for each constructor (`Primrec fun x => plus (f x) (g x)` from `Primrec f`, `Primrec g`), and for each projection or match;
5. a recursion principle stated on `T` itself, Theorem B transported.

**Coverage:**

| Inductive type | Status |
|---|---|
| Finitely many children per constructor, `Primcodable` constructor data | Covered directly |
| Nested, children in a `List T` or an `Option T` | **Covered** (M13): the shape records each list's length and whether each option is `some`. |
| Nested in other containers (`List (List T)`, …) | Same idea, not done yet. |
| Mutual, indexed families | Need indexed W-types. Same idea, more machinery. Later. |
| Infinitely branching (a child per `ℕ`) | Not `Primcodable` in general (functions `ℕ → T` are not finitely codable). Out of scope. |

With this layer, `RExp`, `SKI` and `Term` get real `Primcodable` instances, and statements become `Primrec (f : RExp → RExp)` rather than statements about `ℕ → ℕ` plus a commuting square. The hand-made codes `rc`, `skc` and `tc` then turn out to be the derived encodings, or are proved primitive recursively isomorphic to them.

### Layer 3: tactics

* **`fun_prop` for composition.**
  * *`Primrec`: done (PR #36).* `Primrec` and `PrimrecPred` are `fun_prop` properties (`Prim.lean`). All 24 former `prim` call sites use `fun_prop`, and the old `prim_step` machinery is removed.
  * *Pitfall:* codes built with `Nat.pair` from literals make unification evaluate huge numbers and time out. Use `attribute [local irreducible] Nat.pair`, as `InstanceCode.lean` and `Between.lean` do.
  * *`Computable`: done (M2).* `Prim.lean` registers `Computable`, with Mathlib's lambda theorems, `Primrec.to_comp` as a transition theorem, and compositional wrappers for the operations Mathlib states with `Computable₂`. `List.map`, `flatMap` and `foldr` have `Computable`-level lemmas with `Primrec` hypotheses, because `fun_prop` decomposes an application before it tries a transition. `fun_prop` also knows `Nat.iterate`, `List.foldl`, `List.foldr` and `Bool.toNat`. Tests are in `scripts/FunPropTest.lean`, run in CI.
  * *Library conversion (M3).* The hand-built `Primrec.nat_iterate` / `list_foldl` / `list_foldr` proofs in all 12 benchmark files are now `unfold …; fun_prop`.
  * *Coverage (2026-11-19):* integer arithmetic (`IntPrim.lean`: `+`, `-`, `*`, negation, powers, `≤`, `<`, `natAbs`, `toNat`, casts; Mathlib has none of these); about 45 further list, option, `Bool` and `ℕ` operations in `Prim.lean` (`take`, `drop`, `filter`, `find?`, `count`, `sum`, `zip`, `zipWith`, `zipIdx`, `erase`, `insert`, `×ˢ`, `getLast?`, `min?`, `max?`, `gcd`, `lcm`, `Nat.log`, `sqrt`, bounded `∀`/`∃`), with predicates that may depend on the outer variable; and vectors and matrices (`MatrixPrim.lean`: `![…]`, `!![…]`, `Matrix.of`, `List.ofFn`, and `fun i => …` over `Fin n`), so a matrix with primitive recursive entries needs no split into entries.
  * *More `irreducible` pitfalls:* the λ-calculus proof search needs `attribute [local irreducible] results` for its `stepS` lemma, for the same reason as `Nat.pair`.
  * *Upstream:* Mathlib PR #36893 (a draft with merge conflicts) makes `Primrec` and `Computable` `fun_prop` properties for `Primrec/Basic.lean` only.
* **`derive_primrec` for non-recursive definitions** (`DerivePrimrec.lean`, PR #45). `derive_primrec f` states the uncurried lemma `Primrec fun x : A₁ × A₂ => f x.1 x.2`, proves it by `unfold f; fun_prop`, and registers it as `f_prim` with `@[fun_prop]`. It is a command, permitted by name in `Synthetic/MetaprogramCheck.lean` (CONTRIBUTING convention 9). *Function arguments (PR #54):* an explicit argument `c : A → B` is not `Primcodable`, so the lemma is then stated in compositional form over a parameter type, with `c : X → A → B` and the hypothesis `Primrec fun p : X × A => c p.1 p.2`. An argument whose domain is a function is rejected with a message. The machine-level MPCP and SemiThue results use it for every step of the tile construction (`MPCP/Reductions/HaltCanon_to_MPCP.lean`).
* **`primrec_rec` for structural recursion.** A tactic, not a command. `scripts/CheckMetaprograms.lean` forbids metaprograms that add declarations, and a tactic adds none: you write `@[fun_prop] theorem f_primrec : Primrec f := by primrec_rec`.
  * *Done for `ℕ` and `List` (M3, extended in `232cf0f`):* recursion on the last argument, with any number of parameters (packed into a product in the goal when there are two or more). On `ℕ` it also handles course-of-values recursion (`f (n / 2)`, `f (n - 3)`) and nested patterns (`f 0`, `f 1`, `f (n + 2)`), through `primrec₂_of_nat_cov_eqns`, built on `Primrec.nat_strong_rec`. Still unsupported: overlapping patterns, nested recursive calls (`f (f n)`), non-structural recursion on lists, and recursion on an argument other than the last. *Added 2026-11-19:* polymorphic definitions (type and instance arguments stay fixed), and recursion on the first argument of a two-argument function on `ℕ` while the second argument changes (`f (n+1) a = … f n (h n a) …`, through `primrec₂_of_nat_param_eqns`).
  * *Finding:* the library's own recursive `Primrec` proofs are not pattern-matching recursion. They use `Nat.iterate` and folds explicitly, so it was `fun_prop` lemmas for those, not `primrec_rec`, that converted the benchmark.
  * *For arbitrary inductive types (M7):*
  1. Read `f`'s equation lemmas.
  2. Recognise a structural recursion on an inductive type that has layer 2.
  3. Restate `f` as the paramorphism of layer 1, and prove the two equal by induction using the equation lemmas.
  4. Apply Theorem B, and close the step with `fun_prop`.
  5. Tag the result `@[fun_prop]`, so recursive definitions compose like everything else.

  *Before layers 1 and 2 exist,* a first version can cover `ℕ` and `List` alone, through `Primrec.nat_rec`, `nat_iterate`, `list_foldr` and `list_rec`. A code-level version for DiagonaLean's hand-made codes would use a generic course-of-values combinator `codeRec` in place of the per-function tables.

**Soundness of the tactics.** These tactics prove `Prop` goals about functions that are already defined. Their output is an ordinary proof term that the kernel checks. They cannot change any reduction that `#check_reductions` checks, and headline results still depend only on `propext`, `Classical.choice` and `Quot.sound`.

### Layer 4: certifying translation

The most general automation: a tactic that walks the kernel term of a given definition and emits a proof of `Computable` or `Primrec`. Its compilation rules are the theorems of the layers below:

| Feature of the kernel term | Rule | Result |
|---|---|---|
| Application and composition of known functions | `fun_prop` lemmas | `Primrec` |
| Recursor or `brecOn` on an inductive type, result type `Primcodable` | Theorem B, through layer 2 | `Primrec` |
| Course-of-values or bounded search | Theorem B, course-of-values version; search over `List.range` | `Primrec` |
| Higher-order recursion (the motive is a function type; Gödel's System T) | Uncurry, then `Partrec` and `Code`. **Not** `Primrec` in general (Ackermann). | `Computable` |
| `WellFounded.fix` with a decreasing measure | `Partrec.fix` or the recursion theorem, with totality from the well-foundedness proof | `Computable`; `Primrec` only with a primitive recursive bound |
| Unbounded `Nat.find` on a decidable predicate | `Partrec.rfind`, then totality from the existence proof | `Computable` |
| `Classical.choice`, or an axiom other than the standard three | none | — |

The termination argument limits the class. A measure into `ℕ` with a primitive recursive bound gives `Primrec`. Lexicographic measures on `ℕᵏ` give Péter's multiply recursive functions, which go beyond primitive recursion.

This is the Lean counterpart of certifying extraction in other proof assistants (see Prior art). It is general in reach, and proves one definition at a time.

### Beside the layers: machine-level computability

To get from `Computable` to `∃ R : SingleTapeTM Bool, ComputesReduction R enc₁ enc₂ f`, there are two options.

**Option A: a bridge tactic.** DiagonaLean already has a verified bridge from Mathlib's `Computable` to Cslib machines: `exists_computer` and `exists_computes` in `Computer.lean`. They go through Mathlib's chain `ToPartrec.Code → TM2 → TM1 → TM0`, then `wrap` and cleanup. A tactic `tm_computes` would use one general lemma:

```
Primrec g → (∀ x, g (c₁ x) = c₂ (f x)) → ∃ R, ComputesReduction R (bitsOf ∘ c₁) (bitsOf ∘ c₂) f
```

and close the side goals with the layers above. With layer 2, `c₁` and `c₂` are the `Primcodable` encodings themselves, and the commuting-square side goal disappears.

* *Limitation:* `R` exists only classically, because Mathlib's chain is `noncomputable`. The project's convention allows this (one finite constant), but the machine cannot be run, inspected or bounded in time.

**Option B: explicit machines by reflection (research project).** A data-level `PrimCode f` (a program with a proof that it evaluates to `f`), a reifier, a computable verified compiler to `SingleTapeTM Bool` (probably through Cslib's `MultiTapeTM`, with a multi-to-single-tape simulation theorem), and `compile_correct`. This gives explicit machines and running-time bounds through Cslib's `OutputsWithinTime`. *Shortcut to check first:* Mathlib's chain is `noncomputable` only because of how its supports, the finite sets of states, are built. If they can be computed, Mathlib's compiler becomes the verified compiler.

## Prior art

* **Forster and Kunze**, *A certifying extraction with time bounds from Coq to call-by-value λ-calculus* (ITP 2019). It runs on MetaCoq, extracts Coq functions to the λ-calculus L automatically, with correctness proofs and time bounds, and underlies the Coq Library of Undecidability. It is the closest analogue of layer 4.
* **Myreen and Owens**, proof-producing synthesis of ML from HOL (ICFP 2012), in HOL4 and CakeML. It is the same idea, with ML as the target.
* **Proof theory.**
  * The functions provably total in IΣ₁ are exactly the primitive recursive ones (Parsons, Mints, Takeuti).
  * Program extraction (realizability, Dialectica) takes constructive totality proofs to System T terms. Recursion at base type only gives primitive recursive functions.
* **Lean and Mathlib:** `WType` is `Encodable` but not `Primcodable`. `fun_prop` exists, but it is not set up for computability (#36893 is a draft). There is no certifying extraction to `Nat.Partrec.Code`.

## Milestones

| # | Layer | Milestone | Done when |
|---|---|---|---|
| M1 | 3 | `fun_prop` for `Primrec` | **Done** (PR #36): all `prim` uses replaced, CI green. |
| M2 | 3 | `fun_prop` for `Computable` | **Done** (`f1467df`). |
| M3 | 3 | `primrec_rec` for `ℕ` and `List` | **Done** (`a635e66`). The benchmark was converted through `fun_prop` lemmas for `iterate` and folds (`27ab1b5`). |
| M3b | 3 | `primrec_rec` extensions | **Done** (`232cf0f`): several parameters, course-of-values recursion, nested patterns on `ℕ`. |
| M4 | 1 | Theorem A for W-types | **Done** (`78ce1dd`): `PTree α ar` in `PolyTree.lean`, its own inductive (no diamond with Mathlib's `WType`), `PTree.primcodable` given `Fact (Primrec ar)`. |
| M5 | 1 | Theorem B for W-types | **Done** (`eee51cb`, `efb3f4d`): `fold_primrec` and `para_primrec` (with a parameter); constructor `mkOpt` and destructors `shape`, `children` primitive recursive. Check: `ℕ` and unary trees are primitive recursively isomorphic (both round trips proved, in the tests). |
| M6 | 2 | Correct encodings, and `derive_primcodable` | **Done.** `RExp`, `SKI`, `Term ℕ` are `Primcodable` with primitive recursive constructors, and the hand-made codes are correct encodings (`primrec_iff_rc`, `primrec_iff_skc`, `primrec_iff_tc`, through the general `TaggedCode.primrec_iff`; `39d9287`, `49a2758`). `derive_primcodable T` (`340e853`; parameters in `08ac9db`) generates all of this for types with parameters in any universe (no indices; not mutual; nested `List T` fields since M13), with a narrow `scripts/CheckMetaprograms.lean` exception (CONTRIBUTING convention 9). |
| M7 | 3 | `primrec_rec` on any type from M6 | **Done** (`808b4d1`): structural recursion on any type `T` with `T.primrec_of_eqns` (hand-written for `SKI`; generated by `derive_primcodable` for the others, `RExp` and `Term` included), results of any `Primcodable`, `Inhabited` type; paramorphisms (right-hand sides that use the subterms) in `f09db36`. |
| M8 | — | `tm_computes` (option A) | **Done** (`18c08ef`). `tm_computer F` and `tm_computes F`; the sites in `KleeneAlgebra/Race.lean`, `Between.lean` and `ProofRace.lean` use them. |
| M9 | 1–3 | Upstream | Theorems A and B, and `fun_prop` for `Primrec` and `Computable`, offered to Mathlib, reviving #36893. |
| M10 | 4 | Certifying translation, first-order fragment | A tactic proves `Primrec` for definitions using composition and first-order recursors, directly from their kernel terms. |
| M11 | 4 | Higher-order and well-founded recursion | `Computable` for System T style recursion and `WellFounded.fix`. |
| M12 | — | Option B feasibility | **Decided** (2026-11-19): Mathlib's chain is not the route to explicit machines or time bounds; see *What's next*. |
| M13 | 1–3 | Nested and mutual types | **Nested `List T`: done** (2026-11-19, see *What's next*). Mutual families: open. |

**Order:** M1–M8 are done, and M13 for nested `List T`. Next, in *What's next*: getting the PRs merged, then mutual families (the rest of M13) and M9. M10 and M11 are long term.

**Benchmark for M3 and M7:** about 15 hand-written uses of recursion lemmas (`Primrec.nat_iterate`, `list_foldr`, `nat_rec`, …) across 12 files:

* `Foundations/Computability/`: `Interpreter`, `HaltSearch`, `CodeSim`, `Computer`, `OutputSearch`;
* `Foundations/CombinatoryLogic/`: `Code`, `ProofSearch`;
* `Foundations/LambdaCalculus/`: `ProofSearch`, `Race`;
* `KAComm/KleeneAlgebra/`: `BinarySubst` (`wC_prim`, `subC_prim` and the `subT`/`subV` table), `InstanceCode`, `ProofSearch`.

## What's next

### Next steps, in order (2026-11-22)

The PR stack (#35–#40) and the applied work it led to (#41–#54) are merged. The former items "Halt → MPCP/PCP at machine level" and "a concrete code for grammars" are done: see *Applied*.

**Automation gaps**

1. `List (List T)` fields, and other containers (`T × T` in a list).
2. Mutual inductive families: the many-sorted design under M13.
3. `primrec_rec`: recursion through a `filter`; `foldr`/`foldl` directly over a list field; recursion on an argument other than the last; two lists at once (`zipWith`-shaped); calls on grandchildren and deeper.
4. A `fun_prop` hook for `primrec_rec`, so a recursive definition needs no separately stated lemma.
5. When a function on a right-hand side has no `fun_prop` lemma, `primrec_rec` runs into a heartbeat timeout instead of failing with a clear message.
6. Switch `SKI` to `derive_primcodable`, as `RExp` and `Term` were; its `primrec_of_eqns` is still hand-written.

**Longer term**

7. M9: offer `fun_prop` for `Primrec`/`Computable` and Theorems A and B to Mathlib.
8. M10 and M11: see *Long term* below for how hard they are.
9. Option B, a verified compiler to Cslib's `MultiTapeTM` with step counts, only if running-time bounds become a goal (see M12).

### Where the work is

Everything above is on `main`. #35–#40, #37 included, merged on 2026-11-19. Later PRs: #44 (machine-level MPCP, PCP, MatMort), #45 (`derive_primrec`), #46 (grammar codes; machine-level EmpCFG, AmbigCFG), #47 (proof systems checked by a stack machine, `StackProof.lean`), #48 (SemiThue, GrammarMem), #49–#51 (refactors), #52–#54 (alphabet lifts through `Foundations/Codes`).

### 1. Get the stack reviewed and merged

Done.

### 2. M13: nested and mutual types

*Nested `List T`: done (2026-11-19).* It uses the direct construction, not the many-sorted one below: a node's shape records the length of each list field, so every tree of `PTree Shape ar` is the tree of a term, and Theorems A and B apply unchanged, with no well-sortedness predicate.

* *Generator* (`generateNested` in `DerivePrimcodable.lean`): it produces the same declarations as for plain types. `toTree` is structural recursion together with a helper `toTreeL : (xs : List T) → List.Vector _ xs.length`, whose type gives the length the children's index bound needs. The round trips are proved by induction with a second motive for lists.
* *Interface:* in `T.primrec_of_eqns` the step of a constructor gets its data and the result on each recursive field: `σ` for a field `T`, `List σ` for a field `List T`. The equation is `f p (c … xs …) = g p … (xs.map (f p)) …`. The proof cuts the children's results with `chunks` (`PolyTree.lean`, primitive recursive).
* *Tactic:* `primrec_rec` accepts right-hand sides that use a list field through `List.map (fun c => … f p c …)` and `List.length`. Other uses of the subterms (paramorphisms) are rejected with a message.
* *Tests* (`FunPropTest.lean`): rose trees, a list field between plain fields, two list fields, a type parameter, results in the type itself; and a rejected paramorphism.
* *Paramorphisms (2026-11-19):* a right-hand side may also use the subterms themselves (`cs.map label`, `cs.take 1`); `primrec_rec` then proves the pair `(t, f t)` primitive recursive, with the results on a list field as pairs, as for plain types.
* *Option fields (2026-11-19):* the shape records whether an `Option T` field is `some`, and `ofTree` has one case per assignment of `true`/`false`. The step gets `o.map (f p)`. Lean cannot prove termination for `o.map f` written directly, so users write a `match` or `none`/`some` patterns, and Lean then splits the equations; `primrec_rec` puts them back together with `Option.elim` and proves the constructor's equation by cases.
* *Not covered yet:* other containers (`List (List T)`, `T × T` in a list), `foldr`/`foldl` directly over a list field (`map` first), recursion through a `filter`, and mutual families.
* *Bug fixed on the way:* `primrec_rec` counted a constructor's type parameters as fields when they were variables (`PRose α` with `α` a variable).

The many-sorted design that follows is still the plan for mutual families.

`derive_primcodable` and `primrec_rec` handle one inductive type at a time. A **nested** type keeps children in another type (`node (cs : List T)`); Lean compiles it to a mutual family with an auxiliary "list of `T`" type. A **mutual** family `T₁`, `T₂` refers to itself across types. In both cases a type is no longer *all* trees of `PTree α ar`, only some of them.

**Design: many-sorted trees.**

1. *Theory, once (Layer 1).* A sort for each shape, and a sort for each child of each shape: `sortOf : α → ι` and `childSort : (a : α) → Fin (ar a) → ι`. `WellSorted i t` says that the root of `t` has sort `i` and every child has the sort its parent expects. It is a fold, so it is a primitive recursive predicate (Theorem B), and `{t // WellSorted i t}` is `Primcodable` through Mathlib's `Primcodable.subtype`. Also needed: a fold over well-sorted trees, with one step per sort, and its `Primrec` lemma.
2. *Generator (Layer 2).* For a family `T₁ … Tₖ` (the auxiliary types included for a nested type): one `Shape` for all constructors of all types, its sorts, mutually recursive `toTree`/`ofTree`, round trips by mutual induction, and, for each `Tᵢ`, `Tᵢ ≃ {t // WellSorted i t}`, `Primcodable Tᵢ`, constructor lemmas, and a joint `primrec_of_eqns` with one family of equations per type.
3. *Tactic (Layer 3).* `primrec_rec` for functions defined by mutual recursion (`f` on `T₁` together with `g` on `T₂`), which it cannot do yet. For a nested type this includes the case users actually write: a function on `T` that maps itself over the `List T` of children.

**Order of work:** nested `List T` first. It is the common case (terms with argument lists, rose trees), it has exactly two sorts, and it tests the whole design. Then general mutual families.

**Size and risk:** comparable to all of `derive_primcodable` so far. The risk is in the generated proofs: mutual induction, and carrying the well-sortedness invariant through `ofTree`.

### 3. M12: can Mathlib's compiler give explicit machines?

*Decision (2026-11-19): do not pursue Mathlib's chain for explicit machines or time bounds.* Three findings:

* **The supports can be made computable** (items 2–5 below): routine.
* **The program needs a data-level source.** Mathlib's `ToPartrec.Code.exists_code` (`TuringMachine/Config.lean`) builds the code explicitly in every case (`zero'`, `succ`, `head`, `comp`, `prec`, `rfind`). It recurses on the `Prop` `Nat.Partrec'`, though, so a computable copy needs a data version of those derivations, and something that produces one from a definition: a reifying tactic, which is option B's reification.
* **No running-time bounds come from it.** `StateTransition.Respects` turns one step into "one or more" steps with no bound, so none of the simulations ToPartrec → TM2 → TM1 → TM1 over `Bool` → TM0 → Cslib counts steps. Time bounds would mean re-proving every layer with step counts, through a chain with a large overhead.

So explicit machines are possible at real cost, and time bounds are not reachable this way. For time bounds, compile directly to Cslib's `MultiTapeTM` (option B), with cost-aware proofs from the start.

The details: Choice enters the pipeline in five places:

1. `Code.exists_code`: `Computable f` is a `Prop`, so the program is only known to exist. This is the real obstacle: an explicit machine needs a data-level program, i.e. the reification half of option B, whatever happens to the compiler.
2. `exists_blockEnc`, through Mathlib's `exists_enc_dec` (`Finite.exists_equiv_fin`, `invFun`). An explicit encoding of `Γ2` replaces it.
3. Our `supp2`, under `open scoped Classical`. ToPartrec's states already have `DecidableEq`.
4. Mathlib's supports `TM2to1.trSupp`, `TM1to1.trSupp` and `TM1to0.trStmts`: `Finset`s of statements built with classical `insert`.
5. Cslib's `Fintype State`, which follows from 4.

Statements contain functions, but all of them have finite domains. A prototype gave `DecidableEq (TM1.Stmt Γ Λ σ)` for finite `Γ`, `σ`, and a computable copy of `TM1.stmts₁`, proved equal to Mathlib's, that runs under `#eval`. The transition functions are already computable, and `wrapG` keeps membership as a proof. So items 2–5 are routine: decidable equality for the TM2, TM2to1 and TM1to1 statement and state types, and computable copies of the supports, proved equal to Mathlib's. Item 1 decides the matter.


### 4. M9: upstream to Mathlib

Offer `fun_prop` for `Primrec` and `Computable`, and Theorems A and B, to Mathlib, building on the stalled PR #36893. Decide first whether Theorem A should be stated on Mathlib's `WType` rather than on `PTree` (see *Open questions*). Writing it is a few sessions; review is slow and is mostly waiting.

### Applied: the library's reductions are primitive recursive

| Reduction | Result | Status |
|---|---|---|
| MPCP → PCP | `mpcpToPcp_primrec` (`PCP/Primrec.lean`) | **Done** (`252d2da`) |
| PCP alphabet lift | `liftInstance_primrec`, `synthAlphabetLift_primrec` | **Done** (`252d2da`, `376ac50`). Since 2026-11-19 `hashL` and `hashR` are proved by a bare `primrec_rec`, with no hand-written rewrite lemmas; since 2026-11-22 the lift is the unary code of the letters used (`localCode`), and `natToBits` is gone |
| PCP → MatMort | `matImage_primrec`, `synthFromPCP_primrec` (`MatMort/Primrec.lean`), with `Finset.primcodable` (`FinsetPrim.lean`) | **Done** (`376ac50`). Since 2026-11-19 the matrix of a pair of words is `unfold …; fun_prop`, through `IntPrim` and `MatrixPrim`; no `ℕ` detour, no split into entries |
| PCP → EmpCFG, AmbigCFG | `empCode_prim` (`EmpCFG/Reductions/PCP_to_EmpCFGCode.lean`), `ambCode_prim` (`AmbigCFG/Reductions/PCP_to_AmbigCFGCode.lean`) | **Done** (#46). The reductions go to grammar codes (`Foundations/Grammar/Code.lean`: rules over numbered nonterminals), which are `Primcodable`; `ContextFreeGrammar`, whose field `NT : Type` blocks this, is reached through `GrammarCode.toCFG` |
| Halt → MPCP / PCP | `instOf`, `canonInst_prim` (`MPCP/Reductions/HaltCanon_to_MPCP.lean`) | **Done** (#44; since 2026-11-23 from `HaltCanon`). The tiles are built from a canonical machine's table, each step by `derive_primrec`; `MPCP.fromHalt` is the halting reduction, and PCP and MatMort follow through the reductions above |
| Halt → SemiThue, GrammarMem | `SemiThue/Reductions/HaltCanon_to_SemiThue.lean`, `GrammarMem/Reductions/SemiThue_to_GrammarMem.lean`, `GrammarMem/Reductions/HaltCanon_to_GrammarMem.lean` | **Done** (#48), from the MPCP tiles |
| Halt → KA, SKI, β | `tm_computer` / `tm_computes` | Done earlier, at machine level |

### 5. Smaller items

* `primrec_rec`: course-of-values recursion on inductive types (calls on grandchildren and deeper); recursion on an argument other than the last, beyond the `ℕ` case with one changing argument; recursion on two lists at once (`zipWith`-shaped). Polymorphic definitions are done.
* *Done (2026-11-19):* `derive_primcodable` for universe-polymorphic types. `PTree` and Theorems A and B live in any universe, and the generator writes each parameter's own type and declares the type's universes. `RExp` and Cslib's `Term` now use `derive_primcodable` instead of their hand-written files (`Term` for any variable type, not only `ℕ`), and `rc_primrec` and `tc_primrec` are a bare `primrec_rec`. On the way, the generated `primrec_of_eqns` proves its case analysis level by level (`sumStepLines`), which brought a type with five constructors from about 35 s to 2 s.
* A `fun_prop` hook for `primrec_rec`, so a recursive definition's `Primrec` lemma is found without being stated (see *Open questions*).

### 6. Long term: M10, M11

The certifying translation of Layer 4.

**How hard (assessed 2026-11-19).** The difficulty is coverage, not soundness: the output is an ordinary proof that the kernel checks.

* **M10, first-order fragment: moderate.** What M10 adds is the friction it removes: today every helper a definition calls needs its own `@[fun_prop]` lemma, stated by hand. The kernel terms Lean compiles definitions to are awkward. Structural recursion becomes `brecOn`/`below`, a `match` becomes an auxiliary matcher, and an `if` needs its condition translated to a `PrimrecPred`, which is easy for comparisons and hard for arbitrary `Decidable` instances. The practical route is a driver around the existing tactics, working from equation lemmas rather than raw kernel terms. It would prove every helper in the call graph automatically, handle `match`/`if` in bodies, and cache the results as lemmas. About 4–8 focused sessions for the library's definitions; robustness on arbitrary Lean code is open-ended.
* **M11, higher-order and well-founded recursion: hard, a research project.** Well-founded recursion without a primitive recursive bound gives `Computable`, not `Primrec`, and general (non-tail) recursion has to go through `Partrec.fix` (loops only) or the recursion theorem: in effect, compiling to a stack or continuation machine with a correctness proof. Higher-order recursion (a function-valued motive: System T, Ackermann) is worse. Mathlib's `Computable` only covers `Primcodable` types, and functions are not `Primcodable`, so it needs defunctionalisation or closure conversion, a real verified compiler, with no infrastructure in Mathlib. Forster and Kunze's certifying extraction is the closest analogue, and was a thesis-scale effort. Many weeks to months.
* **Payoff here.** Reductions are almost always primitive recursive, and the current tools prove them. An "M10-lite" (automatic helper lemmas, `match` support) would be a convenience worth doing after the applied work. M11 matters only for functions beyond primitive recursion, which no reduction in the library needs.

## Open questions

* **The W-type instance diamond:** resolved for now by a separate inductive `PTree`. Upstream, Mathlib may prefer the result on `WType` itself.
* **Nested inductives (M13):** settled for `List T` by the direct construction (lengths in the shape). Mutual families still need the many-sorted design.
* **`primrec_rec`:** stay a tactic (as now), or also become a `fun_prop` hook, so that composing a recursive definition needs no separately stated lemma?
* **Input for M3, M7 and M10:** equation lemmas, which are stable across Lean versions, or the kernel's `brecOn` term, which is closer to how the definition actually recurses?
* **Where layers 1 and 2 live:** in DiagonaLean first, or directly in Mathlib?
