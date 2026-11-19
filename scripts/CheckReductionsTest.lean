import DiagonaLean.Synthetic.ReductionCheck
import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.Synthetic.Tactics.ReduceFromPCP

/-! Negative tests for `#check_reductions`, run by CI. Each `bad*` declaration, `Bad*` structure,
`Hidden`, `dependent`, `classicalFn`, `badAxiom` and the declarations with generated-looking names
produces or claims a reduction of `HaltProblem` (or PCP) to a
decidable predicate (`Even`, or `b = true` on `Bool`) by a classical case split, possibly hidden
behind an escape hatch in a dependency or `sorry`, and must be reported. The other declarations
follow the convention and must not be.

Since `Undecidable` is a type, a `theorem` cannot state it: Lean rejects
`theorem t : Undecidable p` itself. The cases below are what can still be written. -/

open DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation

/-- The classical case split, stated as an existential: a claim that a reduction exists. -/
theorem classicalFn :
    ∃ f : EncodableTM Bool × List Bool → ℕ, HaltProblem ⪯ₘ[f] fun n => Even n := by
  classical
  exact ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩

/-- A compiled definition that takes the reduction function as a parameter. -/
def withFunction (f : EncodableTM Bool × List Bool → ℕ)
    (h : HaltProblem ⪯ₘ[f] (fun n : ℕ => Even n)) : HaltProblem ⪯ₘ (fun n : ℕ => Even n) :=
  ⟨f, h⟩

/-! ### Definitions that are not compiled -/

/-- The case split in a `noncomputable` definition. -/
noncomputable def bad1 : Undecidable (fun n : ℕ => Even n) := by
  classical
  exact ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩

/-- The case split obtained from an existential by `Classical.choose`. -/
noncomputable def bad2 : Undecidable (fun n : ℕ => Even n) :=
  withFunction _ classicalFn.choose_spec

/-- A private reduction: private names start with `_private`, like generated ones. -/
private noncomputable def bad3 : Undecidable (fun n : ℕ => Even n) :=
  withFunction _ classicalFn.choose_spec

/-- A compiled definition that decides `HaltProblem` with an instance parameter. -/
def withInstance [DecidablePred HaltProblem] : HaltProblem ⪯ₘ (fun n : ℕ => Even n) :=
  ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩

/-- A classical instance passed to it. -/
noncomputable def bad4 : Undecidable (fun n : ℕ => Even n) :=
  @withInstance (Classical.decPred _)

/-! ### Propositions that claim a reduction exists -/

/-- The old `Prop`-valued statement. -/
theorem bad5 : Nonempty (Undecidable fun n : ℕ => Even n) :=
  ⟨withFunction _ classicalFn.choose_spec⟩

/-- An existential over reductions. -/
theorem bad6 : ∃ _ : HaltProblem ⪯ₘ fun n : ℕ => Even n, True :=
  ⟨withFunction _ classicalFn.choose_spec, trivial⟩

/-- A `Prop`-valued alias, as `Undecidable` used to be. Defining it is allowed. -/
def OldUndecidable (p : ℕ → Prop) : Prop := Nonempty (HaltProblem ⪯ₘ p)

/-- A theorem through the alias. -/
theorem bad7 : OldUndecidable fun n : ℕ => Even n := ⟨withFunction _ classicalFn.choose_spec⟩

/-- An inductive proposition that stores a reduction. -/
inductive Hidden : Prop
  | intro (r : HaltProblem ⪯ₘ fun n : ℕ => Even n)

/-- A reduction postulated as an axiom. -/
axiom badAxiom : HaltProblem ⪯ₘ fun n : ℕ => Even n

/-- An axiom stated with `Undecidable`. -/
axiom bad8 : Undecidable fun n : ℕ => Even n

/-- An `opaque` reduction. -/
noncomputable opaque bad9 : Undecidable fun n : ℕ => Even n :=
  withFunction _ classicalFn.choose_spec

/-! ### Reductions wrapped in another type -/

/-- A definition that turns any function into a reduction, inside an `Equiv`. -/
def dependent :
    (∀ x : EncodableTM Bool × List Bool, {n : ℕ // HaltProblem x ↔ Even n}) ≃
      (HaltProblem ⪯ₘ fun n : ℕ => Even n) where
  toFun g := ⟨fun x => (g x).1, fun x => (g x).2⟩
  invFun r x := ⟨r.f x, r.hf x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A structure that stores a reduction in a field. -/
structure Bad10 where
  r : HaltProblem ⪯ₘ fun n : ℕ => Even n

/-! ### Escape hatches in dependencies

`oracle` is noncomputable with a classical body, but `implemented_by` gives it the code of a stub,
so every definition that calls it compiles without being marked `noncomputable`. Logically,
`haltOracle` and `pcpOracle` decide the halting problem and PCP. -/

universe u

/-- The stub that runs in place of `oracle`. -/
def oracleStub {α : Type u} (_ : α → Prop) (_ : α) : Bool := false

/-- A classical decision procedure, given compiled code by `implemented_by`. -/
@[implemented_by oracleStub]
noncomputable def oracle {α : Type u} (p : α → Prop) (x : α) : Bool :=
  haveI := Classical.propDecidable (p x); decide (p x)

theorem oracle_spec {α : Type u} (p : α → Prop) (x : α) : oracle p x = true ↔ p x := by
  simp [oracle]

/-- Compiles with no flag of its own; logically decides `HaltProblem`. -/
def haltOracle (x : EncodableTM Bool × List Bool) : Bool := oracle HaltProblem x

/-- One more level of indirection. -/
def haltOracle' (x : EncodableTM Bool × List Bool) : Bool := !(!haltOracle x)

/-- A reduction whose dependencies hide the oracle, two calls down. -/
def bad11 : Undecidable fun b : Bool => b = true :=
  ⟨haltOracle', fun x => by simp [haltOracle', haltOracle, oracle_spec]⟩

/-- `implemented_by` on the reduction itself. -/
@[implemented_by bad11]
noncomputable def bad12 : Undecidable fun b : Bool => b = true :=
  ⟨fun x => oracle HaltProblem x, fun x => by simp [oracle_spec]⟩

/-- Compiles with no flag of its own; logically decides PCP. -/
def pcpOracle {α : Type} (P : DiagonaLean.PCP.Stack α) : Bool :=
  oracle DiagonaLean.PCP.DecisionProblem P

/-- A reduction from PCP whose dependencies hide the oracle. -/
def bad13 {α : Type} : @DiagonaLean.PCP.DecisionProblem α ⪯ₘ fun b : Bool => b = true :=
  ⟨pcpOracle, fun P => by simp [pcpOracle, oracle_spec]⟩

/-- `reduce_from_pcp` with that reduction: the composite depends on the oracle too. -/
def bad14 : Undecidable fun b : Bool => b = true := by
  reduce_from_pcp over_letters true false via bad13

/-- A `partial def`: compiled, with no logical body. -/
partial def spin (n : ℕ) : ℕ := spin (n + 1)

/-- A reduction that depends on it. -/
def bad15 : (fun n : ℕ => Even n) ⪯ₘ fun n : ℕ => Even n :=
  ⟨fun n => if spin n = 0 then n else n, fun _ => by simp⟩

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- A reduction whose function is `sorry`: it compiles, and `sorryAx` is in `Init`. -/
def bad16 : Undecidable fun n : ℕ => Even n := ⟨sorry, sorry⟩

/-- The oracle hidden in an instance, so the reduction reaches it through instance resolution. -/
instance haltDecidable : DecidablePred HaltProblem := fun x =>
  decidable_of_iff (oracle HaltProblem x = true) (oracle_spec _ _)

/-- A reduction that decides `HaltProblem` with that instance. -/
def bad17 : Undecidable fun n : ℕ => Even n :=
  ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩

/-! ### Proofs that lie, code swapped by `@[csimp]`, and names that look generated -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- A false correctness proof, behind a theorem, which the dependency walk does not enter. -/
theorem liesSorry : ∀ x : EncodableTM Bool × List Bool, HaltProblem x ↔ Even (0 : ℕ) := sorry

/-- Honest code with that proof. -/
def bad18 : Undecidable fun n : ℕ => Even n := ⟨fun _ => 0, liesSorry⟩

/-- A false axiom that mentions no reduction. -/
axiom liesAxiom : ∀ x : EncodableTM Bool × List Bool, HaltProblem x ↔ Even (0 : ℕ)

/-- The axiom behind a theorem. -/
theorem liesAxiom' : ∀ x : EncodableTM Bool × List Bool, HaltProblem x ↔ Even (0 : ℕ) := liesAxiom

/-- Honest code with that proof. -/
def bad19 : Undecidable fun n : ℕ => Even n := ⟨fun _ => 0, liesAxiom'⟩

/-- Logically `true`, but runs as `false`. -/
@[implemented_by oracleStub]
def honestTrue {α : Type u} (_ : α → Prop) (_ : α) : Bool := true

/-- `native_decide` trusts the compiled code, so it proves a false equation. -/
theorem nativeLie : honestTrue (fun _ : Unit => True) () = false := by native_decide

/-- A reduction whose proof goes through it. -/
def bad20 : Undecidable fun n : ℕ => Even n :=
  ⟨fun _ => 0, absurd nativeLie (by simp [honestTrue])⟩

/-- The case split, logically. -/
noncomputable def classicalF (x : EncodableTM Bool × List Bool) : ℕ :=
  haveI := Classical.propDecidable (HaltProblem x); if HaltProblem x then 0 else 1

theorem classicalF_spec : HaltProblem ⪯ₘ[classicalF] fun n : ℕ => Even n := fun x => by
  unfold classicalF; split <;> simp_all [Nat.not_even_one]

/-- The code that runs in its place. -/
def stubF (_ : EncodableTM Bool × List Bool) : ℕ := 0

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- A false `@[csimp]` lemma: the compiler replaces `classicalF` by `stubF`. -/
@[csimp] theorem classicalF_eq : @classicalF = @stubF := sorry

/-- So this compiles without `noncomputable`. It is reported through `classicalF_eq`, the lemma
that changes its code. -/
def bad21 : Undecidable fun n : ℕ => Even n := ⟨classicalF, classicalF_spec⟩

/-- A name inside a reduction structure's namespace. -/
noncomputable def DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad22 :
    Undecidable fun n : ℕ => Even n := ⟨classicalF, classicalF_spec⟩

/-- A name under a constructor, like the generated `Foo.mk.injEq`. -/
noncomputable def Nat.succ.bad23 : Undecidable fun n : ℕ => Even n :=
  ⟨classicalF, classicalF_spec⟩

/-- A name with an internal component, like the generated `foo._proof_1`. -/
noncomputable def bad24._hidden : Undecidable fun n : ℕ => Even n :=
  ⟨classicalF, classicalF_spec⟩

/-- The name of a generated curried constructor (`Hidden.intro` has none), whose body is not the
constructor. -/
noncomputable def Hidden.intro._flat_ctor : Undecidable fun n : ℕ => Even n :=
  ⟨classicalF, classicalF_spec⟩

/-- A name that ends like the generated `foo._sunfold`. -/
noncomputable def bad25_sunfold : Undecidable fun n : ℕ => Even n := ⟨classicalF, classicalF_spec⟩

/-- A definition for the next one to be named after. -/
def sunfoldBase : ℕ := 0

/-- The generated name `foo._sunfold` itself, for a definition `foo` of another type. -/
noncomputable def sunfoldBase._sunfold : Undecidable fun n : ℕ => Even n := ⟨classicalF, classicalF_spec⟩

/-- The name of a generated `SizeOf` instance, for a type (`Hidden`, a proposition) that has none. -/
noncomputable def Hidden._sizeOf_inst : Undecidable fun n : ℕ => Even n :=
  ⟨classicalF, classicalF_spec⟩

/-! ### Theorems with names that look generated -/

/-- An internal name, like the generated `foo._proof_1`. -/
theorem bad26._hidden : Nonempty (Undecidable fun n : ℕ => Even n) := ⟨⟨classicalF, classicalF_spec⟩⟩

/-- A name under a constructor, like the generated `Foo.mk.injEq`. -/
theorem Nat.succ.bad27 : Nonempty (Undecidable fun n : ℕ => Even n) := ⟨⟨classicalF, classicalF_spec⟩⟩

/-- A theorem inside a reduction structure's namespace. -/
theorem DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad28 :
    Nonempty (Undecidable fun n : ℕ => Even n) := ⟨⟨classicalF, classicalF_spec⟩⟩

/-- An axiom inside a reduction structure's namespace. -/
axiom DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad29 :
    Nonempty (Undecidable fun n : ℕ => Even n)

/-- A structure inside a reduction structure's namespace, whose constructor stores a reduction. -/
structure DiagonaLean.Synthetic.Definitions.ManyOneReduces.Bad30 where
  r : HaltProblem ⪯ₘ fun n : ℕ => Even n

/-! ### Aliases that are not literally types -/

/-- An alias whose declared type is a sort only after β-reduction. -/
def TBeta : (fun _ : Unit => Type 1) () := Undecidable fun n : ℕ => Even n

/-- A reduction stated with it. -/
noncomputable def bad31 : TBeta := (⟨classicalF, classicalF_spec⟩ : Undecidable fun n : ℕ => Even n)

/-- A structure with a type field. -/
structure Box where
  /-- The stored type. -/
  T : Type 1

/-- `Undecidable` stored in it. -/
def box : Box := ⟨Undecidable fun n : ℕ => Even n⟩

/-- A reduction stated with the field. -/
noncomputable def bad32 : box.T := (⟨classicalF, classicalF_spec⟩ : Undecidable fun n : ℕ => Even n)

/-- A proposition alias whose declared type is a sort only after β-reduction. -/
def PBeta : (fun _ : Unit => Prop) () := Nonempty (Undecidable fun n : ℕ => Even n)

/-- A theorem through it. -/
theorem bad33 : PBeta := ⟨⟨classicalF, classicalF_spec⟩⟩

/-! ### Claims with the reduction in a hypothesis of a hypothesis, or a quantified function -/

/-- Double negation. -/
theorem bad34 : ¬¬ Nonempty (Undecidable fun n : ℕ => Even n) :=
  fun h => h ⟨⟨classicalF, classicalF_spec⟩⟩

/-- The Church encoding of `Nonempty`. -/
theorem bad35 : ∀ c : Prop, (Undecidable (fun n : ℕ => Even n) → c) → c :=
  fun _ h => h ⟨classicalF, classicalF_spec⟩

/-- The relation `⪯ₘ[f]` with `f` quantified. -/
theorem bad36 : ∃ f : EncodableTM Bool × List Bool → ℕ, HaltProblem ⪯ₘ[f] fun n => Even n :=
  classicalFn

/-! ### Honest declarations -/

/-- A compiled reduction of `HaltProblem` to itself. -/
def goodReduction : Undecidable HaltProblem := ⟨id, fun _ => Iff.rfl⟩

/-- Composition of compiled reductions. -/
def good1 : Undecidable HaltProblem := undecidabilityFromReducibility goodReduction goodReduction

/-- Honest local helpers are allowed. -/
def double (n : ℕ) : ℕ := 2 * n

/-- A reduction through a local helper. -/
def good2 : (fun n : ℕ => Even (double n)) ⪯ₘ fun _ : ℕ => True :=
  ⟨double, fun n => by simp [double]⟩

/-- An honest reduction from PCP. -/
def goodPCP : @DiagonaLean.PCP.DecisionProblem Bool ⪯ₘ @DiagonaLean.PCP.DecisionProblem Bool :=
  ⟨id, fun _ => Iff.rfl⟩

/-- `reduce_from_pcp` with an honest reduction and explicit letters. -/
def good3 : Undecidable (@DiagonaLean.PCP.DecisionProblem Bool) := by
  reduce_from_pcp over_letters true false via goodPCP

/-- A theorem may take reductions as hypotheses. -/
theorem good4 {p : ℕ → Prop} (r : HaltProblem ⪯ₘ p) (x : EncodableTM Bool × List Bool) :
    p (r.f x) ↔ HaltProblem x :=
  (r.hf x).symm

/-- A predicate on reductions is not a carrier, so theorems about it are allowed. -/
def IsId (r : HaltProblem ⪯ₘ HaltProblem) : Prop := r.f = id

/-- A theorem about a named reduction. -/
theorem good5 : IsId goodReduction := rfl

/-- A reduction's function passed without its input is not a reduction. -/
theorem good6 : goodReduction.f = id := rfl

/-- That no reduction exists may be stated: the reduction occurs only in a hypothesis. -/
theorem good7 : ¬ Nonempty ((fun _ : Unit => True) ⪯ₘ fun _ : Unit => False) :=
  fun ⟨r⟩ => (r.hf ()).mp trivial

/-- The relation `⪯ₘ[f]` for a given function. -/
theorem good8 (r : HaltProblem ⪯ₘ HaltProblem) : HaltProblem ⪯ₘ[r.f] HaltProblem := r.hf

/-- A hypothesis that produces reductions. -/
theorem good9 (_ : ℕ → Undecidable HaltProblem) : True := trivial

/--
error: `bad1` builds a reduction but is marked `noncomputable`
---
error: `bad11` builds a reduction that depends on `oracle`, which uses `implemented_by`, via bad11 → haltOracle' → haltOracle → oracle
---
error: `bad12` builds a reduction but is marked `noncomputable`
---
error: `bad13` builds a reduction that depends on `oracle`, which uses `implemented_by`, via bad13 → pcpOracle → oracle
---
error: `bad14` builds a reduction that depends on `oracle`, which uses `implemented_by`, via bad14 → bad13 → pcpOracle → oracle
---
error: `bad15` builds a reduction that depends on `spin`, which is `opaque` or `partial`, via bad15 → spin
---
error: `bad16` builds a reduction that depends on `sorryAx`, which is `sorry`, via bad16 → sorryAx
---
error: `bad17` builds a reduction that depends on `oracle`, which uses `implemented_by`, via bad17 → haltDecidable → oracle
---
error: `bad18` builds a reduction that depends on `sorry`
---
error: `bad19` builds a reduction that depends on the axiom `liesAxiom`
---
error: `bad2` builds a reduction but is marked `noncomputable`
---
error: `bad20` builds a reduction that depends on the axiom `nativeLie._native.native_decide.ax_1_1`
---
error: `bad25_sunfold` builds a reduction but is marked `noncomputable`
---
error: `bad3` builds a reduction but is marked `noncomputable`
---
error: `bad31` builds a reduction but is marked `noncomputable`
---
error: `bad32` builds a reduction but is marked `noncomputable`
---
error: `bad33` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad34` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad35` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad36` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad4` builds a reduction but is marked `noncomputable`
---
error: `bad5` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad6` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad7` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad8` is an axiom about reductions
---
error: `bad9` is an opaque or partial declaration about reductions
---
error: `badAxiom` is an axiom about reductions
---
error: `classicalFn` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `dependent` returns a reduction inside another type
---
error: `Bad10.mk` stores a reduction inside another type
---
error: `Hidden._sizeOf_inst` builds a reduction but is marked `noncomputable`
---
error: `Hidden.intro` stores a reduction inside another type
---
error: `bad2._proof_1` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad24._hidden` builds a reduction but is marked `noncomputable`
---
error: `bad26._hidden` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `dependent._proof_6` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `sunfoldBase._sunfold` builds a reduction but is marked `noncomputable`
---
error: `Bad10.mk.inj` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `Bad10.mk.injEq` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `Bad10.mk.sizeOf_spec` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `Hidden.intro._flat_ctor` builds a reduction but is marked `noncomputable`
---
error: `Nat.succ.bad23` builds a reduction but is marked `noncomputable`
---
error: `Nat.succ.bad27` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad22` builds a reduction but is marked `noncomputable`
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad28` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad29` is an axiom about reductions
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.Bad30.mk` stores a reduction inside another type
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.Bad30.mk.inj` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.Bad30.mk.injEq` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.Bad30.mk.sizeOf_spec` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `classicalF_eq` is a `@[csimp]` lemma that depends on `sorry`, so the compiled code of `classicalF` may differ from its meaning
-/
#guard_msgs in
#check_reductions local
