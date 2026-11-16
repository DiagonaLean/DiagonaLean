import DiagonaLean.Synthetic.ReductionCheck
import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.Synthetic.Tactics.ReduceFromPCP

/-! Negative tests for `#check_reductions`, run by CI. Each `bad*` declaration, `Bad*` structure,
`Hidden`, `dependent` and `badAxiom` produces or claims a reduction of `HaltProblem` (or PCP) to a
decidable predicate (`Even`, or `b = true` on `Bool`) by a classical case split, possibly hidden
behind an escape hatch in a dependency or `sorry`, and must be reported. The other declarations
follow the convention and must not be.

Since `Undecidable` is a type, a `theorem` cannot state it: Lean rejects
`theorem t : Undecidable p` itself. The cases below are what can still be written. -/

open DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation

/-- The classical case split, stated as an existential. -/
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

/-- `reduceFromPCP` with that reduction: the composite depends on the oracle too. -/
def bad14 : Undecidable fun b : Bool => b = true := by
  reduceFromPCP over_letters true false via bad13

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

/-- `reduceFromPCP` with an honest reduction and explicit letters. -/
def good3 : Undecidable (@DiagonaLean.PCP.DecisionProblem Bool) := by
  reduceFromPCP over_letters true false via goodPCP

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
error: `bad2` builds a reduction but is marked `noncomputable`
---
error: `bad3` builds a reduction but is marked `noncomputable`
---
error: `bad4` builds a reduction but is marked `noncomputable`
---
error: `bad5` states a proposition about a reduction; state the result as a definition whose value is the reduction
---
error: `bad6` states a proposition about a reduction; state the result as a definition whose value is the reduction
---
error: `bad7` states a proposition about a reduction; state the result as a definition whose value is the reduction
---
error: `bad8` is an axiom about reductions
---
error: `bad9` is an opaque or partial declaration about reductions
---
error: `badAxiom` is an axiom about reductions
---
error: `dependent` returns a reduction inside another type
---
error: `Bad10.mk` stores a reduction inside another type
---
error: `Hidden.intro` stores a reduction inside another type
-/
#guard_msgs in
#check_reductions local
