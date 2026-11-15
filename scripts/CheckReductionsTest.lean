import DiagonaLean.Synthetic.ReductionCheck
import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.Synthetic.Tactics.ReduceFromPCP

/-! Negative tests for `#check_reductions`, run by CI. Each `bad*` declaration, `dependent` and
`badAxiom` proves or enables `Undecidable` of a decidable predicate (`Even`, or `b = true` on `Bool`)
by a classical case split, possibly hidden behind an escape hatch in a dependency, and must be
reported. `withFunction`, `withInstance`, `withBoolFunction`, `withPCPFunction` and the `good*`
declarations follow the convention and must not be. -/

open DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation

/-- The case split inline in a theorem, through the `classical` tactic. -/
theorem bad1 : Undecidable (fun n : ℕ => Even n) := by
  classical
  exact ⟨⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩⟩

/-- The case split inline, through `Classical.decEq`. -/
theorem bad2 : Undecidable (fun n : ℕ => Even n) :=
  ⟨⟨fun p => @ite _ (HaltProblem p = True) (Classical.decEq Prop _ _) 0 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩⟩

/-- The case split in a `noncomputable` definition. -/
noncomputable def bad3 : HaltProblem ⪯ₘ (fun n : ℕ => Even n) := by
  classical
  exact ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩

/-- A compiled definition that takes the reduction function as a parameter. -/
def withFunction (f : EncodableTM Bool × List Bool → ℕ)
    (h : HaltProblem ⪯ₘ[f] (fun n : ℕ => Even n)) : HaltProblem ⪯ₘ (fun n : ℕ => Even n) :=
  ⟨f, h⟩

/-- The case split obtained from an existential and passed as a function. -/
theorem bad4 : Undecidable (fun n : ℕ => Even n) := by
  obtain ⟨f, hf⟩ : ∃ f : EncodableTM Bool × List Bool → ℕ, HaltProblem ⪯ₘ[f] (fun n => Even n) := by
    classical
    exact ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
      by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩
  exact ⟨withFunction f hf⟩

/-- A compiled definition that decides `HaltProblem` with an instance parameter. -/
def withInstance [DecidablePred HaltProblem] : HaltProblem ⪯ₘ (fun n : ℕ => Even n) :=
  ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩

/-- A classical instance passed directly. -/
theorem bad5 : Undecidable (fun n : ℕ => Even n) :=
  ⟨@withInstance (Classical.decPred _)⟩

/-- A classical instance obtained from `Nonempty` and passed on. -/
theorem bad6 : Undecidable (fun n : ℕ => Even n) := by
  obtain ⟨inst⟩ : Nonempty (DecidablePred HaltProblem) := ⟨Classical.decPred _⟩
  exact ⟨@withInstance inst⟩

/-- A function wrapped in a subtype, passed through `Nonempty.map`. -/
theorem bad7 : Undecidable (fun n : ℕ => Even n) := by
  have h : Nonempty
      {f : EncodableTM Bool × List Bool → ℕ // HaltProblem ⪯ₘ[f] (fun n => Even n)} := by
    classical
    exact ⟨⟨fun p => if HaltProblem p then 0 else 1, fun p => by
      by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩⟩
  exact h.map fun s => withFunction s.1 s.2

/-- A definition that turns any function into a reduction, inside an `Equiv`. -/
def dependent :
    (∀ x : EncodableTM Bool × List Bool, {n : ℕ // HaltProblem x ↔ Even n}) ≃
      (HaltProblem ⪯ₘ fun n : ℕ => Even n) where
  toFun g := ⟨fun x => (g x).1, fun x => (g x).2⟩
  invFun r x := ⟨r.f x, r.hf x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The case split fed to `dependent` through `Nonempty.map`. -/
theorem bad8 : Undecidable (fun n : ℕ => Even n) := by
  have h : Nonempty (∀ x : EncodableTM Bool × List Bool, {n : ℕ // HaltProblem x ↔ Even n}) := by
    classical
    exact ⟨fun x => if h : HaltProblem x then ⟨0, by simp [h]⟩
      else ⟨1, by simp [h, Nat.not_even_one]⟩⟩
  exact h.map dependent

/-- A reduction postulated as an axiom. -/
axiom badAxiom : HaltProblem ⪯ₘ fun n : ℕ => Even n

/-- A compiled reduction of `HaltProblem` to itself. -/
def goodReduction : HaltProblem ⪯ₘ HaltProblem := ⟨id, fun _ => Iff.rfl⟩

/-- Undecidability through the compiled reduction. -/
theorem good1 : Undecidable HaltProblem := ⟨goodReduction⟩

/-- A finite constant obtained from an existential is allowed. -/
theorem good2 : Undecidable HaltProblem := by
  obtain ⟨n, -⟩ : ∃ n : ℕ, n = n := ⟨0, rfl⟩
  exact ⟨(fun _ => goodReduction) n⟩

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
def bad9 : HaltProblem ⪯ₘ fun b : Bool => b = true :=
  ⟨haltOracle', fun x => by simp [haltOracle', haltOracle, oracle_spec]⟩

/-- A compiled definition that takes the reduction function to `Bool` as a parameter. -/
def withBoolFunction (f : EncodableTM Bool × List Bool → Bool)
    (h : HaltProblem ⪯ₘ[f] fun b : Bool => b = true) : HaltProblem ⪯ₘ fun b : Bool => b = true :=
  ⟨f, h⟩

/-- The oracle passed as a named constant to a compiled definition. -/
theorem bad10 : Undecidable fun b : Bool => b = true :=
  ⟨withBoolFunction haltOracle fun x => by simp [haltOracle, oracle_spec]⟩

/-- Compiles with no flag of its own; logically decides PCP. -/
def pcpOracle {α : Type} (P : DiagonaLean.PCP.Stack α) : Bool :=
  oracle DiagonaLean.PCP.DecisionProblem P

/-- A reduction from PCP whose dependencies hide the oracle. -/
def bad11 {α : Type} : @DiagonaLean.PCP.DecisionProblem α ⪯ₘ fun b : Bool => b = true :=
  ⟨pcpOracle, fun P => by simp [pcpOracle, oracle_spec]⟩

/-- `reduceFromPCP` with that reduction. -/
theorem bad12 : Undecidable fun b : Bool => b = true := by
  reduceFromPCP over_type Bool via bad11

/-- A compiled definition that takes a reduction function from PCP as a parameter. -/
def withPCPFunction {α : Type} (f : DiagonaLean.PCP.Stack α → Bool)
    (h : @DiagonaLean.PCP.DecisionProblem α ⪯ₘ[f] fun b : Bool => b = true) :
    @DiagonaLean.PCP.DecisionProblem α ⪯ₘ fun b : Bool => b = true :=
  ⟨f, h⟩

/-- `reduceFromPCP` with the oracle passed as an argument. -/
theorem bad13 : Undecidable fun b : Bool => b = true := by
  reduceFromPCP over_type Bool via
    withPCPFunction pcpOracle fun P => by simp [pcpOracle, oracle_spec]

/-- A classical instance passed to `pcp_undecidable`, whose type mentions `Undecidable`, not `⪯ₘ`. -/
theorem bad14 : Undecidable (@DiagonaLean.PCP.DecisionProblem ℕ) :=
  @DiagonaLean.PCP.Reduction.pcp_undecidable ℕ (Classical.decEq ℕ) inferInstance

/-- A `partial def`: compiled, with no logical body. -/
partial def spin (n : ℕ) : ℕ := spin (n + 1)

/-- A reduction that depends on it. -/
def bad15 : (fun n : ℕ => Even n) ⪯ₘ fun n : ℕ => Even n :=
  ⟨fun n => if spin n = 0 then n else n, fun _ => by simp⟩

/-- Honest local helpers are allowed. -/
def double (n : ℕ) : ℕ := 2 * n

/-- A reduction through a local helper. -/
def good3 : (fun n : ℕ => Even (double n)) ⪯ₘ fun _ : ℕ => True :=
  ⟨double, fun n => by simp [double]⟩

/-- An honest reduction from PCP. -/
def goodPCP : @DiagonaLean.PCP.DecisionProblem Bool ⪯ₘ @DiagonaLean.PCP.DecisionProblem Bool :=
  ⟨id, fun _ => Iff.rfl⟩

/-- `reduceFromPCP` with an honest reduction. -/
theorem good4 : Undecidable (@DiagonaLean.PCP.DecisionProblem Bool) := by
  reduceFromPCP over_type Bool via goodPCP

/--
error: `bad1` builds a reduction with `DiagonaLean.Synthetic.Definitions.ManyOneReduces.mk`
---
error: `bad1` passes the noncomputable `Classical.propDecidable` to a reduction
---
error: `bad10` passes `haltOracle` to a reduction, which depends on `oracle`, which uses `implemented_by`, via haltOracle → oracle
---
error: `bad11` builds a reduction that depends on `oracle`, which uses `implemented_by`, via bad11 → pcpOracle → oracle
---
error: `bad12` passes `bad11` to a reduction, which depends on `oracle`, which uses `implemented_by`, via bad11 → pcpOracle → oracle
---
error: `bad13` passes `pcpOracle` to a reduction, which depends on `oracle`, which uses `implemented_by`, via pcpOracle → oracle
---
error: `bad14` passes the noncomputable `Classical.decEq` to a reduction
---
error: `bad15` builds a reduction that depends on `spin`, which is `opaque` or `partial`, via bad15 → spin
---
error: `bad2` builds a reduction with `DiagonaLean.Synthetic.Definitions.ManyOneReduces.mk`
---
error: `bad2` passes the noncomputable `Classical.decEq` to a reduction
---
error: `bad3` builds a reduction but is marked `noncomputable`
---
error: `bad4` passes `f`, which carries a function and is bound inside the proof, to a reduction
---
error: `bad5` passes the noncomputable `Classical.decPred` to a reduction
---
error: `bad6` passes `inst`, which carries a function and is bound inside the proof, to a reduction
---
error: `bad7` passes `s`, which carries a function and is bound inside the proof, to a reduction
---
error: `bad9` builds a reduction that depends on `oracle`, which uses `implemented_by`, via bad9 → haltOracle' → haltOracle → oracle
---
error: `badAxiom` is an axiom about reductions
---
error: `dependent` returns a reduction inside another type
-/
#guard_msgs in
#check_reductions local
