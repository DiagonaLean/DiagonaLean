import DiagonaLean.Synthetic.ReductionCheck
import DiagonaLean.Synthetic.Undecidability

/-! Negative tests for `#check_reductions`, run by CI. Each `bad*` declaration, `dependent` and
`badAxiom` proves or enables `Undecidable` of the decidable predicate `Even` by a classical case
split, and must be reported. `withFunction`, `withInstance` and the `good*` declarations follow the
convention and must not be. -/

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

/--
error: `bad1` builds a reduction with `DiagonaLean.Synthetic.Definitions.ManyOneReduces.mk`
---
error: `bad1` passes the noncomputable `Classical.propDecidable` to a reduction
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
error: `badAxiom` is an axiom about reductions
---
error: `dependent` returns a reduction inside another type
-/
#guard_msgs in
#check_reductions local
