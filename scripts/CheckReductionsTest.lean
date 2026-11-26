import DiagonaLean.Synthetic.ReductionCheck
import DiagonaLean.Synthetic.HaltReduction
import DiagonaLean.Synthetic.Tactics.ReduceFromPCP
import DiagonaLean.Foundations.Computability.ComputableReduction

/-! Negative tests for `#check_reductions`, run by CI. Each `bad*` declaration, `Bad*` structure,
`Hidden`, `dependent`, `classicalFn`, `badAxiom` and the declarations with generated-looking names
produces or claims a reduction of `HaltProblem` (or PCP) to a
decidable predicate (`Even`, or `b = true` on `Bool`) by a classical case split, possibly hidden
behind an escape hatch in a dependency or `sorry`, and must be reported. The other declarations
follow the convention and must not be.

Since `SynthHaltReduction` is a type, a `theorem` cannot state it: Lean rejects
`theorem t : SynthHaltReduction p` itself. The cases below are what can still be written. -/

open DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions

/-- The classical case split, stated as an existential: a claim that a reduction exists. -/
theorem classicalFn :
    ∃ f : EncodableTM Bool × List Bool → ℕ, HaltProblem ⪯_s[f] fun n => Even n := by
  classical
  exact ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩

/-- A compiled definition that takes the reduction function as a parameter. -/
def withFunction (f : EncodableTM Bool × List Bool → ℕ)
    (h : HaltProblem ⪯_s[f] (fun n : ℕ => Even n)) : HaltProblem ⪯_s (fun n : ℕ => Even n) :=
  ⟨f, h⟩

/-! ### Definitions that are not compiled -/

/-- The case split in a `noncomputable` definition. -/
noncomputable def bad1 : SynthHaltReduction (fun n : ℕ => Even n) := by
  classical
  exact ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩

/-- The case split obtained from an existential by `Classical.choose`. -/
noncomputable def bad2 : SynthHaltReduction (fun n : ℕ => Even n) :=
  withFunction _ classicalFn.choose_spec

/-- A private reduction: private names start with `_private`, like generated ones. -/
private noncomputable def bad3 : SynthHaltReduction (fun n : ℕ => Even n) :=
  withFunction _ classicalFn.choose_spec

/-- A compiled definition that decides `HaltProblem` with an instance parameter. -/
def withInstance [DecidablePred HaltProblem] : HaltProblem ⪯_s (fun n : ℕ => Even n) :=
  ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩

/-- A classical instance passed to it. -/
noncomputable def bad4 : SynthHaltReduction (fun n : ℕ => Even n) :=
  @withInstance (Classical.decPred _)

/-! ### Propositions that claim a reduction exists -/

/-- The old `Prop`-valued statement. -/
theorem bad5 : Nonempty (SynthHaltReduction fun n : ℕ => Even n) :=
  ⟨withFunction _ classicalFn.choose_spec⟩

/-- An existential over reductions. -/
theorem bad6 : ∃ _ : HaltProblem ⪯_s fun n : ℕ => Even n, True :=
  ⟨withFunction _ classicalFn.choose_spec, trivial⟩

/-- A `Prop`-valued alias, as `Undecidable` (now `SynthHaltReduction`) used to be. Defining it is allowed. -/
def OldUndecidable (p : ℕ → Prop) : Prop := Nonempty (HaltProblem ⪯_s p)

/-- A theorem through the alias. -/
theorem bad7 : OldUndecidable fun n : ℕ => Even n := ⟨withFunction _ classicalFn.choose_spec⟩

/-- An inductive proposition that stores a reduction. -/
inductive Hidden : Prop
  | intro (r : HaltProblem ⪯_s fun n : ℕ => Even n)

/-- A reduction postulated as an axiom. -/
axiom badAxiom : HaltProblem ⪯_s fun n : ℕ => Even n

/-- An axiom stated with `SynthHaltReduction`. -/
axiom bad8 : SynthHaltReduction fun n : ℕ => Even n

/-- An `opaque` reduction. -/
noncomputable opaque bad9 : SynthHaltReduction fun n : ℕ => Even n :=
  withFunction _ classicalFn.choose_spec

/-! ### Reductions wrapped in another type -/

/-- A definition that turns any function into a reduction, inside an `Equiv`. -/
def dependent :
    (∀ x : EncodableTM Bool × List Bool, {n : ℕ // HaltProblem x ↔ Even n}) ≃
      (HaltProblem ⪯_s fun n : ℕ => Even n) where
  toFun g := ⟨fun x => (g x).1, fun x => (g x).2⟩
  invFun r x := ⟨r.f x, r.hf x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A structure that stores a reduction in a field. -/
structure Bad10 where
  r : HaltProblem ⪯_s fun n : ℕ => Even n

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
def bad11 : SynthHaltReduction fun b : Bool => b = true :=
  ⟨haltOracle', fun x => by simp [haltOracle', haltOracle, oracle_spec]⟩

/-- `implemented_by` on the reduction itself. -/
@[implemented_by bad11]
noncomputable def bad12 : SynthHaltReduction fun b : Bool => b = true :=
  ⟨fun x => oracle HaltProblem x, fun x => by simp [oracle_spec]⟩

/-- Compiles with no flag of its own; logically decides PCP. -/
def pcpOracle {α : Type} (P : DiagonaLean.PCP.Stack α) : Bool :=
  oracle DiagonaLean.PCP.DecisionProblem P

/-- A reduction from PCP whose dependencies hide the oracle. -/
def bad13 {α : Type} : @DiagonaLean.PCP.DecisionProblem α ⪯_s fun b : Bool => b = true :=
  ⟨pcpOracle, fun P => by simp [pcpOracle, oracle_spec]⟩

/-- `reduce_from_pcp` with that reduction: the composite depends on the oracle too. -/
def bad14 : SynthHaltReduction fun b : Bool => b = true := by
  reduce_from_pcp over_letters true false via bad13

/-- A `partial def`: compiled, with no logical body. -/
partial def spin (n : ℕ) : ℕ := spin (n + 1)

/-- A reduction that depends on it. -/
def bad15 : (fun n : ℕ => Even n) ⪯_s fun n : ℕ => Even n :=
  ⟨fun n => if spin n = 0 then n else n, fun _ => by simp⟩

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- A reduction whose function is `sorry`: it compiles, and `sorryAx` is in `Init`. -/
def bad16 : SynthHaltReduction fun n : ℕ => Even n := ⟨sorry, sorry⟩

/-- The oracle hidden in an instance, so the reduction reaches it through instance resolution. -/
instance haltDecidable : DecidablePred HaltProblem := fun x =>
  decidable_of_iff (oracle HaltProblem x = true) (oracle_spec _ _)

/-- A reduction that decides `HaltProblem` with that instance. -/
def bad17 : SynthHaltReduction fun n : ℕ => Even n :=
  ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩

/-! ### Proofs that lie, code swapped by `@[csimp]`, and names that look generated -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- A false correctness proof, behind a theorem, which the dependency walk does not enter. -/
theorem liesSorry : ∀ x : EncodableTM Bool × List Bool, HaltProblem x ↔ Even (0 : ℕ) := sorry

/-- Honest code with that proof. -/
def bad18 : SynthHaltReduction fun n : ℕ => Even n := ⟨fun _ => 0, liesSorry⟩

/-- A false axiom that mentions no reduction. -/
axiom liesAxiom : ∀ x : EncodableTM Bool × List Bool, HaltProblem x ↔ Even (0 : ℕ)

/-- The axiom behind a theorem. -/
theorem liesAxiom' : ∀ x : EncodableTM Bool × List Bool, HaltProblem x ↔ Even (0 : ℕ) := liesAxiom

/-- Honest code with that proof. -/
def bad19 : SynthHaltReduction fun n : ℕ => Even n := ⟨fun _ => 0, liesAxiom'⟩

/-- Logically `true`, but runs as `false`. -/
@[implemented_by oracleStub]
def honestTrue {α : Type u} (_ : α → Prop) (_ : α) : Bool := true

/-- `native_decide` trusts the compiled code, so it proves a false equation. -/
theorem nativeLie : honestTrue (fun _ : Unit => True) () = false := by native_decide

/-- A reduction whose proof goes through it. -/
def bad20 : SynthHaltReduction fun n : ℕ => Even n :=
  ⟨fun _ => 0, absurd nativeLie (by simp [honestTrue])⟩

/-- The case split, logically. -/
noncomputable def classicalF (x : EncodableTM Bool × List Bool) : ℕ :=
  haveI := Classical.propDecidable (HaltProblem x); if HaltProblem x then 0 else 1

theorem classicalF_spec : HaltProblem ⪯_s[classicalF] fun n : ℕ => Even n := fun x => by
  unfold classicalF; split <;> simp_all [Nat.not_even_one]

/-- The code that runs in its place. -/
def stubF (_ : EncodableTM Bool × List Bool) : ℕ := 0

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- A false `@[csimp]` lemma: the compiler replaces `classicalF` by `stubF`. -/
@[csimp] theorem classicalF_eq : @classicalF = @stubF := sorry

/-- So this compiles without `noncomputable`. It is reported through `classicalF_eq`, the lemma
that changes its code. -/
def bad21 : SynthHaltReduction fun n : ℕ => Even n := ⟨classicalF, classicalF_spec⟩

/-- A name inside a reduction structure's namespace. -/
noncomputable def DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad22 :
    SynthHaltReduction fun n : ℕ => Even n := ⟨classicalF, classicalF_spec⟩

/-- A name under a constructor, like the generated `Foo.mk.injEq`. -/
noncomputable def Nat.succ.bad23 : SynthHaltReduction fun n : ℕ => Even n :=
  ⟨classicalF, classicalF_spec⟩

/-- A name with an internal component, like the generated `foo._proof_1`. -/
noncomputable def bad24._hidden : SynthHaltReduction fun n : ℕ => Even n :=
  ⟨classicalF, classicalF_spec⟩

/-- The name of a generated curried constructor (`Hidden.intro` has none), whose body is not the
constructor. -/
noncomputable def Hidden.intro._flat_ctor : SynthHaltReduction fun n : ℕ => Even n :=
  ⟨classicalF, classicalF_spec⟩

/-- A name that ends like the generated `foo._sunfold`. -/
noncomputable def bad25_sunfold : SynthHaltReduction fun n : ℕ => Even n := ⟨classicalF, classicalF_spec⟩

/-- A definition for the next one to be named after. -/
def sunfoldBase : ℕ := 0

/-- The generated name `foo._sunfold` itself, for a definition `foo` of another type. -/
noncomputable def sunfoldBase._sunfold : SynthHaltReduction fun n : ℕ => Even n := ⟨classicalF, classicalF_spec⟩

/-- The name of a generated `SizeOf` instance, for a type (`Hidden`, a proposition) that has none. -/
noncomputable def Hidden._sizeOf_inst : SynthHaltReduction fun n : ℕ => Even n :=
  ⟨classicalF, classicalF_spec⟩

/-! ### Theorems with names that look generated -/

/-- An internal name, like the generated `foo._proof_1`. -/
theorem bad26._hidden : Nonempty (SynthHaltReduction fun n : ℕ => Even n) := ⟨⟨classicalF, classicalF_spec⟩⟩

/-- A name under a constructor, like the generated `Foo.mk.injEq`. -/
theorem Nat.succ.bad27 : Nonempty (SynthHaltReduction fun n : ℕ => Even n) := ⟨⟨classicalF, classicalF_spec⟩⟩

/-- A theorem inside a reduction structure's namespace. -/
theorem DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad28 :
    Nonempty (SynthHaltReduction fun n : ℕ => Even n) := ⟨⟨classicalF, classicalF_spec⟩⟩

/-- An axiom inside a reduction structure's namespace. -/
axiom DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad29 :
    Nonempty (SynthHaltReduction fun n : ℕ => Even n)

/-- A structure inside a reduction structure's namespace, whose constructor stores a reduction. -/
structure DiagonaLean.Synthetic.Definitions.ManyOneReduces.Bad30 where
  r : HaltProblem ⪯_s fun n : ℕ => Even n

/-! ### The renamed structure and relation, and the former names kept as aliases

`SynthReduction` is the reduction structure; `ManyOneReduces`, `Undecidable` and `Reduction` are
its former names and those of `SynthHaltReduction` and `ReducesVia`, kept as deprecated aliases. The cases
above use `ManyOneReduces.*` names, now the namespace of an alias; these use the structure's own
namespace, and reach the structure and the relation through each alias. -/

/-- A definition inside the structure's namespace. -/
noncomputable def DiagonaLean.Synthetic.Definitions.SynthReduction.bad50 :
    SynthHaltReduction fun n : ℕ => Even n := ⟨classicalF, classicalF_spec⟩

/-- A theorem inside the structure's namespace. -/
theorem DiagonaLean.Synthetic.Definitions.SynthReduction.bad51 :
    Nonempty (SynthHaltReduction fun n : ℕ => Even n) := ⟨⟨classicalF, classicalF_spec⟩⟩

/-- A structure inside the structure's namespace, whose constructor stores a reduction. -/
structure DiagonaLean.Synthetic.Definitions.SynthReduction.Bad52 where
  r : HaltProblem ⪯_s fun n : ℕ => Even n

set_option linter.deprecated false in
/-- A reduction typed through the alias `ManyOneReduces`. -/
noncomputable def bad53 : ManyOneReduces HaltProblem fun n : ℕ => Even n :=
  ⟨classicalF, classicalF_spec⟩

/-- A reduction typed through `SynthHaltReduction` directly. -/
noncomputable def bad54 : SynthHaltReduction fun n : ℕ => Even n := ⟨classicalF, classicalF_spec⟩

set_option linter.deprecated false in
/-- A claim that a reduction exists, through the former relation name `Reduction`. -/
theorem bad55 :
    ∃ f : EncodableTM Bool × List Bool → ℕ, Reduction f HaltProblem fun n => Even n :=
  ⟨classicalF, classicalF_spec⟩

set_option linter.deprecated false in
/-- A reduction typed through the former name `Undecidable`, in its old namespace. -/
noncomputable def bad56 : DiagonaLean.Synthetic.Notation.Undecidable fun n : ℕ => Even n :=
  ⟨classicalF, classicalF_spec⟩

/-! ### Aliases that are not literally types -/

/-- An alias whose declared type is a sort only after β-reduction. -/
def TBeta : (fun _ : Unit => Type 1) () := SynthHaltReduction fun n : ℕ => Even n

/-- A reduction stated with it. -/
noncomputable def bad31 : TBeta := (⟨classicalF, classicalF_spec⟩ : SynthHaltReduction fun n : ℕ => Even n)

/-- A structure with a type field. -/
structure Box where
  /-- The stored type. -/
  T : Type 1

/-- `SynthHaltReduction` stored in it. -/
def box : Box := ⟨SynthHaltReduction fun n : ℕ => Even n⟩

/-- A reduction stated with the field. -/
noncomputable def bad32 : box.T := (⟨classicalF, classicalF_spec⟩ : SynthHaltReduction fun n : ℕ => Even n)

/-- A proposition alias whose declared type is a sort only after β-reduction. -/
def PBeta : (fun _ : Unit => Prop) () := Nonempty (SynthHaltReduction fun n : ℕ => Even n)

/-- A theorem through it. -/
theorem bad33 : PBeta := ⟨⟨classicalF, classicalF_spec⟩⟩

/-! ### Claims with the reduction in a hypothesis of a hypothesis, or a quantified function -/

/-- Double negation. -/
theorem bad34 : ¬¬ Nonempty (SynthHaltReduction fun n : ℕ => Even n) :=
  fun h => h ⟨⟨classicalF, classicalF_spec⟩⟩

/-- The Church encoding of `Nonempty`. -/
theorem bad35 : ∀ c : Prop, (SynthHaltReduction (fun n : ℕ => Even n) → c) → c :=
  fun _ h => h ⟨classicalF, classicalF_spec⟩

/-- The relation `⪯_s[f]` with `f` quantified. -/
theorem bad36 : ∃ f : EncodableTM Bool × List Bool → ℕ, HaltProblem ⪯_s[f] fun n => Even n :=
  classicalFn

/-! ### Honest declarations -/

/-- A compiled reduction of `HaltProblem` to itself. -/
def goodReduction : SynthHaltReduction HaltProblem := ⟨id, fun _ => Iff.rfl⟩

/-- Composition of compiled reductions. -/
def good1 : SynthHaltReduction HaltProblem := SynthHaltReduction.comp goodReduction goodReduction

/-- Honest local helpers are allowed. -/
def double (n : ℕ) : ℕ := 2 * n

/-- A reduction through a local helper. -/
def good2 : (fun n : ℕ => Even (double n)) ⪯_s fun _ : ℕ => True :=
  ⟨double, fun n => by simp [double]⟩

/-- An honest reduction from PCP. -/
def goodPCP : @DiagonaLean.PCP.DecisionProblem Bool ⪯_s @DiagonaLean.PCP.DecisionProblem Bool :=
  ⟨id, fun _ => Iff.rfl⟩

/-- `reduce_from_pcp` with an honest reduction and explicit letters. -/
def good3 : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem Bool) := by
  reduce_from_pcp over_letters true false via goodPCP

/-- A theorem may take reductions as hypotheses. -/
theorem good4 {p : ℕ → Prop} (r : HaltProblem ⪯_s p) (x : EncodableTM Bool × List Bool) :
    p (r.f x) ↔ HaltProblem x :=
  (r.hf x).symm

/-- A predicate on reductions is not a carrier, so theorems about it are allowed. -/
def IsId (r : HaltProblem ⪯_s HaltProblem) : Prop := r.f = id

/-- A theorem about a named reduction. -/
theorem good5 : IsId goodReduction := rfl

/-- A reduction's function passed without its input is not a reduction. -/
theorem good6 : goodReduction.f = id := rfl

/-- That no reduction exists may be stated: the reduction occurs only in a hypothesis. -/
theorem good7 : ¬ Nonempty ((fun _ : Unit => True) ⪯_s fun _ : Unit => False) :=
  fun ⟨r⟩ => (r.hf ()).mp trivial

/-- The relation `⪯_s[f]` for a given function. -/
theorem good8 (r : HaltProblem ⪯_s HaltProblem) : HaltProblem ⪯_s[r.f] HaltProblem := r.hf

/-- A hypothesis that produces reductions. -/
theorem good9 (_ : ℕ → SynthHaltReduction HaltProblem) : True := trivial

/-- A claim that a *computable* reduction exists (`⪯[f]`) has content, unlike `∃ f, p ⪯_s[f] q`:
it is Mathlib's `ManyOneReducible`, so it may be stated. -/
theorem goodComputableExists : ∃ f : ℕ → ℕ,
    (fun n : ℕ => Even n) ⪯[f] (fun n : ℕ => Even n) :=
  ⟨id, Computable.id, fun _ => Iff.rfl⟩

/-! ### Rule 4: encodings are programs

Under a classical encoding, `Computable`, `ComputablePred` and `MachineDecidable` are about the
encoding, not about a program: with `encode := σ` for a classical bijection `σ` that sends the
halting set to the even numbers, a decidable predicate is provably not computable (NOTIONS-style
counterexample in the module docstring). The `σ` below is only `Classical.choice` of the identity,
which is enough to test that the check sees it. Found by the attack round on the proved layer
(2026-11-26), cases P1–P3 and P6–P8. -/

/-- A type with the encodings below. -/
def EncW := ℕ

/-- A classical bijection. -/
noncomputable def encσ : EncW ≃ ℕ := Classical.choice ⟨Equiv.refl ℕ⟩

/-- A classical `Primcodable` instance (P1). -/
noncomputable instance badEncInst : Primcodable EncW := Primcodable.ofEquiv ℕ encσ

/-- An `encode` whose compiled code is swapped (P2). -/
def badEncFn (n : ℕ) : ℕ := n
/-- The code swapped in. -/
def badEncImpl (n : ℕ) : ℕ := n + 1
attribute [implemented_by badEncImpl] badEncFn

/-- A type with the swapped encoding. -/
def EncW2 := ℕ

/-- An `Encodable` instance through the swapped `encode` (P2). -/
instance badEncInst2 : Encodable EncW2 := ⟨badEncFn, fun n => some n, fun _ => rfl⟩

/-- A classical machine encoding. -/
noncomputable def badMachineEnc : ℕ → List Bool := fun n =>
  if (Classical.propDecidable (n = 0)).decide then [] else [true]

/-- A statement about the classical machine encoding (P3). -/
theorem badEncMachine : MachineDecidable badMachineEnc (fun _ : ℕ => True) ∨ True := Or.inr trivial

/-- The classical instance written inline (P6). -/
theorem badEncInline : @Computable EncW ℕ (Primcodable.ofEquiv ℕ encσ) _ (fun _ => 0) :=
  @Computable.const EncW ℕ (Primcodable.ofEquiv ℕ encσ) _ 0

/-- The classical machine encoding in the body of a predicate that statements only name (P7). -/
def badEncPred (P : ℕ → Prop) : Prop := MachineDecidable badMachineEnc P

/-- A class that extends `Primcodable`. -/
class EncCodes (α : Type) extends Primcodable α

/-- An instance of it, built from the classical instance. -/
noncomputable instance badEncCodes : EncCodes EncW := ⟨⟩

/-- A statement through the projection to `Primcodable` (P8). -/
theorem badEncExtends : @Computable EncW ℕ EncCodes.toPrimcodable _ (fun _ => 0) :=
  @Computable.const EncW ℕ EncCodes.toPrimcodable _ 0

/-- A type with an honest encoding. -/
def EncW3 := ℕ

/-- An honest `Encodable` instance: compiled, no escape hatch. -/
instance goodEncInst : Encodable EncW3 := ⟨fun n => n, fun n => some n, fun _ => rfl⟩

/-- A statement about every computable machine encoding: the encoding is a variable. -/
theorem goodEncVariable (P : ℕ → Prop) (h : ∀ enc : ℕ → List Bool, Computable enc →
    ¬ MachineDecidable enc P) : ∀ enc : ℕ → List Bool, Computable enc → ¬ MachineDecidable enc P :=
  h

/-! Rounds 2 and 3 of the attack (2026-11-26): encodings that a fixed list of machine-level
predicates, or a check of closed encodings only, did not see. -/

open Cslib.Turing in
/-- `TMDeciderFor`, found from its type rather than a list (Q1). -/
theorem badEncTMDecider (D : SingleTapeTM Bool) :
    TMDeciderFor D badMachineEnc (fun _ => True) ∨ True := Or.inr trivial

/-- A structure that bundles a machine encoding. -/
structure EncBox (X : Type) where
  /-- The encoding. -/
  enc : X → List Bool

/-- A predicate on such a structure. -/
def EncBoxDecidable (E : EncBox ℕ) (P : ℕ → Prop) : Prop := MachineDecidable E.enc P

/-- The classical encoding in a structure argument (Q2). -/
theorem badEncBox : EncBoxDecidable ⟨badMachineEnc⟩ (fun _ => True) ∨ True := Or.inr trivial

/-- A predicate on a curried encoding. -/
def EncCurried (enc : ℕ → ℕ → List Bool) (P : ℕ → ℕ → Prop) : Prop :=
  MachineDecidable (fun p : ℕ × ℕ => enc p.1 p.2) (fun p => P p.1 p.2)

/-- A curried classical encoding (Q3). -/
theorem badEncCurried : EncCurried (fun _ => badMachineEnc) (fun _ _ => True) ∨ True :=
  Or.inr trivial

/-- A predicate whose encoding is an implicit argument. -/
def EncImplicit {enc : ℕ → List Bool} (P : ℕ → Prop) : Prop := MachineDecidable enc P

/-- The classical encoding as an implicit argument (Q4). -/
theorem badEncImplicit : @EncImplicit badMachineEnc (fun _ => True) ∨ True := Or.inr trivial

/-- The classical encoding behind a beta-redex (Q6). -/
theorem badEncBeta :
    (fun e : ℕ → List Bool => MachineDecidable e (fun _ => True)) badMachineEnc ∨ True :=
  Or.inr trivial

/-- The classical encoding behind a `let` (Q7). -/
theorem badEncLet : (let e := badMachineEnc; MachineDecidable e (fun _ => True)) ∨ True :=
  Or.inr trivial

/-- A classical decidability instance inside an encoding that mentions a bound variable (Q10). -/
theorem badEncBound (p : ℕ → Prop) (hp : PrimrecPred p) :
    @Computable {n // p n} ℕ (@Primcodable.subtype ℕ _ p (Classical.decPred p) hp) _ (fun _ => 0) :=
  @Computable.const {n // p n} ℕ (@Primcodable.subtype ℕ _ p (Classical.decPred p) hp) _ 0

/-- A predicate on an encoding inside a pair. -/
def EncPair (p : (ℕ → List Bool) × Unit) (P : ℕ → Prop) : Prop := MachineDecidable p.1 P

/-- The classical encoding inside a pair (R1). -/
theorem badEncPair : EncPair (badMachineEnc, ()) (fun _ => True) ∨ True := Or.inr trivial

/-- A predicate that takes a class extending `Primcodable`. -/
def EncCodesPred (X : Type) [EncCodes X] (P : X → Prop) : Prop := ComputablePred P

/-- The classical instance through such a predicate (R2). -/
theorem badEncCodesPred : EncCodesPred EncW (fun _ => True) ∨ True := Or.inr trivial

/-- A `Prop` structure whose constructor fixes the classical encoding (R3). -/
structure BadEncStruct (P : ℕ → Prop) : Prop where
  /-- The fact. -/
  h : MachineDecidable badMachineEnc P

/-- An inductive predicate whose constructor fixes the classical encoding (R4). -/
inductive BadEncInd (P : ℕ → Prop) : Prop
  | intro : MachineDecidable badMachineEnc P → BadEncInd P

/-- An honest encoding in a structure argument, a quantified one, and a statement on
`EncodableTM` (whose structure has an `Encodable` field): none is reported. -/
def goodMachineEnc : ℕ → List Bool := fun n => List.replicate n false
theorem goodEncBox : EncBoxDecidable ⟨goodMachineEnc⟩ (fun _ => True) ∨ True := Or.inr trivial
theorem goodEncBoxVar : ∀ E : EncBox ℕ, EncBoxDecidable E (fun _ => True) ∨ True :=
  fun _ => Or.inr trivial
theorem goodEncHalt (M : EncodableTM Bool) (w : List Bool) : HaltProblem (M, w) ∨ True :=
  Or.inr trivial

/-! ### Registries (rule 2)

A registry of synthetic reductions as a class stores a reduction in a structure, which rule 2
rejects. A registry records names instead, through an attribute (NOTIONS §9.7, decided
2026-11-26); the proved layer has one as a class, `HaltSource`, since it is not checked. -/

/-- A class of synthetic sources (P9). -/
class BadSynthSource (p : ℕ → Prop) where
  /-- The source. -/
  red : SynthHaltReduction p

/-! ### Rule 5: statement and command syntax does not overlap existing syntax

Found by the attack of 2026-11-26: Lean picks the longest parse and reports only a tie, so the
first macro below makes `theorem t : ¬ A ∧ B` state `True ∨ (A ∧ B)` with no error, and leaves
`¬ A` alone. These declarations come last, since they change how the rest of a file parses. -/

/-- Takes over `¬ A ∧ B` (T4). -/
macro (name := badSyntaxNotAnd) "¬" p:term:36 "∧" q:term:35 : term => `(True ∨ ($p ∧ $q))

/-- A longer trailing `∧`. -/
macro:35 (name := badSyntaxAnd) p:term:36 " ∧ " q:term:0 : term => `(True ∨ ($p ∧ $q))

/-- Syntax that starts with an identifier: its first token cannot be read. -/
syntax (name := badSyntaxIdent) ident " ↦↦ " term : term

/-- A notation with a fresh first token: allowed. -/
notation:50 (name := goodSyntaxFresh) a " ≈≈ " b => a = b

/--
error: `bad1` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad11` builds a reduction that depends on `oracle`, which uses `implemented_by`, via bad11 → haltOracle' → haltOracle → oracle; remove the escape hatch from that dependency, or state a proved reduction (`⪯`), which needs none
---
error: `bad12` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad13` builds a reduction that depends on `oracle`, which uses `implemented_by`, via bad13 → pcpOracle → oracle; remove the escape hatch from that dependency, or state a proved reduction (`⪯`), which needs none
---
error: `bad14` builds a reduction that depends on `oracle`, which uses `implemented_by`, via bad14 → bad13 → pcpOracle → oracle; remove the escape hatch from that dependency, or state a proved reduction (`⪯`), which needs none
---
error: `bad15` builds a reduction that depends on `spin`, which is `opaque` or `partial`, via bad15 → spin; remove the escape hatch from that dependency, or state a proved reduction (`⪯`), which needs none
---
error: `bad16` builds a reduction that depends on `sorryAx`, which is `sorry`, via bad16 → sorryAx; remove the escape hatch from that dependency, or state a proved reduction (`⪯`), which needs none
---
error: `bad17` builds a reduction that depends on `oracle`, which uses `implemented_by`, via bad17 → haltDecidable → oracle; remove the escape hatch from that dependency, or state a proved reduction (`⪯`), which needs none
---
error: `bad18` builds a reduction that depends on `sorry`; remove it from the proofs it reaches
---
error: `bad19` builds a reduction that depends on the axiom `liesAxiom`; remove it from the proofs it reaches
---
error: `bad2` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad20` builds a reduction that depends on the axiom `nativeLie._native.native_decide.ax_1_1`; remove it from the proofs it reaches
---
error: `bad25_sunfold` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad3` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad31` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad32` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad33` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad34` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad35` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad36` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad4` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad5` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad53` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad54` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad55` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad56` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad6` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad7` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad8` is an axiom about reductions; prove it, or take it as a hypothesis
---
error: `bad9` is an opaque or partial declaration about reductions; use a `def` or a `theorem`
---
error: `badAxiom` is an axiom about reductions; prove it, or take it as a hypothesis
---
error: `badEncBeta` states a result about an encoding that uses `badMachineEnc`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncBound` states a result about an encoding that uses `Classical.decPred`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncBox` states a result about an encoding that uses `badMachineEnc`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncCodesPred` states a result about an encoding that uses `badEncCodes`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncCurried` states a result about an encoding that uses `badMachineEnc`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncExtends` states a result about an encoding that uses `badEncCodes`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncImplicit` states a result about an encoding that uses `badMachineEnc`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncInline` states a result about an encoding that uses `encσ`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncInst` is an encoding but is marked `noncomputable`; build the encoding from compiled definitions, or take it as a parameter
---
error: `badEncInst2` is an encoding that depends on `badEncFn`, which uses `implemented_by`, via badEncInst2 → badEncFn; build the encoding from compiled definitions, or take it as a parameter
---
error: `badEncLet` states a result about an encoding that uses `badMachineEnc`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncMachine` states a result about an encoding that uses `badMachineEnc`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncPair` states a result about an encoding that uses `badMachineEnc`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncPred` defines a predicate about an encoding that uses `badMachineEnc`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `badEncTMDecider` states a result about an encoding that uses `badMachineEnc`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `classicalFn` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `dependent` returns a reduction inside another type; return the reduction itself, and the other data from separate definitions
---
error: `Bad10.mk` stores a reduction inside another type; pass the reduction as a parameter (a registry records names, through an attribute)
---
error: `BadEncInd.intro` states a result about an encoding that uses `badMachineEnc`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `BadEncStruct.mk` states a result about an encoding that uses `badMachineEnc`, which is marked `noncomputable`; use a compiled encoding, or quantify over it
---
error: `BadSynthSource.mk` stores a reduction inside another type; pass the reduction as a parameter (a registry records names, through an attribute)
---
error: `Hidden._sizeOf_inst` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `Hidden.intro` stores a reduction inside another type; pass the reduction as a parameter (a registry records names, through an attribute)
---
error: `bad2._proof_1` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `bad24._hidden` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `bad26._hidden` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `dependent._proof_6` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `sunfoldBase._sunfold` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `Bad10.mk.inj` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `Bad10.mk.injEq` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `Bad10.mk.sizeOf_spec` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `Hidden.intro._flat_ctor` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `Nat.succ.bad23` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `Nat.succ.bad27` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad22` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad28` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.bad29` is an axiom about reductions; prove it, or take it as a hypothesis
---
error: `DiagonaLean.Synthetic.Definitions.SynthReduction.bad50` builds a reduction but is marked `noncomputable`; build its function from compiled definitions, or, for a result proved classically, prove `Computable` of it and state a proved reduction (`⪯`, `HaltReduction`) instead
---
error: `DiagonaLean.Synthetic.Definitions.SynthReduction.bad51` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.Bad30.mk` stores a reduction inside another type; pass the reduction as a parameter (a registry records names, through an attribute)
---
error: `DiagonaLean.Synthetic.Definitions.SynthReduction.Bad52.mk` stores a reduction inside another type; pass the reduction as a parameter (a registry records names, through an attribute)
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.Bad30.mk.inj` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.Bad30.mk.injEq` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.ManyOneReduces.Bad30.mk.sizeOf_spec` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.SynthReduction.Bad52.mk.inj` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.SynthReduction.Bad52.mk.injEq` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `DiagonaLean.Synthetic.Definitions.SynthReduction.Bad52.mk.sizeOf_spec` states a proposition that a reduction exists; state the result as a definition whose value is the reduction
---
error: `classicalF_eq` is a `@[csimp]` lemma that depends on `sorry`, so the compiled code of `classicalF` may differ from its meaning; prove it without `sorry` or a new axiom
---
error: `badSyntaxIdent` is term syntax whose first token cannot be read, so rule 5 cannot check that it does not overlap existing syntax; start it with a token
---
error: `badSyntaxNotAnd` is term syntax whose first token `¬` also starts 1 other parser(s), so a longer parse can take over existing notation without an error; start it with a fresh token, or add it to `syntaxOverlapAllowances` after review
---
error: `badSyntaxAnd` is term syntax whose first token `∧` also starts 1 other parser(s), so a longer parse can take over existing notation without an error; start it with a fresh token, or add it to `syntaxOverlapAllowances` after review
-/
#guard_msgs in
#check_reductions local
