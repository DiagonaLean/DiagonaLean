/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Halt.Undecidable

@[expose] public section

/-! # Computably inseparable sets

`SelfOut b M` holds when `M` halts on its own code with output `[b]`. No Turing machine decides a
set containing `SelfOut true` and disjoint from `SelfOut false` (`selfOut_inseparable`). A
separation reduction (`SepReduces`) maps the first set into a predicate and the second into its
complement, so it transfers this inseparability (`InsepUndecidable`).

## References

* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing SingleTapeTM DiagonaLean.Halt.Encoding DiagonaLean.Halt.Compositions
  DiagonaLean.Halt.Undecidable DiagonaLean.Synthetic.Definitions

variable {X Y : Type*}

/-- `S` separates `A` from `B`. -/
def Separates (A B S : X → Prop) : Prop := (∀ x, A x → S x) ∧ ∀ x, B x → ¬ S x

/-- `f` maps `A` into `p` and `B` into the complement of `p`. As with `ManyOneReduces`, `f` is
meant to be built from the data of `x`, never by inspecting `A`, `B` or `p`. -/
structure SepReduces (A B : X → Prop) (p : Y → Prop) where
  /-- The reduction function. -/
  f : X → Y
  /-- `A` lands in `p`. -/
  pos : ∀ x, A x → p (f x)
  /-- `B` lands outside `p`. -/
  neg : ∀ x, B x → ¬ p (f x)

/-- `M` halts on its own code with output `[b]`. -/
def SelfOut (b : Bool) (M : EncodableTM Bool) : Prop :=
  M.toSingleTapeTM.Outputs (encodeBoolTM M) [b]

/-- Flip the bit under the head and halt. -/
def flipTM : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ a :=
    match a with
    | some b => (⟨some (!b), none⟩, none)
    | none => (⟨none, none⟩, none)

/-- `flipTM` turns `[true]` into `[false]`. -/
theorem flipTM_true : flipTM.Outputs [true] [false] := Relation.ReflTransGen.single rfl

/-- `flipTM` turns `[false]` into `[true]`. -/
theorem flipTM_false : flipTM.Outputs [false] [true] := Relation.ReflTransGen.single rfl

/-- **The pair `SelfOut true`, `SelfOut false` is computably inseparable.** -/
theorem selfOut_inseparable {S : EncodableTM Bool → Prop}
    (hS : Separates (SelfOut true) (SelfOut false) S) : ¬ MachineDecidable encodeBoolTM S := by
  rintro ⟨D, hD⟩
  let E : EncodableTM Bool := ⟨compComputer D flipTM, Fintype.toEncodable _⟩
  obtain ⟨hpos, hneg⟩ := hD E
  by_cases hE : S E
  · exact hS.2 E (compComputer_seq_outputs (hpos hE) flipTM_true) hE
  · exact hE (hS.1 E (compComputer_seq_outputs (hneg hE) flipTM_false))

/-- `p` is undecidable via the inseparable pair. Like `Undecidable`, the reduction is wrapped in
`Nonempty` to keep this a `Prop`. -/
def InsepUndecidable (p : Y → Prop) : Prop := Nonempty (SepReduces (SelfOut true) (SelfOut false) p)

/-- A separation reduction computed by a Turing machine transfers inseparability: `p` has no
machine decider. -/
theorem not_machineDecidable_of_sepReduces {enc : Y → List Bool} {p : Y → Prop}
    (r : SepReduces (SelfOut true) (SelfOut false) p) {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encodeBoolTM enc r.f) : ¬ MachineDecidable enc p := fun hp =>
  selfOut_inseparable (S := p ∘ r.f) ⟨r.pos, r.neg⟩
    (machineDecidable_of_computes_reduction hR (fun _ => Iff.rfl) hp)

/-- A machine-level undecidability result transfers to any encoding that a machine can compute
from the given one. -/
theorem not_machineDecidable_of_conv {enc enc' : Y → List Bool} {P : Y → Prop}
    (h : ¬ MachineDecidable enc P) {R : SingleTapeTM Bool}
    (hR : ComputesReduction R enc enc' id) : ¬ MachineDecidable enc' P := fun hd =>
  h (machineDecidable_of_computes_reduction hR (fun _ => Iff.rfl) hd)

end DiagonaLean.Foundations.Computability
