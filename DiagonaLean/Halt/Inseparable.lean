/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Halt.Undecidable

@[expose] public section

/-! # Computably inseparable sets

`SelfOut b M` holds when `M` halts on its own code with output `[b]`. No Turing machine decides a
set containing `SelfOut true` and disjoint from `SelfOut false` (`selfOut_inseparable`), by a
diagonal argument like the one for the halting problem.

This is a proof technique, not a notion of undecidability: a function `f` that sends `SelfOut true`
into `p` and `SelfOut false` outside it, and that a machine computes, shows that no machine decides
`p` (`not_machineDecidable_of_separation`). Unlike a many-one reduction from `HaltProblem`, it says
nothing about the machines in neither set, so it does not give `SynthHaltReduction p`.

## References

* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.Halt.Inseparable

open Cslib.Turing SingleTapeTM DiagonaLean.Halt.Encoding DiagonaLean.Halt.Compositions
  DiagonaLean.Halt.Undecidable DiagonaLean.Synthetic.Definitions

variable {Y : Type*}

/-- `S` separates `A` from `B`: it contains `A` and is disjoint from `B`. -/
def Separates {X : Type*} (A B S : X → Prop) : Prop := (∀ x, A x → S x) ∧ ∀ x, B x → ¬ S x

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

/-- **The pair `SelfOut true`, `SelfOut false` is computably inseparable**: no machine decides a
set that separates them. -/
theorem selfOut_inseparable {S : EncodableTM Bool → Prop}
    (hS : Separates (SelfOut true) (SelfOut false) S) : ¬ MachineDecidable encodeBoolTM S := by
  rintro ⟨D, hD⟩
  let E : EncodableTM Bool := ⟨compComputer D flipTM, Fintype.toEncodable _⟩
  obtain ⟨hpos, hneg⟩ := hD E
  by_cases hE : S E
  · exact hS.2 E (compComputer_seq_outputs (hpos hE) flipTM_true) hE
  · exact hE (hS.1 E (compComputer_seq_outputs (hneg hE) flipTM_false))

/-- **No machine decides `p`** if a function computed by a machine sends `SelfOut true` into `p` and
`SelfOut false` outside it. -/
theorem not_machineDecidable_of_separation {enc : Y → List Bool} {p : Y → Prop}
    {f : EncodableTM Bool → Y} (pos : ∀ M, SelfOut true M → p (f M))
    (neg : ∀ M, SelfOut false M → ¬ p (f M)) {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encodeBoolTM enc f) : ¬ MachineDecidable enc p := fun hp =>
  selfOut_inseparable (S := p ∘ f) ⟨pos, neg⟩
    (machineDecidable_of_computes_reduction hR (fun _ => Iff.rfl) hp)

/-- A machine-level undecidability result transfers to any encoding that a machine can compute
from the given one. -/
theorem not_machineDecidable_of_conv {enc enc' : Y → List Bool} {P : Y → Prop}
    (h : ¬ MachineDecidable enc P) {R : SingleTapeTM Bool}
    (hR : ComputesReduction R enc enc' id) : ¬ MachineDecidable enc' P := fun hd =>
  h (machineDecidable_of_computes_reduction hR (fun _ => Iff.rfl) hd)

end DiagonaLean.Halt.Inseparable
