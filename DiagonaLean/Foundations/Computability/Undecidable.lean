/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.Foundations.Computability.HaltCanon

@[expose] public section

/-! # Undecidability

`Undecidable P` is `¬ ComputablePred P`, by definition, so every `not_computablePred` result of
the library is an `Undecidable` result as stated. Unfolded, it says that no computable Boolean
function decides `P`: there is no `f : β → Bool` with `Computable f` and `Decider f P`
(`P x ↔ f x = true` for every `x`), which is `undecidable_iff`. Without the condition
`Computable f` the statement would be false for every `P`, since `Classical.propDecidable` gives a
Boolean decider for any predicate (`SDecidable`).

## Main statements

* `Undecidable`: the definition, `¬ ComputablePred P`.
* `undecidable_iff`: no computable function decides `P`.
* `Undecidable.not_machineDecidable`: no machine decides an undecidable predicate, under any
  computable encoding.
* `HaltHard.undecidable`, `HaltReduction.undecidable`: halting-hard predicates are undecidable.

## References

* [Y. Forster, D. Larchey-Wendling, A. Dudenhefner, et al.,
    *A Coq Library of Undecidable Problems*][ForsterEtAl2020]
-/

namespace DiagonaLean.Foundations.Computability

open DiagonaLean.Synthetic.Definitions

variable {β : Type*} [Primcodable β] {P : β → Prop}

/-- **Undecidability**: `P` is not a computable predicate. Unfolded, no computable Boolean
function decides `P` (`undecidable_iff`). An `abbrev`, so every `¬ ComputablePred P` result is an
`Undecidable P` result as stated. -/
abbrev Undecidable (P : β → Prop) : Prop := ¬ ComputablePred P

/-- **Undecidability is the absence of a computable decider.** The condition `Computable f` is
what gives the statement content: a Boolean decider with no such condition exists for every `P`,
classically (`SDecidable`). -/
theorem undecidable_iff : Undecidable P ↔ ¬ ∃ f : β → Bool, Computable f ∧ Decider f P := by
  refine not_congr ⟨fun h => ?_, fun ⟨f, hf, hd⟩ =>
    ComputablePred.computable_iff.2 ⟨f, hf, funext fun x => propext (hd x)⟩⟩
  obtain ⟨f, hf, rfl⟩ := ComputablePred.computable_iff.1 h
  exact ⟨f, hf, fun _ => Iff.rfl⟩

/-- **No machine decides an undecidable predicate**, under any computable encoding. -/
theorem Undecidable.not_machineDecidable (h : Undecidable P) {enc : β → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc P :=
  not_machineDecidable_of_not_computablePred henc h

/-- **Halting-hard predicates are undecidable.** -/
theorem HaltHard.undecidable (h : HaltHard P) : Undecidable P :=
  h.not_computablePred

/-- **The target of a halting reduction is undecidable.** -/
theorem HaltReduction.undecidable (h : HaltReduction P) : Undecidable P :=
  h.not_computablePred

end DiagonaLean.Foundations.Computability
