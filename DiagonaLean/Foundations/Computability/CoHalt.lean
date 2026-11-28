/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.Computability.HaltComplete
import DiagonaLean.Foundations.Computability.ListHaltRE

@[expose] public section

/-! # Co-halting-hardness

A predicate is co-halting-hard (`CoHaltHard p`) when its complement is halting-hard, that is, when
the complement of the halting problem on canonical machines many-one reduces to it, computably
(`coHaltHard_iff`). The halting problem is recursively enumerable (`haltCanon_rePred`, through
`ListHalt`), and not computable, so its complement is not recursively enumerable
(`not_rePred_compl_haltCanon`). A co-halting-hard predicate is therefore not computable, not
decided by any machine under a computable encoding, and not recursively enumerable
(`CoHaltHard.not_computablePred`, `CoHaltHard.not_machineDecidable`, `CoHaltHard.not_rePred`).
Every predicate whose complement is recursively enumerable reduces to every co-halting-hard
predicate (`ManyOneReducible.of_coRE_of_coHaltHard`), so co-halting-hard predicates with a
recursively enumerable complement are many-one equivalent
(`manyOneEquiv_of_coHaltHard_of_coRE`).

## Main definitions

* `CoHaltHard`: the complement of the halting problem reduces to the predicate.

## Main statements

* `haltCanon_rePred`, `not_rePred_compl_haltCanon`: the halting problem is recursively
  enumerable and its complement is not.
* `CoHaltHard.not_computablePred`, `CoHaltHard.not_machineDecidable`, `CoHaltHard.not_rePred`.
* `ManyOneReducible.of_coRE_of_coHaltHard`, `manyOneEquiv_of_coHaltHard_of_coRE`: the co-r.e.
  degree.

## References

* H. Rogers, *Theory of Recursive Functions and Effective Computability* (1967), Section 7.2
-/

namespace DiagonaLean.Foundations.Computability

open DiagonaLean.Synthetic.Definitions

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- Many-one reducibility between complements is many-one reducibility, by the same function. -/
theorem manyOneReducible_compl_iff {p : α → Prop} {q : β → Prop} :
    ManyOneReducible (fun a => ¬ p a) (fun b => ¬ q b) ↔ ManyOneReducible p q :=
  ⟨fun ⟨f, hf, h⟩ => ⟨f, hf, fun a => not_not.symm.trans ((not_congr (h a)).trans not_not)⟩,
    fun ⟨f, hf, h⟩ => ⟨f, hf, fun a => not_congr (h a)⟩⟩

/-- **Co-halting-hardness**: the complement of the predicate is halting-hard. -/
def CoHaltHard (p : β → Prop) : Prop := HaltHard fun b => ¬ p b

/-- A predicate is co-halting-hard iff the complement of `HaltCanon` many-one reduces to it. -/
theorem coHaltHard_iff {p : β → Prop} :
    CoHaltHard p ↔ ManyOneReducible (fun x => ¬ HaltCanon x) p := by
  rw [CoHaltHard, haltHard_iff, ← manyOneReducible_compl_iff]
  simp only [not_not]

/-- **The halting problem on canonical machines is recursively enumerable**: `canonList` reduces
it to halting of list machines, which is (`ListHalt.rePred`). -/
theorem haltCanon_rePred : REPred HaltCanon :=
  REPred.of_manyOneReducible ⟨ListHalt.canonList, ListHalt.canonList_prim.to_comp,
    ListHalt.haltCanon_iff_listHalt⟩ (ListHalt.rePred none)

/-- **The complement of the halting problem is not recursively enumerable.** -/
theorem not_rePred_compl_haltCanon : ¬ REPred fun x => ¬ HaltCanon x := fun h =>
  not_computablePred_haltCanon (ComputablePred.computable_iff_re_compl_re'.2 ⟨haltCanon_rePred, h⟩)

/-- **Co-halting-hard predicates are not computable.** -/
theorem CoHaltHard.not_computablePred {p : β → Prop} (h : CoHaltHard p) : ¬ ComputablePred p :=
  fun hp => HaltHard.not_computablePred h hp.not

/-- **No machine decides a co-halting-hard predicate**, under any computable encoding. -/
theorem CoHaltHard.not_machineDecidable {p : β → Prop} (h : CoHaltHard p) {enc : β → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc p :=
  not_machineDecidable_of_not_computablePred henc h.not_computablePred

/-- **Co-halting-hard predicates are not recursively enumerable.** -/
theorem CoHaltHard.not_rePred {p : β → Prop} (h : CoHaltHard p) : ¬ REPred p := fun hp =>
  not_rePred_compl_haltCanon (REPred.of_manyOneReducible (coHaltHard_iff.1 h) hp)

/-- **A predicate with a recursively enumerable complement reduces to every co-halting-hard
predicate**: complements of `ManyOneReducible.of_rePred_of_haltHard`. -/
theorem _root_.ManyOneReducible.of_coRE_of_coHaltHard {p : α → Prop} {q : β → Prop}
    (hp : REPred fun a => ¬ p a) (hq : CoHaltHard q) : ManyOneReducible p q :=
  manyOneReducible_compl_iff.1 (.of_rePred_of_haltHard hp hq)

/-- **Co-halting-hard predicates with a recursively enumerable complement are many-one
equivalent**: both have the degree of the complement of the halting problem. -/
theorem manyOneEquiv_of_coHaltHard_of_coRE {p : α → Prop} {q : β → Prop} (hp : CoHaltHard p)
    (hp' : REPred fun a => ¬ p a) (hq : CoHaltHard q) (hq' : REPred fun b => ¬ q b) :
    ManyOneEquiv p q :=
  ⟨.of_coRE_of_coHaltHard hp' hq, .of_coRE_of_coHaltHard hq' hp⟩

/-- **The complement of a halting-hard predicate is co-halting-hard.** -/
theorem HaltHard.coHaltHard_compl {p : β → Prop} (h : HaltHard p) : CoHaltHard fun b => ¬ p b := by
  simpa only [CoHaltHard, not_not] using h

end DiagonaLean.Foundations.Computability
