/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Reductions proved computable

A `ComputableReduction p q` is a many-one reduction whose function is proved `Computable`: the
kernel checks its guarantee, unlike a synthetic reduction (`SynthReduction`, `p ⪯ₘ q`), whose only
guarantee is that its function is compiled code (`#check_reductions`).

It is a separate structure, not an extension of `SynthReduction`. Extending would make every
proved reduction a synthetic one inside it, which `#check_reductions` rejects (a constructor that
stores a reduction, and a proposition that one exists), and would force every proved reduction to
be compiled code, which a kernel-checked reduction does not need. The two connect through
`ComputableReduction.ofSynth`, which upgrades a synthetic reduction given a proof that its function
is computable, and `ComputableReduction.toSynth`, which forgets the proof.

Since the computability is proved, the existence of a proved reduction has content, and
`ComputableReduction.manyOneReducible` gives Mathlib's `ManyOneReducible`.

## Main definitions

* `ComputableReduction`: a function, a proof that it is computable, and its correctness.
* `ComputableReduction.ofSynth`, `ComputableReduction.toSynth`: between the two layers.
* `ComputableReduction.refl`, `ComputableReduction.trans`: identity and composition.
* `ComputableReduction.not_computablePred`, `ComputableReduction.not_machineDecidable`:
  undecidability transfers along a proved reduction.
-/

namespace DiagonaLean.Foundations.Computability

open DiagonaLean.Synthetic.Definitions

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

/-- **A many-one reduction proved computable.** -/
structure ComputableReduction (p : α → Prop) (q : β → Prop) where
  /-- The reduction function. -/
  f : α → β
  /-- Its computability, checked by the kernel. -/
  computable : Computable f
  /-- Its correctness: `p x ↔ q (f x)` for every `x`. -/
  hf : p ⪯ₘ[f] q

namespace ComputableReduction

variable {p : α → Prop} {q : β → Prop} {r : γ → Prop}

/-- Upgrade a synthetic reduction, given a proof that its function is computable. -/
def ofSynth (s : p ⪯ₘ q) (h : Computable s.f) : ComputableReduction p q :=
  ⟨s.f, h, s.hf⟩

/-- Forget the proof of computability: a proved reduction is a synthetic one. -/
def toSynth (c : ComputableReduction p q) : p ⪯ₘ q :=
  ⟨c.f, c.hf⟩

/-- The identity reduction. -/
def refl (p : α → Prop) : ComputableReduction p p :=
  ⟨id, Computable.id, fun _ => Iff.rfl⟩

/-- Proved reductions compose. -/
def trans (c₁ : ComputableReduction p q) (c₂ : ComputableReduction q r) :
    ComputableReduction p r :=
  ⟨c₂.f ∘ c₁.f, c₂.computable.comp c₁.computable, fun x => (c₁.hf x).trans (c₂.hf (c₁.f x))⟩

/-- A proved reduction gives Mathlib's many-one reducibility. -/
theorem manyOneReducible (c : ComputableReduction p q) : ManyOneReducible p q :=
  ⟨c.f, c.computable, c.hf⟩

/-- `ofSynth` keeps the function. -/
@[simp] theorem ofSynth_f (s : p ⪯ₘ q) (h : Computable s.f) : (ofSynth s h).f = s.f := rfl

/-- `toSynth` keeps the function. -/
@[simp] theorem toSynth_f (c : ComputableReduction p q) : c.toSynth.f = c.f := rfl

/-- **Undecidability transfers along a proved reduction.** -/
theorem not_computablePred (c : ComputableReduction p q) (hp : ¬ ComputablePred p) :
    ¬ ComputablePred q :=
  fun hq => hp (ComputablePred.computable_of_manyOneReducible c.manyOneReducible hq)

/-- **No machine decides the target of a proved reduction from an undecidable predicate**, under
any computable encoding. -/
theorem not_machineDecidable (c : ComputableReduction p q) (hp : ¬ ComputablePred p)
    {enc : β → List Bool} (henc : Computable enc) : ¬ MachineDecidable enc q :=
  not_machineDecidable_of_not_computablePred henc (c.not_computablePred hp)

end ComputableReduction

end DiagonaLean.Foundations.Computability
