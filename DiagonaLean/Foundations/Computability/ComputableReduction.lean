/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Reductions proved computable

A `ComputableReduction p q` (notation `p ⪯ q`) is a many-one reduction whose function is proved
`Computable`: the kernel checks its guarantee, unlike a synthetic reduction (`SynthReduction`,
`p ⪯_s q`), whose only guarantee is that its function is compiled code (`#check_reductions`).

## Notation

The plain symbol is the proved notion; `_s` marks that no proof of computability is attached.

| notation | meaning |
|---|---|
| `p ⪯[f] q` | `ComputablyReducesVia f p q`: `f` is computable and `p x ↔ q (f x)` for every `x` |
| `p ⪯_s[f] q` | `ReducesVia f p q`: `p x ↔ q (f x)` for every `x`, nothing said about `f` |
| `p ⪯ q` | `ComputableReduction p q`: a function with `p ⪯[f] q`, as data |
| `p ⪯_s q` | `SynthReduction p q`: a function with `p ⪯_s[f] q`, as data |

A claim `∃ f, p ⪯[f] q` has content: it is Mathlib's `ManyOneReducible p q`
(`manyOneReducible_iff_exists`). A claim `∃ f, p ⪯_s[f] q` holds classically for almost any `p` and
`q`, which `#check_reductions` rejects.

It is a separate structure, not an extension of `SynthReduction`. Extending would make every
proved reduction a synthetic one inside it, which `#check_reductions` rejects (a constructor that
stores a reduction, and a proposition that one exists), and would force every proved reduction to
be compiled code, which a kernel-checked reduction does not need. The two connect through
`ComputableReduction.ofSynth`, which upgrades a synthetic reduction given a proof that its function
is computable, and `ComputableReduction.toSynth`, which forgets the proof.

Since the computability is proved, the existence of a proved reduction has content, and
`ComputableReduction.manyOneReducible` gives Mathlib's `ManyOneReducible`.

## Main definitions

* `ComputablyReducesVia` (`p ⪯[f] q`): a given function is a computable reduction.
* `ComputableReduction` (`p ⪯ q`): a function, a proof that it is computable, and its correctness.
* `ComputableReduction.ofSynth`, `ComputableReduction.toSynth`: between the two layers.
* `ComputableReduction.refl`, `ComputableReduction.trans`: identity and composition.
* `ComputableReduction.not_computablePred`, `ComputableReduction.not_machineDecidable`:
  undecidability transfers along a proved reduction.
-/

namespace DiagonaLean.Foundations.Computability

open DiagonaLean.Synthetic.Definitions

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

/-- **`f` is a computable many-one reduction from `p` to `q`**: `f` is computable and
`p x ↔ q (f x)` for every `x`. Unlike `p ⪯_s[f] q`, its existential has content
(`manyOneReducible_iff_exists`). -/
def ComputablyReducesVia (f : α → β) (p : α → Prop) (q : β → Prop) : Prop :=
  Computable f ∧ p ⪯_s[f] q

@[inherit_doc] notation:50 p " ⪯[" f "] " q => ComputablyReducesVia f p q

/-- Mathlib's many-one reducibility is the existence of a computable reduction. -/
theorem manyOneReducible_iff_exists {p : α → Prop} {q : β → Prop} :
    ManyOneReducible p q ↔ ∃ f, p ⪯[f] q :=
  ⟨fun ⟨f, hf, h⟩ => ⟨f, hf, h⟩, fun ⟨f, hf, h⟩ => ⟨f, hf, h⟩⟩

/-- **A many-one reduction proved computable.** -/
structure ComputableReduction (p : α → Prop) (q : β → Prop) where
  /-- The reduction function. -/
  f : α → β
  /-- Its computability, checked by the kernel. -/
  computable : Computable f
  /-- Its correctness: `p x ↔ q (f x)` for every `x`. -/
  hf : p ⪯_s[f] q

@[inherit_doc] notation:50 p " ⪯ " q => ComputableReduction p q

namespace ComputableReduction

variable {p : α → Prop} {q : β → Prop} {r : γ → Prop}

/-- The function of a proved reduction is a computable reduction. -/
theorem red (c : p ⪯ q) : p ⪯[c.f] q := ⟨c.computable, c.hf⟩

/-- A proved reduction from a computable reduction. -/
def ofRed {f : α → β} (h : p ⪯[f] q) : p ⪯ q := ⟨f, h.1, h.2⟩

/-- Upgrade a synthetic reduction, given a proof that its function is computable. -/
def ofSynth (s : p ⪯_s q) (h : Computable s.f) : p ⪯ q :=
  ⟨s.f, h, s.hf⟩

/-- Forget the proof of computability: a proved reduction is a synthetic one. -/
def toSynth (c : p ⪯ q) : p ⪯_s q :=
  ⟨c.f, c.hf⟩

/-- The identity reduction. -/
def refl (p : α → Prop) : p ⪯ p :=
  ⟨id, Computable.id, fun _ => Iff.rfl⟩

/-- Proved reductions compose. -/
def trans (c₁ : p ⪯ q) (c₂ : q ⪯ r) : p ⪯ r :=
  ⟨c₂.f ∘ c₁.f, c₂.computable.comp c₁.computable, fun x => (c₁.hf x).trans (c₂.hf (c₁.f x))⟩

/-- A proved reduction gives Mathlib's many-one reducibility. -/
theorem manyOneReducible (c : p ⪯ q) : ManyOneReducible p q :=
  ⟨c.f, c.computable, c.hf⟩

/-- `ofSynth` keeps the function. -/
@[simp] theorem ofSynth_f (s : p ⪯_s q) (h : Computable s.f) : (ofSynth s h).f = s.f := rfl

/-- `toSynth` keeps the function. -/
@[simp] theorem toSynth_f (c : p ⪯ q) : c.toSynth.f = c.f := rfl

/-- **Not being a computable predicate transfers along a proved reduction.** -/
theorem not_computablePred (c : p ⪯ q) (hp : ¬ ComputablePred p) :
    ¬ ComputablePred q :=
  fun hq => hp (ComputablePred.computable_of_manyOneReducible c.manyOneReducible hq)

/-- **No machine decides the target of a proved reduction from a predicate that is not
computable**, under any computable encoding. -/
theorem not_machineDecidable (c : p ⪯ q) (hp : ¬ ComputablePred p)
    {enc : β → List Bool} (henc : Computable enc) : ¬ MachineDecidable enc q :=
  not_machineDecidable_of_not_computablePred henc (c.not_computablePred hp)

end ComputableReduction

end DiagonaLean.Foundations.Computability
