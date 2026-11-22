/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.Halt.Basic
import DiagonaLean.Synthetic.Definitions

@[expose] public section

/-! # Preorder properties of many-one reductions

Synthetic many-one reducibility is reflexive (`SynthReduction.refl`) and transitive
(`SynthReduction.trans`), and a reduction from `P` to `Q` is also a reduction from the complement
of `P` to the complement of `Q` (`SynthReduction.compl`). `reducesRefl`, `reducesTrans` and
`reducesCompl` are their former names, kept as aliases until existing uses are renamed. Each
reduction is a `def` built from a spec theorem (`reduces_reflexive_spec`,
`reduces_transitive_spec`, `reduces_complement_spec`).

## References

* [Y. Forster, D. Larchey-Wendling, A. Dudenhefner, et al.,
    *A Coq Library of Undecidable Problems*][ForsterEtAl2020]
-/

namespace DiagonaLean.Synthetic.ReductionChain
open DiagonaLean.Halt Cslib.Turing DiagonaLean.Synthetic.Definitions

variable {X Y Z : Type*}

/-- `id` witnesses that many-one reducibility is reflexive. -/
theorem reduces_reflexive_spec (P : X → Prop) : P ⪯ₘ[id] P :=
  fun _ => Iff.rfl

/-- Many-one reducibility is reflexive. `⪯ₘ` is data (see `SynthReduction`), so building one is
a `def`, not a `theorem`. -/
def _root_.DiagonaLean.Synthetic.Definitions.SynthReduction.refl (P : X → Prop) : P ⪯ₘ P :=
  ⟨id, reduces_reflexive_spec P⟩

/-- The former name of `SynthReduction.refl`. -/
abbrev reducesRefl := @SynthReduction.refl

/-- The composition `hQR.f ∘ hPQ.f` of the two witness functions witnesses that many-one
reducibility is transitive. -/
theorem reduces_transitive_spec {P : X → Prop} {Q : Y → Prop} {R : Z → Prop}
    (hPQ : P ⪯ₘ Q) (hQR : Q ⪯ₘ R) : P ⪯ₘ[hQR.f ∘ hPQ.f] R :=
  fun x => (hPQ.hf x).trans (hQR.hf (hPQ.f x))

/-- Many-one reducibility is transitive: compose the two witness functions. -/
def _root_.DiagonaLean.Synthetic.Definitions.SynthReduction.trans {P : X → Prop} {Q : Y → Prop}
    {R : Z → Prop} (hPQ : P ⪯ₘ Q) (hQR : Q ⪯ₘ R) : P ⪯ₘ R :=
  ⟨hQR.f ∘ hPQ.f, reduces_transitive_spec hPQ hQR⟩

/-- The former name of `SynthReduction.trans`. -/
abbrev reducesTrans := @SynthReduction.trans

/-- The witness function `h.f` of `P ⪯ₘ Q` also witnesses that the complement of `P` reduces to
the complement of `Q`. -/
theorem reduces_complement_spec {P : X → Prop} {Q : Y → Prop}
    (h : P ⪯ₘ Q) : Complement P ⪯ₘ[h.f] Complement Q :=
  fun x => not_congr (h.hf x)

/-- If `P` reduces to `Q`, then the complement of `P` reduces to the complement of `Q`. -/
def _root_.DiagonaLean.Synthetic.Definitions.SynthReduction.compl {P : X → Prop} {Q : Y → Prop}
    (h : P ⪯ₘ Q) : Complement P ⪯ₘ Complement Q :=
  ⟨h.f, reduces_complement_spec h⟩

/-- The former name of `SynthReduction.compl`. -/
abbrev reducesCompl := @SynthReduction.compl

/-- `reduce_chain H` proves a reduction by applying transitivity with `H` and closing with
reflexivity, as often as needed. -/
macro "reduce_chain" H:term : tactic =>
  `(tactic| repeat (first | exact reducesRefl _ | apply reducesTrans $H))

end DiagonaLean.Synthetic.ReductionChain
