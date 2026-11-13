/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.Halt.Basic
import DiagonaLean.Synthetic.Definitions
import DiagonaLean.Synthetic.ReductionChain

/-! # Core undecidability definitions

## References

* [Y. Forster, D. Larchey-Wendling, A. Dudenhefner, et al.,
    *A Coq Library of Undecidable Problems*][ForsterEtAl2020]
-/


namespace DiagonaLean.Synthetic.Notation
open DiagonaLean.Halt DiagonaLean.Halt.Encoding Cslib.Turing DiagonaLean.Synthetic.Definitions

variable {X Y : Type*}

/-- `p` is undecidable: `HaltProblem` many-one reduces to `p`. `HaltProblem ⪯ₘ p` is data (see
`ManyOneReduces`), so it is wrapped in `Nonempty` to keep `Undecidable` a `Prop`.

As a statement this is weak: Lean's logic is classical, so `HaltProblem ⪯ₘ p` holds for every `p`
with a positive and a negative instance, through the case split `if HaltProblem x then a else b`.
The meaning comes from the convention on `ManyOneReduces`, which `#check_reductions`
(`Synthetic/ReductionCheck.lean`) checks in CI: every reduction behind an `Undecidable` theorem is a
compiled definition. The statement that a Turing machine computes the reduction is
`not_machineDecidable_of_halt_reduces`. -/
def Undecidable (p : X → Prop) : Prop := Nonempty (HaltProblem ⪯ₘ p)

/-- Undecidability propagates upward along many-one reductions. -/
lemma undecidability_from_reducibility {p : X → Prop} {q : Y → Prop}
    (hp : Undecidable p) (hpq : p ⪯ₘ q) : Undecidable q := by
  obtain ⟨r⟩ := hp
  exact ⟨ReductionChain.ReducesTransitive r hpq⟩

/-- Tactic to prove undecidability by reduction from another undecidable problem.
Translates `undec from H` to `apply undecidability_from_reducibility H`. -/
macro "undec" "from" H:term : tactic =>
  `(tactic| apply undecidability_from_reducibility $H)

end DiagonaLean.Synthetic.Notation
