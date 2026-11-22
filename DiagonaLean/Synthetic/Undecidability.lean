/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.Halt.Basic
import DiagonaLean.Synthetic.Definitions
import DiagonaLean.Synthetic.ReductionChain

@[expose] public section

/-! # Core undecidability definitions

`SynthHaltReduction p` is a synthetic many-one reduction from `HaltProblem` to `p`, kept as data.
It composes with further synthetic reductions (`SynthHaltReduction.comp`). `Undecidable` and
`undecidabilityFromReducibility` are their former names, kept as aliases until existing uses are
renamed. The name `Undecidable` undersold the notion: a reduction from the halting problem is
halting-hardness, which is stronger than undecidability.

## References

* [Y. Forster, D. Larchey-Wendling, A. Dudenhefner, et al.,
    *A Coq Library of Undecidable Problems*][ForsterEtAl2020]
-/

namespace DiagonaLean.Synthetic.Notation
open DiagonaLean.Halt DiagonaLean.Halt.Encoding Cslib.Turing DiagonaLean.Synthetic.Definitions

variable {X Y : Type*}

/-- **A synthetic reduction from the halting problem** to `p`. This is data, not a `Prop`: such a
result is a definition whose value is the reduction, and composing results composes their functions
(`SynthHaltReduction.comp`).

Lean's logic is classical, so the bare existence of a term of this type would say nothing: the case
split `if HaltProblem x then a else b` reduces `HaltProblem` to every `p` with a positive and a
negative instance. That case split is not a program, and Lean refuses to compile it. So an
undecidability result means something because it is a definition that Lean compiles, with no escape
hatch in its dependencies; `#check_reductions` (`Synthetic/ReductionCheck.lean`) checks this in CI.
The statement that a Turing machine computes the reduction is
`not_machineDecidable_of_halt_reduces`. -/
abbrev SynthHaltReduction (p : X → Prop) : Type _ := HaltProblem ⪯_s p

/-- The former name of `SynthHaltReduction`, kept as an alias until existing uses are renamed. -/
abbrev Undecidable := @SynthHaltReduction

/-- A synthetic halting reduction composes with a further synthetic reduction: the reduction from
`HaltProblem` to `q` is the composition of the two functions. -/
def SynthHaltReduction.comp {p : X → Prop} {q : Y → Prop}
    (hp : SynthHaltReduction p) (hpq : p ⪯_s q) : SynthHaltReduction q :=
  SynthReduction.trans hp hpq

/-- The former name of `SynthHaltReduction.comp`. -/
abbrev undecidabilityFromReducibility := @SynthHaltReduction.comp

/-- `undec from H` reduces a goal `Undecidable q` to a reduction `p ⪯_s q`, given
`H : Undecidable p`; it applies `undecidabilityFromReducibility H`. -/
macro "undec" "from" H:term : tactic =>
  `(tactic| apply undecidabilityFromReducibility $H)

end DiagonaLean.Synthetic.Notation
