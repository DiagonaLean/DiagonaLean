/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.Halt.Basic
import DiagonaLean.Synthetic.Definitions
import DiagonaLean.Synthetic.ReductionChain

@[expose] public section

/-! # Core undecidability definitions

`Undecidable p` is a many-one reduction from `HaltProblem` to `p`, kept as data. Undecidability
propagates along many-one reductions (`undecidabilityFromReducibility`).

## References

* [Y. Forster, D. Larchey-Wendling, A. Dudenhefner, et al.,
    *A Coq Library of Undecidable Problems*][ForsterEtAl2020]
-/

namespace DiagonaLean.Synthetic.Notation
open DiagonaLean.Halt DiagonaLean.Halt.Encoding Cslib.Turing DiagonaLean.Synthetic.Definitions

variable {X Y : Type*}

/-- `p` is undecidable: a many-one reduction from `HaltProblem` to `p`. This is data, not a `Prop`:
an undecidability result is a definition whose value is the reduction, and composing results
composes their functions (`undecidabilityFromReducibility`).

Lean's logic is classical, so the bare existence of a term of this type would say nothing: the case
split `if HaltProblem x then a else b` reduces `HaltProblem` to every `p` with a positive and a
negative instance. That case split is not a program, and Lean refuses to compile it. So an
undecidability result means something because it is a definition that Lean compiles, with no escape
hatch in its dependencies; `#check_reductions` (`Synthetic/ReductionCheck.lean`) checks this in CI.
The statement that a Turing machine computes the reduction is
`not_machineDecidable_of_halt_reduces`. -/
abbrev Undecidable (p : X → Prop) : Type _ := HaltProblem ⪯ₘ p

/-- Undecidability propagates upward along many-one reductions: the reduction from `HaltProblem`
to `q` is the composition of the two functions. -/
def undecidabilityFromReducibility {p : X → Prop} {q : Y → Prop}
    (hp : Undecidable p) (hpq : p ⪯ₘ q) : Undecidable q :=
  ReductionChain.reducesTrans hp hpq

end DiagonaLean.Synthetic.Notation
