/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga
-/

import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.PCP.Undecidable
import DiagonaLean.PCP.Basic

@[expose] public section

/-! # The `reduceFromPCP` tactic

Every "target problem `Q` is undecidable by reduction from PCP" result in this development composes
`undecidablePCP` with a reduction `R : PCP.DecisionProblem ⪯ₘ Q`, through
`undecidabilityFromReducibility`. `R` must be a named definition that Lean compiles (see the
convention on `ManyOneReduces`), so the reduction function and its correctness proof live in the
target's `Reductions/PCP_to_Q.lean`, and the tactic only composes. The result is a definition, so
the tactic is used in `def … := by reduceFromPCP …`.

## Form

`reduceFromPCP over_letters b0 b1 via R` closes the goal with
`undecidabilityFromReducibility (undecidablePCP b0 b1 _) R`. The alphabet is the type of `b0`
and `b1`. The proof of `b0 ≠ b1` is found by `assumption` or `decide`, with a targeted error on
failure.

The letters are given explicitly, rather than taken from a `Nontrivial` instance, because a
definition cannot extract data from a proof.
-/

open DiagonaLean.PCP DiagonaLean.Synthetic.Notation DiagonaLean.PCP.Reduction

/-- Syntax for the `reduceFromPCP` tactic. See the module docstring. -/
syntax "reduceFromPCP" "over_letters" term:max term:max "via" term : tactic

macro_rules
  | `(tactic| reduceFromPCP over_letters $b0 $b1 via $r) =>
    `(tactic|
        (refine DiagonaLean.Synthetic.Notation.undecidabilityFromReducibility
          (DiagonaLean.PCP.Reduction.undecidablePCP $b0 $b1 ?hne) $r
         case hne =>
           first
           | assumption
           | decide
           | fail "reduceFromPCP: could not prove that the two letters are distinct. \
               Add a hypothesis `h : b0 ≠ b1` before calling `reduceFromPCP`."))
