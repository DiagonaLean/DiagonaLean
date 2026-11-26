/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga
-/

import DiagonaLean.Synthetic.HaltReduction
import DiagonaLean.PCP.Undecidable
import DiagonaLean.PCP.Basic
import DiagonaLean.Foundations.Computability.ReduceFrom

@[expose] public section

/-! # The `reduce_from_pcp` tactic

Every "target problem `Q` is undecidable by reduction from PCP" result in this development composes
`PCP.synthFromHaltOver` with a reduction `R : PCP.DecisionProblem ⪯_s Q`, through
`SynthHaltReduction.comp`. `R` must be a named definition that Lean compiles (see the
convention on `SynthReduction`), so the reduction function and its correctness proof live in the
target's `Reductions/PCP_to_Q.lean`, and the tactic only composes. The result is a definition, so
the tactic is used in `def … := by reduce_from_pcp …`.

## Form

`reduce_from_pcp over_letters b0 b1 via R` is `reduce_from (PCP.synthFromHaltOver b0 b1 _) via R`
(`Foundations/Computability/ReduceFrom.lean`), kept until the older call sites move. The alphabet is
the type of `b0` and `b1`. The proof of `b0 ≠ b1` is found by `assumption` or `decide`, with a
targeted error on failure.

The letters are given explicitly, rather than taken from a `Nontrivial` instance, because a
definition cannot extract data from a proof.

`reduceFromPCP` is the earlier name of the tactic, kept as an alias.
-/

open DiagonaLean.PCP DiagonaLean.Synthetic.Definitions DiagonaLean.PCP.Reduction

/-- Syntax for the `reduce_from_pcp` tactic. See the module docstring. -/
syntax "reduce_from_pcp" "over_letters" term:max term:max "via" term : tactic

/-- The earlier name of `reduce_from_pcp`, kept as an alias. -/
syntax "reduceFromPCP" "over_letters" term:max term:max "via" term : tactic

macro_rules
  | `(tactic| reduceFromPCP over_letters $b0 $b1 via $r) =>
    `(tactic| reduce_from_pcp over_letters $b0 $b1 via $r)

macro_rules
  | `(tactic| reduce_from_pcp over_letters $b0 $b1 via $r) =>
    `(tactic|
        reduce_from (DiagonaLean.PCP.synthFromHaltOver $b0 $b1 (by
          first
          | assumption
          | decide
          | fail "reduce_from_pcp: could not prove that the two letters are distinct. \
              Add a hypothesis `h : b0 ≠ b1` before calling `reduce_from_pcp`.")) via $r)
