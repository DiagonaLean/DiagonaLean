/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga
-/

import DiagonaLean.Synthetic.Undecidability
import DiagonaLean.PCP.Undecidable
import DiagonaLean.PCP.Basic

/-! # The `reduceFromPCP` tactic

Every "target problem `Q` is undecidable by reduction from PCP" proof in this development composes
`pcp_undecidable` with a reduction `R : PCP.DecisionProblem ⪯ₘ Q`, through
`undecidability_from_reducibility`. `R` must be a named definition that Lean compiles (see the
convention on `ManyOneReduces`), so the reduction function and its correctness proof live in the
target's `Reductions/PCP_to_Q.lean`, and the tactic only composes.

## Forms

| Form                              | Effect                                            |
| :-------------------------------- | :------------------------------------------------ |
| `reduceFromPCP via R`             | closes the goal; the alphabet comes from `R`      |
| `reduceFromPCP over_type α via R` | the same, with the alphabet `α` given explicitly  |

With `over_type`, the `DecidableEq α` and `Nontrivial α` instances that `pcp_undecidable` needs are
found by `infer_instance`, with a targeted error on failure.
-/

open DiagonaLean.PCP DiagonaLean.Synthetic.Notation DiagonaLean.PCP.Reduction

/-- Syntax for the `reduceFromPCP` tactic. See the module docstring for the two forms. -/
syntax "reduceFromPCP" ("over_type" term)? "via" term : tactic

macro_rules
  | `(tactic| reduceFromPCP via $r) =>
    `(tactic|
        exact DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          DiagonaLean.PCP.Reduction.pcp_undecidable $r)
  | `(tactic| reduceFromPCP over_type $alpha via $r) =>
    `(tactic|
        (refine DiagonaLean.Synthetic.Notation.undecidability_from_reducibility
          (@DiagonaLean.PCP.Reduction.pcp_undecidable $alpha ?instDecEq ?instNontrivial) $r
         case instDecEq =>
           first
           | infer_instance
           | fail "reduceFromPCP: could not find a `DecidableEq` instance for the alphabet type. Check that it has/derives `DecidableEq`, or add one as a local assumption before calling `reduceFromPCP`."
         case instNontrivial =>
           first
           | infer_instance
           | fail "reduceFromPCP: could not find a `Nontrivial` instance for the alphabet type. Check that it has/derives `Nontrivial`, or add one as a local assumption before calling `reduceFromPCP`."))
