/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean

/-! # Checking the declarations tagged for `undec from`

Every `@[undecReduction]` declaration must be a closed reduction definition `P ⪯_s Q`, and every
`@[undecHardness]` theorem must state `¬ ComputablePred P` after its parameters. The tactics skip a
declaration that is not, so this script fails CI instead. Run it with
`lake env lean scripts/CheckUndecTags.lean`.
-/

open Lean Meta in
run_meta do
  let bad ← DiagonaLean.Foundations.Computability.undecTagProblems
  unless bad.isEmpty do
    throwError m!"ill-formed undec tags:\n{MessageData.joinSep bad.toList "\n"}"
