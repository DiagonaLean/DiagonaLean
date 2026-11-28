/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Rewriting.SRS
import DiagonaLean.Foundations.Computability.DerivePrimcodable
import DiagonaLean.Foundations.Computability.DerivePrimrec

@[expose] public section

/-! # Rewriting systems are `Primcodable`

`derive_primcodable` makes `Rule T` `Primcodable` for any `Primcodable T`, so a system
`SRS T = List (Rule T)` is too, and registers the `fun_prop` lemmas of the constructor
(`Rule.prim_mk`) and of the projections (`Rule.prim_lhs`, `Rule.prim_rhs`), with which `fun_prop`
proves that functions building or reading systems are primitive recursive.

## Main statements

* `instance : Primcodable (Rule T)`; `Rule.toPair_prim`.
-/

derive_primcodable DiagonaLean.Foundations.Rewriting.Rule

namespace DiagonaLean.Foundations.Rewriting

/- `Rule.toPair_prim`: a rule as a pair is primitive recursive. -/
derive_primrec Rule.toPair [Primcodable T]

end DiagonaLean.Foundations.Rewriting
