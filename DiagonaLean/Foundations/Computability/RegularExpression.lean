/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.Computability.DerivePrimcodable
import Mathlib.Computability.RegularExpressions

@[expose] public section

/-! # Regular expressions are `Primcodable`

Mathlib's regular expressions over a `Primcodable` alphabet are `Primcodable`, with primitive
recursive constructors (`derive_primcodable RegularExpression`). Sums and products written with
`+` and `*`, and the constants `0` and `1`, are primitive recursive too (`prim_reAdd`,
`prim_reMul`, `prim_reZero`, `prim_reOne`), so `fun_prop` proves a function built from them
primitive recursive.

## Main statements

* `prim_reAdd`, `prim_reMul`, `prim_reZero`, `prim_reOne`: the operations, for `fun_prop`.
-/

derive_primcodable RegularExpression

namespace DiagonaLean.Foundations.Computability

variable {α β : Type} [Primcodable α] [Primcodable β]

/-- The sum of two expressions is primitive recursive in them. -/
@[fun_prop] theorem prim_reAdd {f g : β → RegularExpression α} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x + g x := by
  change Primrec fun x => (f x).plus (g x)
  fun_prop

/-- The product of two expressions is primitive recursive in them. -/
@[fun_prop] theorem prim_reMul {f g : β → RegularExpression α} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x * g x := by
  change Primrec fun x => (f x).comp (g x)
  fun_prop

/-- The empty expression is a primitive recursive constant. -/
@[fun_prop] theorem prim_reZero : Primrec fun _ : β => (0 : RegularExpression α) := Primrec.const _

/-- The expression of the empty word is a primitive recursive constant. -/
@[fun_prop] theorem prim_reOne : Primrec fun _ : β => (1 : RegularExpression α) := Primrec.const _

end DiagonaLean.Foundations.Computability
