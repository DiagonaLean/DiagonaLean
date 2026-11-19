/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import Mathlib.Computability.PartrecBasis

@[expose] public section

/-! # A tactic for `Primrec` goals

`prim` proves `Primrec` and `PrimrecPred` goals built from pairs, projections, arithmetic, list
operations and `if`. Later files add rules for their own definitions, with
`macro_rules | \`(tactic| prim_step) => ...`.
-/

namespace DiagonaLean.Foundations.Computability

section Prim

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

/-- The identity function is primitive recursive. -/
theorem prim_self : Primrec fun x : α => x := Primrec.id

/-- The pairing `fun x => (f x, g x)` of two primitive recursive functions is primitive
recursive. -/
theorem prim_pair {f : α → β} {g : α → γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => (f x, g x) := hf.pair hg

/-- The first projection of a primitive recursive function is primitive recursive. -/
theorem prim_fst {f : α → β × γ} (hf : Primrec f) : Primrec fun x => (f x).1 := Primrec.fst.comp hf

/-- The second projection of a primitive recursive function is primitive recursive. -/
theorem prim_snd {f : α → β × γ} (hf : Primrec f) : Primrec fun x => (f x).2 := Primrec.snd.comp hf

/-- `Nat.pair` of two primitive recursive functions is primitive recursive. -/
theorem prim_natPair {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => Nat.pair (f x) (g x) := Primrec₂.natPair.comp hf hg

/-- `Nat.unpair` of a primitive recursive function is primitive recursive. -/
theorem prim_unpair {f : α → ℕ} (hf : Primrec f) : Primrec fun x => (f x).unpair :=
  Primrec.unpair.comp hf

/-- Consing the values of two primitive recursive functions is primitive recursive. -/
theorem prim_cons {f : α → β} {g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x :: g x := Primrec.list_cons.comp hf hg

/-- Appending the values of two primitive recursive functions is primitive recursive. -/
theorem prim_append {f g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x ++ g x := Primrec.list_append.comp hf hg

/-- `List.headI` of a primitive recursive function is primitive recursive. -/
theorem prim_headI {inst : Inhabited β} {f : α → List β} (hf : Primrec f) :
    Primrec fun x => (f x).headI := Primrec.list_headI.comp hf

/-- `List.tail` of a primitive recursive function is primitive recursive. -/
theorem prim_tail {f : α → List β} (hf : Primrec f) : Primrec fun x => (f x).tail :=
  Primrec.list_tail.comp hf

/-- `List.length` of a primitive recursive function is primitive recursive. -/
theorem prim_length {f : α → List β} (hf : Primrec f) : Primrec fun x => (f x).length :=
  Primrec.list_length.comp hf

/-- `List.range` of a primitive recursive function is primitive recursive. -/
theorem prim_range {f : α → ℕ} (hf : Primrec f) : Primrec fun x => List.range (f x) :=
  Primrec.list_range.comp hf

/-- `List.reverse` of a primitive recursive function is primitive recursive. -/
theorem prim_reverse {f : α → List β} (hf : Primrec f) : Primrec fun x => (f x).reverse :=
  Primrec.list_reverse.comp hf

/-- The sum of two primitive recursive functions is primitive recursive. -/
theorem prim_add {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x + g x := Primrec.nat_add.comp hf hg

/-- The truncated difference of two primitive recursive functions is primitive recursive. -/
theorem prim_sub {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x - g x := Primrec.nat_sub.comp hf hg

/-- The product of two primitive recursive functions is primitive recursive. -/
theorem prim_mul {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x * g x := Primrec.nat_mul.comp hf hg

/-- The remainder `f x % g x` of two primitive recursive functions is primitive recursive. -/
theorem prim_mod {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x % g x := Primrec.nat_mod.comp hf hg

/-- The quotient `f x / g x` of two primitive recursive functions is primitive recursive. -/
theorem prim_div {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x / g x := Primrec.nat_div.comp hf hg

/-- `List.getD` with primitive recursive list and index is primitive recursive. -/
theorem prim_getD {f : α → List β} {g : α → ℕ} (d : β) (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => (f x).getD (g x) d := (Primrec.list_getD d).comp hf hg

/-- An `if` with a primitive recursive condition and primitive recursive branches is primitive
recursive. -/
theorem prim_ite {c : α → Prop} [DecidablePred c] {f g : α → β} (hc : PrimrecPred c)
    (hf : Primrec f) (hg : Primrec g) : Primrec fun x => if c x then f x else g x :=
  Primrec.ite hc hf hg

/-- Equality of two primitive recursive functions is a primitive recursive predicate. -/
theorem pred_eq {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun x => f x = g x := Primrec.eq.comp hf hg

/-- `f x < g x` for primitive recursive `f` and `g` is a primitive recursive predicate. -/
theorem pred_lt {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun x => f x < g x := Primrec.nat_lt.comp hf hg

/-- `f x ≤ g x` for primitive recursive `f` and `g` is a primitive recursive predicate. -/
theorem pred_le {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun x => f x ≤ g x := Primrec.nat_le.comp hf hg

/-- The conjunction of two primitive recursive predicates is primitive recursive. -/
theorem pred_and {p q : α → Prop} (hp : PrimrecPred p) (hq : PrimrecPred q) :
    PrimrecPred fun x => p x ∧ q x := hp.and hq

/-- Disequality of two primitive recursive functions is a primitive recursive predicate. -/
theorem pred_ne {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun x => f x ≠ g x := (pred_eq hf hg).not

/-- Mapping a primitive recursive function over a primitive recursive list is primitive
recursive. -/
theorem prim_map {f : α → List β} {g : α → β → γ} (hf : Primrec f)
    (hg : Primrec fun y : α × β => g y.1 y.2) : Primrec fun x => (f x).map (g x) :=
  Primrec.list_map hf hg.to₂

/-- `List.flatMap` of a primitive recursive function over a primitive recursive list is primitive
recursive. -/
theorem prim_flatMap {f : α → List β} {g : α → β → List γ} (hf : Primrec f)
    (hg : Primrec fun y : α × β => g y.1 y.2) : Primrec fun x => (f x).flatMap (g x) :=
  Primrec.list_flatMap hf hg.to₂

end Prim

open Lean Meta Elab Tactic in
/-- Succeeds when the target is `Primrec fun x => (_).1` or `Primrec fun x => (_).2`. -/
elab (name := guardProj) "guard_proj" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  let some f := t.getAppArgs.back? | throwError "not an application"
  unless f.isLambda do throwError "not a lambda"
  let b := f.bindingBody!
  unless b.isAppOf ``Prod.fst || b.isAppOf ``Prod.snd do throwError "not a projection"

open Lean Meta Elab Tactic in
/-- Succeeds when the target is `Primrec fun x => (_, _)`. -/
elab (name := guardMk) "guard_mk" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  let some f := t.getAppArgs.back? | throwError "not an application"
  unless f.isLambda do throwError "not a lambda"
  unless f.bindingBody!.isAppOf ``Prod.mk do throwError "not a pair"

/-- One step of `prim`. Later files add rules for their own definitions. -/
syntax (name := primStep) "prim_step" : tactic

macro_rules
  | `(tactic| prim_step) => `(tactic| with_reducible first
  | exact Primrec.const _
  | exact prim_self
  | exact Primrec.fst
  | exact Primrec.snd
  | assumption
  | (guard_mk; apply prim_pair)
  | apply prim_unpair
  | apply prim_natPair
  | apply prim_cons
  | apply prim_append
  | apply prim_headI
  | apply prim_tail
  | apply prim_length
  | apply prim_range
  | apply prim_reverse
  | apply prim_add
  | apply prim_sub
  | apply prim_mul
  | apply prim_mod
  | apply prim_div
  | apply prim_getD
  | apply prim_ite
  | apply pred_and
  | apply pred_eq
  | apply pred_ne
  | apply pred_lt
  | apply pred_le
  | apply prim_map
  | apply prim_flatMap
  | (guard_proj; apply prim_fst)
  | (guard_proj; apply prim_snd))

/-- Closes `Primrec` goals built from the lemmas above. -/
macro "prim" : tactic => `(tactic| repeat' prim_step)

end DiagonaLean.Foundations.Computability
