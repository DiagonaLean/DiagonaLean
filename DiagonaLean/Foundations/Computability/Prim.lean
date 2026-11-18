/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import Mathlib.Computability.PartrecBasis
import Mathlib.Tactic.FunProp

@[expose] public section

/-! # `fun_prop` for `Primrec` goals

Registers `Primrec` and `PrimrecPred` with Mathlib's `fun_prop` tactic, so that `fun_prop` proves
`Primrec` and `PrimrecPred` goals built from pairs, projections, arithmetic, list operations, folds
and `if`. Later files tag the lemmas for their own definitions with `@[fun_prop]`, in
compositional form (`Primrec f → Primrec fun x => g (f x)`) or as `Primrec g`.

A goal whose function contains codes built with `Nat.pair` from literals can time out, because
unification evaluates them; `attribute [local irreducible] Nat.pair` prevents this.
-/

namespace DiagonaLean.Foundations.Computability

/-! ### `fun_prop` for `Primrec` and `PrimrecPred`

`Primrec` and `PrimrecPred` are `fun_prop` properties: the lambda theorems are Mathlib's
`Primrec.id`, `Primrec.const`, `Primrec.comp` and `PrimrecPred.comp`, and the function theorems are
the `prim_*` and `pred_*` lemmas below, in compositional form. Later files tag the lemmas for their
own definitions with `@[fun_prop]`. -/

attribute [fun_prop] Primrec PrimrecPred
attribute [fun_prop] Primrec.id Primrec.const Primrec.comp PrimrecPred.comp PrimrecPred.not
  PrimrecPred.or

section Prim

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

@[fun_prop] theorem prim_pair {f : α → β} {g : α → γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => (f x, g x) := hf.pair hg

@[fun_prop] theorem prim_fst {f : α → β × γ} (hf : Primrec f) : Primrec fun x => (f x).1 := Primrec.fst.comp hf

@[fun_prop] theorem prim_snd {f : α → β × γ} (hf : Primrec f) : Primrec fun x => (f x).2 := Primrec.snd.comp hf

@[fun_prop] theorem prim_natPair {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => Nat.pair (f x) (g x) := Primrec₂.natPair.comp hf hg

@[fun_prop] theorem prim_unpair {f : α → ℕ} (hf : Primrec f) : Primrec fun x => (f x).unpair :=
  Primrec.unpair.comp hf

@[fun_prop] theorem prim_cons {f : α → β} {g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x :: g x := Primrec.list_cons.comp hf hg

@[fun_prop] theorem prim_append {f g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x ++ g x := Primrec.list_append.comp hf hg

/-- `List.append` written as a function rather than as `++`. -/
@[fun_prop] theorem prim_append' {f g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => (f x).append (g x) := Primrec.list_append.comp hf hg

@[fun_prop] theorem prim_headI {inst : Inhabited β} {f : α → List β} (hf : Primrec f) :
    Primrec fun x => (f x).headI := Primrec.list_headI.comp hf

@[fun_prop] theorem prim_tail {f : α → List β} (hf : Primrec f) : Primrec fun x => (f x).tail :=
  Primrec.list_tail.comp hf

@[fun_prop] theorem prim_length {f : α → List β} (hf : Primrec f) : Primrec fun x => (f x).length :=
  Primrec.list_length.comp hf

@[fun_prop] theorem prim_range {f : α → ℕ} (hf : Primrec f) : Primrec fun x => List.range (f x) :=
  Primrec.list_range.comp hf

@[fun_prop] theorem prim_reverse {f : α → List β} (hf : Primrec f) : Primrec fun x => (f x).reverse :=
  Primrec.list_reverse.comp hf

@[fun_prop] theorem prim_add {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x + g x := Primrec.nat_add.comp hf hg

@[fun_prop] theorem prim_sub {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x - g x := Primrec.nat_sub.comp hf hg

@[fun_prop] theorem prim_mul {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x * g x := Primrec.nat_mul.comp hf hg

@[fun_prop] theorem prim_mod {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x % g x := Primrec.nat_mod.comp hf hg

@[fun_prop] theorem prim_div {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x / g x := Primrec.nat_div.comp hf hg

@[fun_prop] theorem prim_getD {f : α → List β} {g : α → ℕ} (d : β) (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => (f x).getD (g x) d := (Primrec.list_getD d).comp hf hg

@[fun_prop] theorem prim_ite {c : α → Prop} [DecidablePred c] {f g : α → β} (hc : PrimrecPred c)
    (hf : Primrec f) (hg : Primrec g) : Primrec fun x => if c x then f x else g x :=
  Primrec.ite hc hf hg

@[fun_prop] theorem pred_eq {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun x => f x = g x := Primrec.eq.comp hf hg

@[fun_prop] theorem pred_lt {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun x => f x < g x := Primrec.nat_lt.comp hf hg

@[fun_prop] theorem pred_le {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun x => f x ≤ g x := Primrec.nat_le.comp hf hg

@[fun_prop] theorem pred_and {p q : α → Prop} (hp : PrimrecPred p) (hq : PrimrecPred q) :
    PrimrecPred fun x => p x ∧ q x := hp.and hq

@[fun_prop] theorem pred_ne {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun x => f x ≠ g x := (pred_eq hf hg).not

@[fun_prop] theorem prim_map {f : α → List β} {g : α → β → γ} (hf : Primrec f)
    (hg : Primrec fun y : α × β => g y.1 y.2) : Primrec fun x => (f x).map (g x) :=
  Primrec.list_map hf hg.to₂

@[fun_prop] theorem prim_foldr {f : α → List β} {g : α → β → γ → γ} {z : α → γ} (hf : Primrec f)
    (hz : Primrec z) (hg : Primrec fun y : α × (β × γ) => g y.1 y.2.1 y.2.2) :
    Primrec fun x => (f x).foldr (g x) (z x) :=
  Primrec.list_foldr (h := fun a y => g a y.1 y.2) hf hz hg

@[fun_prop] theorem prim_flatMap {f : α → List β} {g : α → β → List γ} (hf : Primrec f)
    (hg : Primrec fun y : α × β => g y.1 y.2) : Primrec fun x => (f x).flatMap (g x) :=
  Primrec.list_flatMap hf hg.to₂

end Prim

end DiagonaLean.Foundations.Computability
