/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.Partrec
import Mathlib.Tactic.FunProp

@[expose] public section

/-! # `fun_prop` for `Primrec` goals

Registers `Primrec`, `PrimrecPred` and `Computable` with Mathlib's `fun_prop` tactic, so that
`fun_prop` proves such goals built from pairs, projections, arithmetic, list operations, folds and
`if`. A `Primrec` goal is also a `Computable` goal, through the transition theorem
`Primrec.to_comp`. Later files tag the lemmas for their own definitions with `@[fun_prop]`, in
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
  PrimrecPred.or Primrec.ofNat Primrec.encode Primrec.decode₂

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

/-- `List.getD` with a default that varies. -/
@[fun_prop] theorem prim_getD' {f : α → List β} {g : α → ℕ} {d : α → β} (hf : Primrec f)
    (hg : Primrec g) (hd : Primrec d) : Primrec fun x => (f x).getD (g x) (d x) :=
  (Primrec.option_getD.comp (Primrec.list_getElem?.comp hf hg) hd).of_eq fun x =>
    (List.getD_eq_getElem?_getD ..).symm

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

@[fun_prop] theorem prim_foldl {f : α → List β} {g : α → γ} {h : α → γ → β → γ} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec fun y : α × (γ × β) => h y.1 y.2.1 y.2.2) :
    Primrec fun x => (f x).foldl (h x) (g x) :=
  Primrec.list_foldl (h := fun a y => h a y.1 y.2) hf hg hh

@[fun_prop] theorem prim_iterate {f : α → ℕ} {g : α → β} {h : α → β → β} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec fun y : α × β => h y.1 y.2) :
    Primrec fun x => (h x)^[f x] (g x) :=
  Primrec.nat_iterate hf hg hh

@[fun_prop] theorem prim_boolToNat {f : α → Bool} (hf : Primrec f) :
    Primrec fun x => (f x).toNat := (Primrec.dom_finite Bool.toNat).comp hf

@[fun_prop] theorem prim_band {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x && g x := Primrec.and.comp hf hg

@[fun_prop] theorem prim_decide {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) :
    Primrec fun x => decide (p x) := hp.decide

@[fun_prop] theorem prim_elim {o : α → Option β} {f : α → γ} {g : α → β → γ} (ho : Primrec o)
    (hf : Primrec f) (hg : Primrec fun y : α × β => g y.1 y.2) :
    Primrec fun x => (o x).elim (f x) (g x) :=
  (Primrec.option_casesOn ho hf hg).of_eq fun x => by cases o x <;> rfl

@[fun_prop] theorem prim_all {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec fun y : α × β => p y.1 y.2) : Primrec fun x => (f x).all (p x) := by
  have h : Primrec fun x => (f x).foldr (fun b acc => p x b && acc) true := by fun_prop
  refine h.of_eq fun x => ?_
  induction f x with
  | nil => rfl
  | cons b l ih => simp [List.all_cons, ih]

@[fun_prop] theorem prim_flatMap {f : α → List β} {g : α → β → List γ} (hf : Primrec f)
    (hg : Primrec fun y : α × β => g y.1 y.2) : Primrec fun x => (f x).flatMap (g x) :=
  Primrec.list_flatMap hf hg.to₂

end Prim

/-! ### `fun_prop` for `Computable`

The lambda theorems are Mathlib's `Computable.id`, `Computable.const`, `Computable.comp` and
`Computable.pair`. Mathlib states most binary operations with `Computable₂`, which `fun_prop` does
not see through, so they get compositional wrappers below. `Primrec.to_comp` is a transition
theorem: a function that `fun_prop` proves `Primrec` is `Computable`.

`fun_prop` decomposes an application before it tries a transition, so an operation whose arguments
may be merely `Computable` needs a lemma at the `Computable` level. For `List.map`, `List.flatMap`
and `List.foldr`, Mathlib has only `Primrec` versions; their `Computable`-level lemmas below take
`Primrec` hypotheses, which `fun_prop` proves through the `Primrec` lemmas. -/

attribute [fun_prop] Computable
attribute [fun_prop] Computable.id Computable.const Computable.comp Computable.pair
  Primrec.to_comp

section Comp

variable {α β γ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

@[fun_prop] theorem comp_fst {f : α → β × γ} (hf : Computable f) :
    Computable fun x => (f x).1 := Computable.fst.comp hf

@[fun_prop] theorem comp_snd {f : α → β × γ} (hf : Computable f) :
    Computable fun x => (f x).2 := Computable.snd.comp hf

@[fun_prop] theorem comp_natPair {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun x => Nat.pair (f x) (g x) := Primrec₂.natPair.to_comp.comp hf hg

@[fun_prop] theorem comp_unpair {f : α → ℕ} (hf : Computable f) :
    Computable fun x => (f x).unpair := Computable.unpair.comp hf

@[fun_prop] theorem comp_succ {f : α → ℕ} (hf : Computable f) :
    Computable fun x => (f x).succ := Computable.succ.comp hf

@[fun_prop] theorem comp_add {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun x => f x + g x := Primrec.nat_add.to_comp.comp hf hg

@[fun_prop] theorem comp_sub {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun x => f x - g x := Primrec.nat_sub.to_comp.comp hf hg

@[fun_prop] theorem comp_mul {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun x => f x * g x := Primrec.nat_mul.to_comp.comp hf hg

@[fun_prop] theorem comp_div {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun x => f x / g x := Primrec.nat_div.to_comp.comp hf hg

@[fun_prop] theorem comp_mod {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun x => f x % g x := Primrec.nat_mod.to_comp.comp hf hg

@[fun_prop] theorem comp_some {f : α → β} (hf : Computable f) :
    Computable fun x => some (f x) := Computable.option_some.comp hf

@[fun_prop] theorem comp_cons {f : α → β} {g : α → List β} (hf : Computable f)
    (hg : Computable g) : Computable fun x => f x :: g x := Computable.list_cons.comp hf hg

@[fun_prop] theorem comp_append {f g : α → List β} (hf : Computable f) (hg : Computable g) :
    Computable fun x => f x ++ g x := Computable.list_append.comp hf hg

/-- `List.append` written as a function rather than as `++`. -/
@[fun_prop] theorem comp_append' {f g : α → List β} (hf : Computable f) (hg : Computable g) :
    Computable fun x => (f x).append (g x) := Computable.list_append.comp hf hg

@[fun_prop] theorem comp_length {f : α → List β} (hf : Computable f) :
    Computable fun x => (f x).length := Computable.list_length.comp hf

@[fun_prop] theorem comp_reverse {f : α → List β} (hf : Computable f) :
    Computable fun x => (f x).reverse := Computable.list_reverse.comp hf

@[fun_prop] theorem comp_cond {c : α → Bool} {f g : α → σ} (hc : Computable c)
    (hf : Computable f) (hg : Computable g) :
    Computable fun x => _root_.cond (c x) (f x) (g x) := Computable.cond hc hf hg

@[fun_prop] theorem comp_ite {c : α → Prop} [DecidablePred c] {f g : α → σ} (hc : PrimrecPred c)
    (hf : Computable f) (hg : Computable g) : Computable fun x => if c x then f x else g x :=
  (Computable.cond hc.decide.to_comp hf hg).of_eq fun x => by by_cases h : c x <;> simp [h]

@[fun_prop] theorem comp_getD {f : α → Option β} {g : α → β} (hf : Computable f)
    (hg : Computable g) : Computable fun x => (f x).getD (g x) := Computable.option_getD hf hg

/-- `List.map` at the `Computable` level, with `Primrec` hypotheses (see the section comment). -/
@[fun_prop] theorem comp_map {f : α → List β} {g : α → β → γ} (hf : Primrec f)
    (hg : Primrec fun y : α × β => g y.1 y.2) : Computable fun x => (f x).map (g x) :=
  (prim_map hf hg).to_comp

/-- `List.flatMap` at the `Computable` level, with `Primrec` hypotheses. -/
@[fun_prop] theorem comp_flatMap {f : α → List β} {g : α → β → List γ} (hf : Primrec f)
    (hg : Primrec fun y : α × β => g y.1 y.2) : Computable fun x => (f x).flatMap (g x) :=
  (prim_flatMap hf hg).to_comp

/-- `List.foldr` at the `Computable` level, with `Primrec` hypotheses. -/
@[fun_prop] theorem comp_foldr {f : α → List β} {g : α → β → γ → γ} {z : α → γ}
    (hf : Primrec f) (hz : Primrec z) (hg : Primrec fun y : α × (β × γ) => g y.1 y.2.1 y.2.2) :
    Computable fun x => (f x).foldr (g x) (z x) :=
  (prim_foldr hf hz hg).to_comp

end Comp

end DiagonaLean.Foundations.Computability
