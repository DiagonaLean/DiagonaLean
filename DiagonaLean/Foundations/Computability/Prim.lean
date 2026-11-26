/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.Partrec
import Mathlib.Tactic.FunProp
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

@[expose] public section

/-! # `fun_prop` for `Primrec` goals

Registers `Primrec`, `PrimrecPred` and `Computable` with Mathlib's `fun_prop` tactic, so that
`fun_prop` proves such goals built from pairs, projections, arithmetic, list operations, folds and
`if`. A `Primrec` goal is also a `Computable` goal, through the transition theorem
`Primrec.to_comp`. Later files tag the lemmas for their own definitions with `@[fun_prop]`, in
compositional form (`Primrec f → Primrec fun x => g (f x)`) or as `Primrec g`.

A function out of a finite type, including a `match` on a value of a finite type, is primitive
recursive with no lemma of its own: `Primrec.dom_finite` is a transition theorem, tried when no
other theorem applies, and it succeeds when instance search finds `Finite` of the domain.

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
  PrimrecPred.or Primrec.ofNat Primrec.encode Primrec.decode₂ Primrec.decode

/- Every function out of a finite type is primitive recursive. As a transition theorem it closes
goals for functions with no `fun_prop` lemma, such as `match` on `Option Bool`, when instance search
finds `Finite` of the domain. -/
attribute [fun_prop] Primrec.dom_finite

section Prim

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

@[fun_prop] theorem prim_pair {f : α → β} {g : α → γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => (f x, g x) := hf.pair hg

@[fun_prop] theorem prim_fst {f : α → β × γ} (hf : Primrec f) : Primrec fun x => (f x).1 := Primrec.fst.comp hf

@[fun_prop] theorem prim_snd {f : α → β × γ} (hf : Primrec f) : Primrec fun x => (f x).2 := Primrec.snd.comp hf

/-- The value of an element of a subtype with the encoding `Primcodable.subtype hp`. `fun_prop`
proves `hp` as a side goal, so the predicate needs a `@[fun_prop]` lemma (`isType0_prim`). -/
@[fun_prop] theorem prim_subtype_val {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p}
    {f : α → { b // p b }} (hf : @Primrec α { b // p b } _ (Primcodable.subtype hp) f) :
    Primrec fun x => (f x).1 :=
  letI := Primcodable.subtype hp
  (Primrec.subtype_val (hp := hp)).comp hf

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
  (Primrec.option_getD.comp (Primrec.list_getElem?.comp hf hg) hd).of_eq fun _ =>
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

@[fun_prop] theorem prim_optionGetD {f : α → Option β} {g : α → β} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => (f x).getD (g x) := Primrec.option_getD.comp hf hg

@[fun_prop] theorem prim_sumElim {δ : Type*} [Primcodable δ] {o : α → β ⊕ δ} {f : α → β → γ}
    {g : α → δ → γ} (ho : Primrec o) (hf : Primrec fun y : α × β => f y.1 y.2)
    (hg : Primrec fun y : α × δ => g y.1 y.2) : Primrec fun x => (o x).elim (f x) (g x) :=
  (Primrec.sumCasesOn ho hf hg).of_eq fun x => by cases o x <;> rfl

@[fun_prop] theorem prim_finVal {n : ℕ} {f : α → Fin n} (hf : Primrec f) :
    Primrec fun x => (f x).val := Primrec.fin_val.comp hf

@[fun_prop] theorem prim_optionMap {f : α → Option β} {g : α → β → γ} (hf : Primrec f)
    (hg : Primrec fun y : α × β => g y.1 y.2) : Primrec fun x => (f x).map (g x) :=
  Primrec.option_map hf hg

@[fun_prop] theorem prim_sumInl {δ : Type*} [Primcodable δ] {f : α → β} (hf : Primrec f) :
    Primrec fun x => (Sum.inl (f x) : β ⊕ δ) := Primrec.sumInl.comp hf

@[fun_prop] theorem prim_sumInr {δ : Type*} [Primcodable δ] {f : α → δ} (hf : Primrec f) :
    Primrec fun x => (Sum.inr (f x) : β ⊕ δ) := Primrec.sumInr.comp hf

/-- `Sum.map`, as `Sum.elim` of the two injections. -/
@[fun_prop] theorem prim_sumMap {δ ε : Type*} [Primcodable δ] [Primcodable ε] {o : α → β ⊕ δ}
    {f : α → β → γ} {g : α → δ → ε} (ho : Primrec o) (hf : Primrec fun y : α × β => f y.1 y.2)
    (hg : Primrec fun y : α × δ => g y.1 y.2) : Primrec fun x => Sum.map (f x) (g x) (o x) :=
  (prim_sumElim (f := fun x b => (Sum.inl (f x b) : γ ⊕ ε))
    (g := fun x d => (Sum.inr (g x d) : γ ⊕ ε)) ho (prim_sumInl hf) (prim_sumInr hg)).of_eq
    fun x => by cases o x <;> rfl

@[fun_prop] theorem prim_some {f : α → β} (hf : Primrec f) : Primrec fun x => some (f x) :=
  Primrec.option_some.comp hf

@[fun_prop] theorem prim_getElem? {f : α → List β} {g : α → ℕ} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => (f x)[g x]? := Primrec.list_getElem?.comp hf hg

@[fun_prop] theorem prim_max {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => max (f x) (g x) := Primrec.nat_max.comp hf hg

@[fun_prop] theorem prim_min {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => min (f x) (g x) := Primrec.nat_min.comp hf hg

@[fun_prop] theorem prim_filterMap {f : α → List β} {g : α → β → Option γ} (hf : Primrec f)
    (hg : Primrec fun y : α × β => g y.1 y.2) : Primrec fun x => (f x).filterMap (g x) :=
  Primrec.listFilterMap hf hg

@[fun_prop] theorem prim_idxOf [DecidableEq β] {f : α → List β} {g : α → β} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => (f x).idxOf (g x) := Primrec.list_idxOf.comp hg hf

/-- `x ^ k` by iterated multiplication. -/
theorem pow_eq_iterate (x k : ℕ) : x ^ k = (fun y => y * x)^[k] 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ← ih, pow_succ]

@[fun_prop] theorem prim_pow {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x ^ g x := by
  have h : Primrec fun q : ℕ × ℕ => (fun y => y * q.1)^[q.2] 1 := by fun_prop
  exact (h.of_eq fun q => (pow_eq_iterate q.1 q.2).symm).comp (hf.pair hg)

/-- One halving step of `Nat.log2`, counting the halvings. -/
def log2Step (q : ℕ × ℕ) : ℕ × ℕ := if 2 ≤ q.1 then (q.1 / 2, q.2 + 1) else q

theorem log2Step_iterate (k : ℕ) : ∀ x c, Nat.log2 x ≤ k → (log2Step^[k] (x, c)).2 = c + Nat.log2 x := by
  induction k with
  | zero => intro x c h; simp [Nat.le_zero.1 h]
  | succ k ih =>
    intro x c h
    rw [Function.iterate_succ_apply]
    by_cases hx : 2 ≤ x
    · have hl : Nat.log2 x = Nat.log2 (x / 2) + 1 := by rw [Nat.log2_def]; simp [hx]
      simp only [log2Step, hx, ite_true]
      rw [ih (x / 2) (c + 1) (by omega), hl]; omega
    · have hl : Nat.log2 x = 0 := by rw [Nat.log2_def]; simp [hx]
      simp only [log2Step, hx, ite_false]
      rw [ih x c (by omega)]

@[fun_prop] theorem prim_log2 {f : α → ℕ} (hf : Primrec f) : Primrec fun x => Nat.log2 (f x) := by
  have h : Primrec fun n : ℕ => (log2Step^[n] (n, 0)).2 := by unfold log2Step; fun_prop
  exact (h.of_eq fun n => by rw [log2Step_iterate n n 0 (Nat.log2_le_self n), Nat.zero_add]).comp hf

omit [Primcodable β] in
/-- `dedup` as a fold: an element is kept when it is not already in what follows. -/
theorem dedup_eq_foldr [DecidableEq β] (l : List β) :
    l.dedup = l.foldr (fun a acc => if acc.idxOf a < acc.length then acc else a :: acc) [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ← ih]
    by_cases ha : a ∈ l
    · rw [List.dedup_cons_of_mem ha, ite_eq_left (List.idxOf_lt_length_iff.2 (List.mem_dedup.2 ha))]
    · rw [List.dedup_cons_of_notMem ha,
        ite_eq_right fun h => ha (List.mem_dedup.1 (List.idxOf_lt_length_iff.1 h))]

@[fun_prop] theorem prim_dedup [DecidableEq β] {f : α → List β} (hf : Primrec f) :
    Primrec fun x => (f x).dedup := by
  have h : Primrec fun l : List β =>
      l.foldr (fun a acc => if acc.idxOf a < acc.length then acc else a :: acc) [] := by fun_prop
  exact (h.of_eq fun l => (dedup_eq_foldr l).symm).comp hf

@[fun_prop] theorem prim_flatMap {f : α → List β} {g : α → β → List γ} (hf : Primrec f)
    (hg : Primrec fun y : α × β => g y.1 y.2) : Primrec fun x => (f x).flatMap (g x) :=
  Primrec.list_flatMap hf hg.to₂

/-! #### Further list, option, `Bool` and `ℕ` operations

Where Mathlib's lemma fixes the predicate, the wrapper lets it depend on the outer variable,
by a rewrite into `foldr` or `map`. -/

@[fun_prop] theorem prim_take {f : α → ℕ} {g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => (g x).take (f x) := Primrec.list_take.comp hf hg

@[fun_prop] theorem prim_drop {f : α → ℕ} {g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => (g x).drop (f x) := Primrec.list_drop.comp hf hg

@[fun_prop] theorem prim_head? {f : α → List β} (hf : Primrec f) : Primrec fun x => (f x).head? :=
  Primrec.list_head?.comp hf

@[fun_prop] theorem prim_flatten {f : α → List (List β)} (hf : Primrec f) :
    Primrec fun x => (f x).flatten := Primrec.list_flatten.comp hf

@[fun_prop] theorem prim_concat {f : α → List β} {g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => (f x).concat (g x) :=
  (Primrec.list_concat.comp hf hg).of_eq fun _ => (List.concat_eq_append ..).symm

@[fun_prop] theorem prim_set {f : α → List β} {g : α → ℕ} {h : α → β} (hf : Primrec f)
    (hg : Primrec g) (hh : Primrec h) : Primrec fun x => (f x).set (g x) (h x) :=
  Primrec.list_set.comp hf (hg.pair hh)

omit [Primcodable β] in
theorem replicate_eq_iterate (n : ℕ) (b : β) : List.replicate n b = (b :: ·)^[n] [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih, List.replicate_succ]

@[fun_prop] theorem prim_replicate {f : α → ℕ} {g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => List.replicate (f x) (g x) := by
  have h : Primrec fun x => (g x :: ·)^[f x] [] := by fun_prop
  exact h.of_eq fun x => (replicate_eq_iterate _ _).symm

@[fun_prop] theorem prim_succ {f : α → ℕ} (hf : Primrec f) : Primrec fun x => (f x).succ :=
  Primrec.succ.comp hf

@[fun_prop] theorem prim_pred {f : α → ℕ} (hf : Primrec f) : Primrec fun x => (f x).pred :=
  Primrec.pred.comp hf

@[fun_prop] theorem prim_bodd {f : α → ℕ} (hf : Primrec f) : Primrec fun x => (f x).bodd :=
  Primrec.nat_bodd.comp hf

@[fun_prop] theorem prim_bnot {f : α → Bool} (hf : Primrec f) : Primrec fun x => !f x :=
  Primrec.not.comp hf

@[fun_prop] theorem prim_bor {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x || g x := Primrec.or.comp hf hg

@[fun_prop] theorem prim_cond {c : α → Bool} {f g : α → β} (hc : Primrec c) (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => cond (c x) (f x) (g x) := Primrec.cond hc hf hg

@[fun_prop] theorem prim_beq [DecidableEq β] {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x == g x := Primrec.beq.comp hf hg

@[fun_prop] theorem prim_optionBind {f : α → Option β} {g : α → β → Option γ} (hf : Primrec f)
    (hg : Primrec fun y : α × β => g y.1 y.2) : Primrec fun x => (f x).bind (g x) :=
  Primrec.option_bind hf hg.to₂

@[fun_prop] theorem prim_isSome {f : α → Option β} (hf : Primrec f) :
    Primrec fun x => (f x).isSome := Primrec.option_isSome.comp hf

@[fun_prop] theorem prim_orElse {f g : α → Option β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => (f x <|> g x) := Primrec.option_orElse.comp hf hg

@[fun_prop] theorem prim_optionToList {f : α → Option β} (hf : Primrec f) :
    Primrec fun x => (f x).toList := Primrec.optionToList.comp hf

@[fun_prop] theorem prim_filter {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec fun y : α × β => p y.1 y.2) : Primrec fun x => (f x).filter (p x) := by
  have h : Primrec fun x => (f x).foldr (fun b acc => if p x b then b :: acc else acc) [] := by
    fun_prop
  refine h.of_eq fun x => ?_
  induction f x with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.filter_cons]

@[fun_prop] theorem prim_any {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec fun y : α × β => p y.1 y.2) : Primrec fun x => (f x).any (p x) := by
  have h : Primrec fun x => (f x).foldr (fun b acc => p x b || acc) false := by fun_prop
  refine h.of_eq fun x => ?_
  induction f x with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.any_cons]

@[fun_prop] theorem prim_find? {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec fun y : α × β => p y.1 y.2) : Primrec fun x => (f x).find? (p x) := by
  have h : Primrec fun x => (f x).foldr (fun b acc => if p x b then some b else acc) none := by
    fun_prop
  refine h.of_eq fun x => ?_
  induction f x with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.find?_cons]; cases p x b <;> rfl

@[fun_prop] theorem prim_findIdx {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec fun y : α × β => p y.1 y.2) : Primrec fun x => (f x).findIdx (p x) := by
  have h : Primrec fun x => (f x).foldr (fun b acc => if p x b then 0 else acc + 1) 0 := by
    fun_prop
  refine h.of_eq fun x => ?_
  induction f x with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.findIdx_cons]

@[fun_prop] theorem prim_takeWhile {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec fun y : α × β => p y.1 y.2) : Primrec fun x => (f x).takeWhile (p x) := by
  have h : Primrec fun x => (f x).take ((f x).findIdx fun b => !p x b) := by fun_prop
  exact h.of_eq fun x => List.takeWhile_eq_take_findIdx_not.symm

@[fun_prop] theorem prim_dropWhile {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec fun y : α × β => p y.1 y.2) : Primrec fun x => (f x).dropWhile (p x) := by
  have h : Primrec fun x => (f x).drop ((f x).findIdx fun b => !p x b) := by fun_prop
  exact h.of_eq fun x => List.dropWhile_eq_drop_findIdx_not.symm

@[fun_prop] theorem prim_count [DecidableEq β] {f : α → List β} {g : α → β} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => (f x).count (g x) := by
  have h : Primrec fun x => (f x).foldr (fun b acc => if b == g x then acc + 1 else acc) 0 := by
    fun_prop
  refine h.of_eq fun x => ?_
  induction f x with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, ih, List.count_cons]; split <;> simp_all

@[fun_prop] theorem prim_sum {f : α → List ℕ} (hf : Primrec f) : Primrec fun x => (f x).sum := by
  have h : Primrec fun x => (f x).foldr (· + ·) 0 := by fun_prop
  exact h.of_eq fun x => (List.sum_eq_foldr).symm

@[fun_prop] theorem pred_forall_mem {f : α → List β} {p : α → β → Prop}
    (hf : Primrec f) (hp : PrimrecPred fun y : α × β => p y.1 y.2) :
    PrimrecPred fun x => ∀ b ∈ f x, p x b := by
  have h := (PrimrecPred.forall_mem_list hp).comp (prim_map (g := fun x b => (x, b)) hf
    (Primrec.pair (Primrec.fst) (Primrec.snd)))
  exact h.of_eq fun x => by simp

@[fun_prop] theorem pred_exists_mem {f : α → List β} {p : α → β → Prop}
    (hf : Primrec f) (hp : PrimrecPred fun y : α × β => p y.1 y.2) :
    PrimrecPred fun x => ∃ b ∈ f x, p x b := by
  have h := (PrimrecPred.exists_mem_list hp).comp (prim_map (g := fun x b => (x, b)) hf
    (Primrec.pair (Primrec.fst) (Primrec.snd)))
  exact h.of_eq fun x => by simp

@[fun_prop] theorem pred_forall_lt {f : α → ℕ} {p : α → ℕ → Prop} (hf : Primrec f)
    (hp : PrimrecPred fun y : α × ℕ => p y.1 y.2) : PrimrecPred fun x => ∀ n < f x, p x n :=
  (pred_forall_mem (prim_range hf) hp).of_eq fun x => by simp

@[fun_prop] theorem pred_exists_lt {f : α → ℕ} {p : α → ℕ → Prop} (hf : Primrec f)
    (hp : PrimrecPred fun y : α × ℕ => p y.1 y.2) : PrimrecPred fun x => ∃ n < f x, p x n :=
  (pred_exists_mem (prim_range hf) hp).of_eq fun x => by simp

@[fun_prop] theorem pred_mem {f : α → List β} {g : α → β} (hf : Primrec f)
    (hg : Primrec g) : PrimrecPred fun x => g x ∈ f x :=
  (pred_exists_mem (p := fun x b => b = g x) hf
    (pred_eq Primrec.snd (hg.comp Primrec.fst))).of_eq fun x => by simp

end Prim

/-! #### Zips, `erase`, `min?`/`max?`, `insert`, products, `gcd`, `lcm`, `log` and `sqrt`

Each is rewritten into operations already covered (`zipWith` into a `filterMap` over indices,
`erase` into `take`/`drop` at `idxOf`, `gcd` and `log` into `Nat.findGreatest`), and the rewrite
is proved once. -/

section Gaps

variable {α β γ δ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]

omit [Primcodable β] [Primcodable γ] [Primcodable δ] in
theorem zipWith_eq_filterMap (g : β → γ → δ) (l₁ : List β) (l₂ : List γ) :
    List.zipWith g l₁ l₂ = (List.range (min l₁.length l₂.length)).filterMap
      fun i => l₁[i]?.bind fun a => l₂[i]?.map (g a) := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      rw [List.zipWith_cons_cons, ih, List.length_cons, List.length_cons, Nat.succ_min_succ,
        List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
      simp

@[fun_prop] theorem prim_zipWith {f : α → List β} {g : α → List γ} {h : α → β → γ → δ}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec fun y : α × (β × γ) => h y.1 y.2.1 y.2.2) :
    Primrec fun x => List.zipWith (h x) (f x) (g x) := by
  simp only [zipWith_eq_filterMap]
  fun_prop

@[fun_prop] theorem prim_zip {f : α → List β} {g : α → List γ} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => (f x).zip (g x) :=
  prim_zipWith (h := fun _ => Prod.mk) hf hg (by fun_prop)

@[fun_prop] theorem prim_zipIdx {f : α → List β} {g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => (f x).zipIdx (g x) := by
  simp only [List.zipIdx_eq_zip_range', List.range'_eq_map_range]
  fun_prop

omit [Primcodable β] in
theorem erase_eq_take_drop [DecidableEq β] (l : List β) (a : β) :
    l.erase a = l.take (l.idxOf a) ++ l.drop (l.idxOf a + 1) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    by_cases h : b = a
    · simp [h]
    · simp [h, ih]

@[fun_prop] theorem prim_erase [DecidableEq β] {f : α → List β} {g : α → β} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => (f x).erase (g x) := by
  simp only [erase_eq_take_drop]
  fun_prop

@[fun_prop] theorem prim_getLast? {f : α → List β} (hf : Primrec f) :
    Primrec fun x => (f x).getLast? := by
  simp only [List.getLast?_eq_head?_reverse]
  fun_prop

theorem min?_eq (l : List ℕ) : l.min? = l.head?.map fun a => l.tail.foldl (fun b c => min b c) a := by
  cases l <;> rfl

theorem max?_eq (l : List ℕ) : l.max? = l.head?.map fun a => l.tail.foldl (fun b c => max b c) a := by
  cases l <;> rfl

@[fun_prop] theorem prim_min? {f : α → List ℕ} (hf : Primrec f) : Primrec fun x => (f x).min? := by
  simp only [min?_eq]
  fun_prop

@[fun_prop] theorem prim_max? {f : α → List ℕ} (hf : Primrec f) : Primrec fun x => (f x).max? := by
  simp only [max?_eq]
  fun_prop

@[fun_prop] theorem prim_insert [DecidableEq β] {f : α → List β} {g : α → β} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => (f x).insert (g x) := by
  have : Primrec fun x => if g x ∈ f x then f x else g x :: f x := by fun_prop
  exact this.of_eq fun x => (List.insert_eq_ite _ _).symm

@[fun_prop] theorem prim_product {f : α → List β} {g : α → List γ} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => (f x) ×ˢ (g x) := by
  have : Primrec fun x => (f x).flatMap fun a => (g x).map (Prod.mk a) := by fun_prop
  exact this.of_eq fun x => rfl

@[fun_prop] theorem prim_sqrt {f : α → ℕ} (hf : Primrec f) : Primrec fun x => (f x).sqrt :=
  Primrec.nat_sqrt.comp hf

@[fun_prop] theorem prim_findGreatest {f : α → ℕ} {p : α → ℕ → Prop} [DecidableRel p]
    (hf : Primrec f) (hp : PrimrecPred fun y : α × ℕ => p y.1 y.2) :
    Primrec fun x => Nat.findGreatest (p x) (f x) :=
  Primrec.nat_findGreatest hf hp

theorem gcd_eq_findGreatest (m n : ℕ) :
    Nat.gcd m n = Nat.findGreatest (fun d => m % d = 0 ∧ n % d = 0) (m + n) := by
  symm
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, fun _ => ⟨Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left m n),
    Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right m n)⟩, fun k hk _ ⟨hm, hn⟩ => ?_⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact (Nat.gcd_le_left n hm).trans (Nat.le_add_right m n)
  · have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hm) (Nat.dvd_of_mod_eq_zero hn)
    rcases Nat.eq_zero_or_pos (Nat.gcd m n) with h0 | hpos
    · rw [Nat.gcd_eq_zero_iff] at h0
      omega
    · exact absurd (Nat.le_of_dvd hpos hd) (by omega)

@[fun_prop] theorem prim_gcd {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => Nat.gcd (f x) (g x) := by
  simp only [gcd_eq_findGreatest]
  fun_prop

@[fun_prop] theorem prim_lcm {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => Nat.lcm (f x) (g x) := by
  unfold Nat.lcm
  fun_prop

theorem log_eq_findGreatest (b n : ℕ) :
    Nat.log b n = if 1 < b then Nat.findGreatest (fun k => b ^ k ≤ n) n else 0 := by
  split
  · rename_i hb
    symm
    rw [Nat.findGreatest_eq_iff]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨by simp, fun h => by simp at h, fun k _ _ h => ?_⟩
      exact absurd h (by have := Nat.pow_pos (n := k) (by omega : 0 < b); omega)
    · refine ⟨Nat.log_le_self b n, fun _ => Nat.pow_log_le_self b (by omega),
        fun k hk _ h => ?_⟩
      exact absurd ((Nat.le_log_iff_pow_le hb (by omega)).2 h) (by omega)
  · exact Nat.log_eq_zero_iff.2 (Or.inr (by omega))

@[fun_prop] theorem prim_log {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => Nat.log (f x) (g x) := by
  simp only [log_eq_findGreatest]
  fun_prop

end Gaps

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
