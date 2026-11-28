/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.Computability.ListHalt
import DiagonaLean.Foundations.Computability.Reaches

@[expose] public section

/-! # Halting of list machines given by a table is recursively enumerable

A configuration of a list machine is a tuple `(q, l, c, r)` of numbers and lists (`toTup`), and
one step of the machine of a program on tuples (`stepTup`) is primitive recursive in the program
and the tuple. The machine halts iff it reaches a tuple whose state and head cell have no rule
(`halts_iff_tup`). So halting is recursively enumerable over every alphabet with a `Primcodable`
type and decidable equality (`ListHalt.rePred`): search for the number of steps
(`REPred.of_reaches`). With `ListHalt.haltHard` it is as hard as the halting problem and no
harder.

## Main statements

* `next_eq_stepTup`, `halts_iff_tup`: the machine of a program on tuples.
* `ListHalt.rePred`: halting of list machines given by a table is recursively enumerable.
-/

namespace DiagonaLean.Foundations.Computability.ListHalt

open DiagonaLean.Foundations.Computability.ListMachine

variable {Γ : Type} [DecidableEq Γ]

/-- A configuration as a tuple `(q, l, c, r)`: the state, the cells left of the head, the head
cell and the cells right of the head. -/
abbrev Tup (Γ : Type) := ℕ × List Γ × Γ × List Γ

/-- The tuple of a configuration. -/
def toTup (k : Cfg ℕ Γ) : Tup Γ := (k.q, k.l, k.c, k.r)

/-- The configuration of a tuple. -/
def ofTup (t : Tup Γ) : Cfg ℕ Γ := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩

/-- One step of the machine of `p` on tuples, from the rule for the state and the head cell. -/
def stepTup (p : Program Γ) (bl : Γ) (t : Tup Γ) : Option (Tup Γ) :=
  (rule? p t.1 t.2.2.1).bind fun r =>
    if r.1 = .stay then some (r.2.1, t.2.1, r.2.2, t.2.2.2)
    else if r.1 = .right then some (r.2.1, r.2.2 :: t.2.1, t.2.2.2.headD bl, t.2.2.2.tail)
    else t.2.1.head?.map fun d => (r.2.1, t.2.1.tail, d, r.2.2 :: t.2.2.2)

/-- A step of the machine of `p` is a step on tuples. -/
theorem next_eq_stepTup (p : Program Γ) (bl : Γ) (k : Cfg ℕ Γ) :
    next (act p) bl k = (stepTup p bl (toTup k)).map ofTup := by
  obtain ⟨q, l, c, r⟩ := k
  simp only [next, act, stepTup, toTup]
  cases h : rule? p q c with
  | none => simp
  | some x =>
    obtain ⟨m, q', b⟩ := x
    cases m with
    | stay => simp [toAct, ofTup]
    | right => simp [toAct, ofTup]
    | left => cases l <;> simp [toAct, ofTup]

/-- The machine of `p` halts in a state and on a head cell iff they have no rule. -/
theorem act_eq_halt_iff (p : Program Γ) (q : ℕ) (c : Γ) :
    act p q c = .halt ↔ rule? p q c = none := by
  unfold act
  cases rule? p q c with
  | none => simp
  | some x => simp only [Option.map_some, Option.getD_some, toAct]; split_ifs <;> simp

/-- The machine of `p` halts from `k` iff, on tuples, it reaches a tuple whose state and head
cell have no rule. -/
theorem halts_iff_tup (p : Program Γ) (bl : Γ) (k : Cfg ℕ Γ) :
    Halts (act p) bl k ↔ ∃ t, Relation.ReflTransGen (fun x y => stepTup p bl x = some y)
      (toTup k) t ∧ rule? p t.1 t.2.2.1 = none := by
  constructor
  · rintro ⟨k', h, hk'⟩
    refine ⟨toTup k', h.lift toTup fun a b hab => ?_, (act_eq_halt_iff p _ _).1 hk'⟩
    rw [next_eq_stepTup, Option.map_eq_some_iff] at hab
    obtain ⟨t, ht, rfl⟩ := hab
    exact ht
  · rintro ⟨t, h, ht⟩
    refine ⟨ofTup t, h.lift ofTup fun a b hab => ?_, (act_eq_halt_iff p _ _).2 ht⟩
    change next (act p) bl (ofTup a) = some (ofTup b)
    rw [next_eq_stepTup, show toTup (ofTup a) = a from rfl, hab]
    rfl

derive_primrec stepTup [Primcodable Γ]

/-- **Halting of list machines given by a table is recursively enumerable**: search for the
number of steps. -/
theorem rePred [Primcodable Γ] (bl : Γ) : REPred (DecisionProblem bl) :=
  REPred.of_eq (REPred.of_reaches (step := fun x => stepTup x.1 bl)
    (start := fun x : Program Γ × ℕ × List Γ => toTup (start bl x.2.1 x.2.2))
    (stop := fun x t => rule? x.1 t.1 t.2.2.1 = none) (by fun_prop)
    (by unfold toTup start; fun_prop)
    (Primrec.eq.comp (by fun_prop) (.const none))) fun x => (halts_iff_tup x.1 bl _).symm

end DiagonaLean.Foundations.Computability.ListHalt
