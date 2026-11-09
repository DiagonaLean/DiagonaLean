/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Reductions.SelfOut_to_Eq
import DiagonaLean.Foundations.Computability.Prim

@[expose] public section

/-! # Expressions as natural numbers

`rc` codes an expression as a natural number, so that its constructors are plain arithmetic, and
the `prim` tactic learns to handle those constructors.
-/

namespace DiagonaLean.KAComm.Reduction

open RExp DiagonaLean.Foundations.Computability

/-- The code of a letter of the doubled alphabet. -/
def symC : ℕ ⊕ ℕ → ℕ
  | .inl a => 2 * a
  | .inr a => 2 * a + 1

theorem symC_injective : Function.Injective symC := by
  rintro (a | a) (b | b) h <;> simp only [symC] at h <;> first | omega | (congr 1; omega)

theorem symC_surjective : Function.Surjective symC := fun n => by
  rcases Nat.even_or_odd' n with ⟨a, rfl | rfl⟩
  · exact ⟨.inl a, rfl⟩
  · exact ⟨.inr a, rfl⟩

/-- `zero`. -/
def cz : ℕ := Nat.pair 0 0
/-- `one`. -/
def co : ℕ := Nat.pair 1 0
/-- `sym`. -/
def cs (s : ℕ) : ℕ := Nat.pair 2 s
/-- `plus`. -/
def cp (a b : ℕ) : ℕ := Nat.pair 3 (Nat.pair a b)
/-- `mul`. -/
def cm (a b : ℕ) : ℕ := Nat.pair 4 (Nat.pair a b)
/-- `star`. -/
def ct (a : ℕ) : ℕ := Nat.pair 5 a

/-- The code of an expression. -/
def rc : RExp (ℕ ⊕ ℕ) → ℕ
  | zero => cz
  | one => co
  | sym x => cs (symC x)
  | plus e f => cp (rc e) (rc f)
  | mul e f => cm (rc e) (rc f)
  | RExp.star e => ct (rc e)

theorem rc_injective : Function.Injective rc := by
  intro e
  induction e with
  | zero => intro f h; cases f <;> simp_all [rc, cz, co, cs, cp, cm, ct, Nat.pair_eq_pair]
  | one => intro f h; cases f <;> simp_all [rc, cz, co, cs, cp, cm, ct, Nat.pair_eq_pair]
  | sym x =>
    intro f h
    cases f <;> simp [rc, cz, co, cs, cp, cm, ct, Nat.pair_eq_pair] at h
    rw [symC_injective h]
  | plus e f ihe ihf =>
    intro g h
    cases g <;> simp [rc, cz, co, cs, cp, cm, ct, Nat.pair_eq_pair] at h
    rw [ihe h.1, ihf h.2]
  | mul e f ihe ihf =>
    intro g h
    cases g <;> simp [rc, cz, co, cs, cp, cm, ct, Nat.pair_eq_pair] at h
    rw [ihe h.1, ihf h.2]
  | star e ih =>
    intro g h
    cases g <;> simp [rc, cz, co, cs, cp, cm, ct, Nat.pair_eq_pair] at h
    rw [ih h]

/-! ### `Primrec` lemmas -/

section Prim

variable {α : Type*} [Primcodable α]

theorem prim_cs {f : α → ℕ} (hf : Primrec f) : Primrec fun x => cs (f x) :=
  prim_natPair (Primrec.const 2) hf

theorem prim_cp {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => cp (f x) (g x) := prim_natPair (Primrec.const 3) (prim_natPair hf hg)

theorem prim_cm {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => cm (f x) (g x) := prim_natPair (Primrec.const 4) (prim_natPair hf hg)

theorem prim_ct {f : α → ℕ} (hf : Primrec f) : Primrec fun x => ct (f x) :=
  prim_natPair (Primrec.const 5) hf

end Prim

macro_rules
  | `(tactic| prim_step) => `(tactic| with_reducible first
    | apply prim_cs
    | apply prim_cp
    | apply prim_cm
    | apply prim_ct)

end DiagonaLean.KAComm.Reduction
