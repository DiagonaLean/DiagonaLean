/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.Inequality
import DiagonaLean.Foundations.KleeneAlgebra.MachineEncoding.Halting
import DiagonaLean.Foundations.Computability.Prim

@[expose] public section

/-! # Expressions as natural numbers

`rc` codes an expression as a natural number, so that its constructors are plain arithmetic, and
the `prim` tactic learns to handle those constructors.
-/

namespace DiagonaLean.Foundations.KleeneAlgebra

open RExp DiagonaLean.Foundations.Computability

/-- The code of a letter of the doubled alphabet. -/
def symC : ℕ ⊕ ℕ → ℕ
  | .inl a => 2 * a
  | .inr a => 2 * a + 1

/-- `symC` is injective. -/
theorem symC_injective : Function.Injective symC := by
  rintro (a | a) (b | b) h <;> simp only [symC] at h <;> first | omega | (congr 1; omega)

/-- `symC` is surjective. -/
theorem symC_surjective : Function.Surjective symC := fun n => by
  rcases Nat.even_or_odd' n with ⟨a, rfl | rfl⟩
  · exact ⟨.inl a, rfl⟩
  · exact ⟨.inr a, rfl⟩

/-- The code of `zero`. -/
def cz : ℕ := Nat.pair 0 0
/-- The code of `one`. -/
def co : ℕ := Nat.pair 1 0
/-- The code of `sym s`, given the code `s` of the letter. -/
def cs (s : ℕ) : ℕ := Nat.pair 2 s
/-- The code of `plus e f`, given the codes of `e` and `f`. -/
def cp (a b : ℕ) : ℕ := Nat.pair 3 (Nat.pair a b)
/-- The code of `mul e f`, given the codes of `e` and `f`. -/
def cm (a b : ℕ) : ℕ := Nat.pair 4 (Nat.pair a b)
/-- The code of `star e`, given the code of `e`. -/
def ct (a : ℕ) : ℕ := Nat.pair 5 a

/-- The code of an expression. -/
def rc : RExp (ℕ ⊕ ℕ) → ℕ
  | zero => cz
  | one => co
  | sym x => cs (symC x)
  | plus e f => cp (rc e) (rc f)
  | mul e f => cm (rc e) (rc f)
  | RExp.star e => ct (rc e)

/-- `rc` is injective. -/
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

section Prim

variable {α : Type*} [Primcodable α]

/-- `cs` applied to a primitive recursive function is primitive recursive. -/
theorem prim_cs {f : α → ℕ} (hf : Primrec f) : Primrec fun x => cs (f x) :=
  prim_natPair (Primrec.const 2) hf

/-- `cp` applied to primitive recursive functions is primitive recursive. -/
theorem prim_cp {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => cp (f x) (g x) := prim_natPair (Primrec.const 3) (prim_natPair hf hg)

/-- `cm` applied to primitive recursive functions is primitive recursive. -/
theorem prim_cm {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => cm (f x) (g x) := prim_natPair (Primrec.const 4) (prim_natPair hf hg)

/-- `ct` applied to a primitive recursive function is primitive recursive. -/
theorem prim_ct {f : α → ℕ} (hf : Primrec f) : Primrec fun x => ct (f x) :=
  prim_natPair (Primrec.const 5) hf

end Prim

macro_rules
  | `(tactic| prim_step) => `(tactic| with_reducible first
    | apply prim_cs
    | apply prim_cp
    | apply prim_cm
    | apply prim_ct)

end DiagonaLean.Foundations.KleeneAlgebra
