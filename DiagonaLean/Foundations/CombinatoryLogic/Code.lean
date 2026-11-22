/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Cslib.Languages.CombinatoryLogic.Recursion
import DiagonaLean.Foundations.Computability.Prim

@[expose] public section

/-! # SKI terms as natural numbers

`skc` codes an SKI term as a natural number, so that application is plain arithmetic, and registers
the lemmas for it with `fun_prop`. The code of the Church numeral `toChurch n` is primitive
recursive in `n` (`skc_toChurch_prim`).
-/

namespace DiagonaLean.Foundations.CombinatoryLogic

open Cslib SKI DiagonaLean.Foundations.Computability

/-- The code of `S`. -/
def cS : ℕ := Nat.pair 0 0
/-- The code of `K`. -/
def cK : ℕ := Nat.pair 1 0
/-- The code of `I`. -/
def cI : ℕ := Nat.pair 2 0
/-- The code of `x ⬝ y`, given the codes of `x` and `y`. -/
def ca (a b : ℕ) : ℕ := Nat.pair 3 (Nat.pair a b)

/-- The code of an SKI term. -/
def skc : SKI → ℕ
  | S => cS
  | K => cK
  | I => cI
  | app x y => ca (skc x) (skc y)

/-- `skc` is injective. -/
theorem skc_injective : Function.Injective skc := by
  intro x
  induction x with
  | S | K | I => intro y h; cases y <;> simp_all [skc, cS, cK, cI, ca, Nat.pair_eq_pair]
  | app x y ihx ihy =>
    intro z h
    cases z <;> simp only [skc, ca, Nat.pair_eq_pair, true_and, cI, Nat.succ_ne_self, false_and, cK,
                    OfNat.ofNat_ne_one, cS, OfNat.ofNat_ne_zero] at h
    rw [ihx h.1, ihy h.2]

section Prim

variable {α : Type*} [Primcodable α]

/-- `ca` applied to primitive recursive functions is primitive recursive. -/
@[fun_prop] theorem prim_ca {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => ca (f x) (g x) := prim_natPair (Primrec.const 3) (prim_natPair hf hg)

end Prim


/-- The code of `toChurch n` is the code of `Zero` with `n` applications of `Succ` in front. -/
theorem skc_toChurch (n : ℕ) :
    skc (toChurch n) = (fun m => ca (skc SKI.Succ) m)^[n] (skc SKI.Zero) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

/-- The code of `toChurch n` is primitive recursive in `n`. -/
theorem skc_toChurch_prim : Primrec fun n => skc (toChurch n) := by
  have h : Primrec fun n : ℕ => (fun m => ca (skc SKI.Succ) m)^[n] (skc SKI.Zero) := by
    fun_prop
  exact h.of_eq fun n => (skc_toChurch n).symm

end DiagonaLean.Foundations.CombinatoryLogic
