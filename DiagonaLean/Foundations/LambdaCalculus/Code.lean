/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import DiagonaLean.Foundations.Computability.Prim

@[expose] public section

/-! # λ-terms as natural numbers

`tc` codes a locally nameless λ-term over the variables `ℕ` as a natural number, so that its
constructors are plain arithmetic, and registers the lemmas for it with `fun_prop`.
`tc` is injective (`tc_injective`).
-/

namespace DiagonaLean.Foundations.LambdaCalculus

open Cslib LambdaCalculus.LocallyNameless.Untyped DiagonaLean.Foundations.Computability

/-- The code of the bound variable `bvar i`. -/
def cb (i : ℕ) : ℕ := Nat.pair 0 i
/-- The code of the free variable `fvar x`. -/
def cf (x : ℕ) : ℕ := Nat.pair 1 x
/-- The code of `abs M`, given the code of `M`. -/
def cl (m : ℕ) : ℕ := Nat.pair 2 m
/-- The code of `app M N`, given the codes of `M` and `N`. -/
def cp (m n : ℕ) : ℕ := Nat.pair 3 (Nat.pair m n)

/-- The code of a λ-term. -/
def tc : Term ℕ → ℕ
  | .bvar i => cb i
  | .fvar x => cf x
  | .abs M => cl (tc M)
  | .app M N => cp (tc M) (tc N)

/-- `tc` is injective. -/
theorem tc_injective : Function.Injective tc := by
  intro M
  induction M with
  | bvar i => intro N h; cases N <;> simp_all [tc, cb, cf, cl, cp, Nat.pair_eq_pair]
  | fvar x => intro N h; cases N <;> simp_all [tc, cb, cf, cl, cp, Nat.pair_eq_pair]
  | abs M ih =>
    intro N h
    cases N <;> simp only [tc, cl, Nat.pair_eq_pair, true_and, cb, OfNat.ofNat_ne_zero, false_and,
                    cf, OfNat.ofNat_ne_one, cp, Nat.reduceEqDiff] at h
    rw [ih h]
  | app M M' ih ih' =>
    intro N h
    cases N <;> simp only [tc, cp, Nat.pair_eq_pair, true_and, cb, OfNat.ofNat_ne_zero, false_and,
                    cf, OfNat.ofNat_ne_one, cl, Nat.succ_ne_self] at h
    rw [ih h.1, ih' h.2]

section Prim

variable {α : Type*} [Primcodable α]

/-- `cb` applied to a primitive recursive function is primitive recursive. -/
@[fun_prop] theorem prim_cb {f : α → ℕ} (hf : Primrec f) : Primrec fun x => cb (f x) :=
  prim_natPair (Primrec.const 0) hf

/-- `cf` applied to a primitive recursive function is primitive recursive. -/
@[fun_prop] theorem prim_cf {f : α → ℕ} (hf : Primrec f) : Primrec fun x => cf (f x) :=
  prim_natPair (Primrec.const 1) hf

/-- `cl` applied to a primitive recursive function is primitive recursive. -/
@[fun_prop] theorem prim_cl {f : α → ℕ} (hf : Primrec f) : Primrec fun x => cl (f x) :=
  prim_natPair (Primrec.const 2) hf

/-- `cp` applied to primitive recursive functions is primitive recursive. -/
@[fun_prop] theorem prim_cp {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => cp (f x) (g x) := prim_natPair (Primrec.const 3) (prim_natPair hf hg)

end Prim


end DiagonaLean.Foundations.LambdaCalculus
