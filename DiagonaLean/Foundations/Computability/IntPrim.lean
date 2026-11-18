/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.Prim
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Integer arithmetic is primitive recursive

Mathlib makes `ℤ` `Primcodable` (`Primcodable.ofDenumerable`): `n ≥ 0` has code `2 * n` and
`Int.negSucc n` code `2 * n + 1`, but gives no lemmas about its arithmetic. Every integer is
`p - q` for the naturals `p = z.toNat` and `q = (-z).toNat`, both read off the code
(`toNat_eq`, `negToNat_eq`); conversely `p - q` is built by a case split (`ofPair_eq`). The
operations `+`, `*`, `-`, negation, `≤`, `<`, `natAbs` and powers then reduce to arithmetic on `ℕ`,
and all have `fun_prop` lemmas.
-/

namespace DiagonaLean.Foundations.Computability

open Encodable

/-- The cast `ℕ → ℤ` is primitive recursive: the code of `(n : ℤ)` is `2 * n`. -/
theorem intCast_primrec : Primrec (fun n : ℕ => (n : ℤ)) :=
  Primrec.encode_iff.1 ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq fun _ => rfl)

theorem negSucc_primrec : Primrec Int.negSucc :=
  Primrec.encode_iff.1 ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
    Primrec.id) (Primrec.const 1)).of_eq fun _ => rfl)

theorem toNat_eq (z : ℤ) : z.toNat = if encode z % 2 = 0 then encode z / 2 else 0 := by
  cases z with
  | ofNat n => show n = if 2 * n % 2 = 0 then 2 * n / 2 else 0; simp
  | negSucc n => show 0 = if (2 * n + 1) % 2 = 0 then (2 * n + 1) / 2 else 0; simp [Nat.add_mod]

theorem negToNat_eq (z : ℤ) : (-z).toNat = if encode z % 2 = 0 then 0 else encode z / 2 + 1 := by
  cases z with
  | ofNat n =>
    show (-(n : ℤ)).toNat = if 2 * n % 2 = 0 then 0 else 2 * n / 2 + 1; simp
  | negSucc n =>
    show (-(Int.negSucc n)).toNat = if (2 * n + 1) % 2 = 0 then 0 else (2 * n + 1) / 2 + 1
    simp [Nat.add_mod, Int.neg_negSucc]; omega

theorem ofPair_eq (p q : ℕ) :
    ((p : ℤ) - q) = if q ≤ p then (((p - q : ℕ)) : ℤ) else Int.negSucc (q - p - 1) := by
  split
  · omega
  · rw [Int.negSucc_eq]; omega

theorem eq_toNat_sub (z : ℤ) : z = (z.toNat : ℤ) - ((-z).toNat : ℤ) := by omega

section Prim

variable {α : Type*} [Primcodable α]

@[fun_prop] theorem prim_intCast {f : α → ℕ} (hf : Primrec f) :
    Primrec fun x => ((f x : ℕ) : ℤ) := intCast_primrec.comp hf

@[fun_prop] theorem prim_negSucc {f : α → ℕ} (hf : Primrec f) :
    Primrec fun x => Int.negSucc (f x) := negSucc_primrec.comp hf

theorem int_toNat_primrec : Primrec Int.toNat := by
  have : Primrec fun z : ℤ => if encode z % 2 = 0 then encode z / 2 else 0 := by fun_prop
  exact this.of_eq fun z => (toNat_eq z).symm

theorem int_negToNat_primrec : Primrec fun z : ℤ => (-z).toNat := by
  have : Primrec fun z : ℤ => if encode z % 2 = 0 then 0 else encode z / 2 + 1 := by fun_prop
  exact this.of_eq fun z => (negToNat_eq z).symm

@[fun_prop] theorem prim_toNat {f : α → ℤ} (hf : Primrec f) : Primrec fun x => (f x).toNat :=
  int_toNat_primrec.comp hf

/-- `p - q`, for naturals `p` and `q`, as an integer. -/
@[fun_prop] theorem prim_natSub {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => ((f x : ℕ) : ℤ) - ((g x : ℕ) : ℤ) := by
  have : Primrec fun x => if g x ≤ f x then (((f x - g x : ℕ)) : ℤ)
      else Int.negSucc (g x - f x - 1) := by fun_prop
  exact this.of_eq fun x => (ofPair_eq _ _).symm

@[fun_prop] theorem prim_intNeg {f : α → ℤ} (hf : Primrec f) : Primrec fun x => -f x := by
  have : Primrec fun x => (((-f x).toNat : ℕ) : ℤ) - (((f x).toNat : ℕ) : ℤ) :=
    prim_natSub (int_negToNat_primrec.comp hf) (prim_toNat hf)
  exact this.of_eq fun x => by omega

@[fun_prop] theorem prim_intAdd {f g : α → ℤ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x + g x := by
  have hf' := int_negToNat_primrec.comp hf
  have hg' := int_negToNat_primrec.comp hg
  have : Primrec fun x => (((f x).toNat + (g x).toNat : ℕ) : ℤ) -
      (((-f x).toNat + (-g x).toNat : ℕ) : ℤ) := by fun_prop
  exact this.of_eq fun x => by omega

@[fun_prop] theorem prim_intSub {f g : α → ℤ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x - g x :=
  (prim_intAdd hf (prim_intNeg hg)).of_eq fun _ => (Int.sub_eq_add_neg).symm

@[fun_prop] theorem prim_intMul {f g : α → ℤ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x * g x := by
  have hf' := int_negToNat_primrec.comp hf
  have hg' := int_negToNat_primrec.comp hg
  have : Primrec fun x =>
      (((f x).toNat * (g x).toNat + (-f x).toNat * (-g x).toNat : ℕ) : ℤ) -
      (((f x).toNat * (-g x).toNat + (-f x).toNat * (g x).toNat : ℕ) : ℤ) := by fun_prop
  refine this.of_eq fun x => ?_
  conv_rhs => rw [eq_toNat_sub (f x), eq_toNat_sub (g x)]
  push_cast; ring

@[fun_prop] theorem prim_natAbs {f : α → ℤ} (hf : Primrec f) : Primrec fun x => (f x).natAbs := by
  have hf' := int_negToNat_primrec.comp hf
  have : Primrec fun x => (f x).toNat + (-f x).toNat := by fun_prop
  exact this.of_eq fun x => by omega

@[fun_prop] theorem pred_intLe {f g : α → ℤ} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun x => f x ≤ g x := by
  have hf' := int_negToNat_primrec.comp hf
  have hg' := int_negToNat_primrec.comp hg
  have : PrimrecPred fun x => (f x).toNat + (-g x).toNat ≤ (g x).toNat + (-f x).toNat := by
    fun_prop
  exact this.of_eq fun x => by omega

@[fun_prop] theorem pred_intLt {f g : α → ℤ} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun x => f x < g x :=
  (pred_intLe (prim_intAdd hf (Primrec.const 1)) hg).of_eq fun _ => Int.add_one_le_iff

theorem int_pow_eq_iterate (z : ℤ) (k : ℕ) : z ^ k = (fun y => y * z)^[k] 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ← ih, pow_succ]

@[fun_prop] theorem prim_intPow {f : α → ℤ} {g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x ^ g x := by
  have : Primrec fun x => (fun y => y * f x)^[g x] 1 := by fun_prop
  exact this.of_eq fun x => (int_pow_eq_iterate _ _).symm

end Prim

end DiagonaLean.Foundations.Computability
