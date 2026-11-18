/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MatMort.Reductions.PCP_to_MatMort
import DiagonaLean.PCP.Primrec
import DiagonaLean.Foundations.Computability.FinsetPrim

@[expose] public section

/-! # The reduction from PCP to matrix mortality is primitive recursive

Matrices `Matrix (Fin m) (Fin n) β` are `Primcodable` as the functions `Fin m → Fin n → β` they
are, and a matrix-valued function is primitive recursive when each of its entries is
(`prim_matrix`). The entries of the reduction's matrices are nonnegative integers given by base-10
words, primitive recursive through the cast `ℕ → ℤ` (`prim_intCast`). The image `MatImage K` is
`toFinset` of an explicit list (`matImage_eq`), and finite sets are `Primcodable`
(`Finset.primcodable`), so the reduction is primitive recursive (`matImage_primrec`).
-/

namespace DiagonaLean.MatMort.Reduction

open DiagonaLean.Foundations.Computability DiagonaLean.PCP

/-- Matrices are `Primcodable`, as functions on their indices. -/
instance matrixPrimcodable {m n : ℕ} {β : Type} [Primcodable β] :
    Primcodable (Matrix (Fin m) (Fin n) β) :=
  inferInstanceAs (Primcodable (Fin m → Fin n → β))

section Prim

variable {α : Type} [Primcodable α]

/-- A function into `Fin n → σ` is primitive recursive when each of its components is. -/
theorem prim_finFun {n : ℕ} {σ : Type} [Primcodable σ] {f : α → Fin n → σ}
    (h : ∀ i, Primrec fun a => f a i) : Primrec f :=
  Primrec.fin_curry.2 ((Primrec.fin_curry₁ (f := fun i a => f a i)).2 h |>.comp Primrec.snd
    Primrec.fst)

/-- A matrix-valued function is primitive recursive when each of its entries is. -/
theorem prim_matrix {m n : ℕ} {β : Type} [Primcodable β] {f : α → Matrix (Fin m) (Fin n) β}
    (h : ∀ i j, Primrec fun a => f a i j) : Primrec f :=
  prim_finFun (σ := Fin n → β) fun i => prim_finFun fun j => h i j

/-- The cast `ℕ → ℤ` is primitive recursive: the code of `(n : ℤ)` is `2 * n`. -/
theorem intCast_primrec : Primrec (fun n : ℕ => (n : ℤ)) :=
  Primrec.encode_iff.1 ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq fun _ => rfl)

@[fun_prop] theorem prim_intCast {f : α → ℕ} (hf : Primrec f) :
    Primrec fun x => ((f x : ℕ) : ℤ) := intCast_primrec.comp hf

/-- Powers of `10` in `ℤ`, through the cast from `ℕ`. -/
@[fun_prop] theorem prim_intPow10 {f : α → ℕ} (hf : Primrec f) :
    Primrec fun x => (10 : ℤ) ^ f x :=
  (prim_intCast (prim_pow (Primrec.const 10) hf)).of_eq fun x => by push_cast; rfl

@[fun_prop] theorem prim_finSucc {n : ℕ} {f : α → Fin n} (hf : Primrec f) :
    Primrec fun x => (f x).succ := Primrec.fin_succ.comp hf

end Prim

/-- `wordToInt` on naturals. -/
def wordToNat (w : List S123) : ℕ := w.foldl (fun acc d => acc * 10 + (d.val + 1)) 0

theorem wordToInt_eq (w : List S123) : wordToInt w = (wordToNat w : ℤ) := by
  suffices h : ∀ acc : ℕ, w.foldl (fun (acc : ℤ) d => acc * 10 + (d.val + 1)) (acc : ℤ) =
      ((w.foldl (fun acc d => acc * 10 + (d.val + 1)) acc : ℕ) : ℤ) from h 0
  induction w with
  | nil => intro acc; rfl
  | cons d w ih => intro acc; simp only [List.foldl_cons]; rw [← ih]; push_cast; rfl

theorem shift_eq (n : ℕ) : shift n = ((10 ^ n : ℕ) : ℤ) := by simp [shift]

section Prim

variable {α : Type} [Primcodable α]

@[fun_prop] theorem prim_wordToNat {f : α → List S123} (hf : Primrec f) :
    Primrec fun x => wordToNat (f x) := by
  unfold wordToNat; fun_prop

/-- The matrix of a pair of words is primitive recursive in the words. -/
@[fun_prop] theorem prim_stringPairToW {f g : α → List S123} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => StringPairToW (f x) (g x) := by
  refine prim_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [StringPairToW, W', wordToInt_eq, shift_eq, -Nat.cast_pow, -Nat.cast_ofNat] <;> fun_prop

end Prim

/-- `MatImage K` is `toFinset` of an explicit list. -/
theorem matImage_eq (K : Stack S23) : MatImage K =
    ([S, T] ++ K.map (fun tile => StringPairToW (liftS23 tile.top) (liftS23 tile.bot)) ++
      K.map (fun tile => StringPairToW (liftS23 tile.top) (one₁₂₃ :: liftS23 tile.bot))).toFinset := by
  ext M
  simp [MatImage]

/-- **The reduction from PCP to matrix mortality is primitive recursive.** -/
theorem matImage_primrec : Primrec MatImage := by
  have h : Primrec fun K : Stack S23 =>
      ([S, T] ++ K.map (fun tile => StringPairToW (liftS23 tile.top) (liftS23 tile.bot)) ++
        K.map (fun tile => StringPairToW (liftS23 tile.top) (one₁₂₃ :: liftS23 tile.bot))).toFinset := by
    unfold liftS23
    fun_prop
  exact h.of_eq fun K => (matImage_eq K).symm

/-- The function of the reduction `pcpReducesMatMort` is primitive recursive. -/
theorem pcpReducesMatMort_primrec : Primrec pcpReducesMatMort.f := matImage_primrec

end DiagonaLean.MatMort.Reduction
