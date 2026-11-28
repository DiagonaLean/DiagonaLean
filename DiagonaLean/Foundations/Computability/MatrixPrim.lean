/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.IntPrim
import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-! # Vectors `Fin n → σ` and matrices are primitive recursive data

Mathlib makes `Fin n → σ` `Primcodable` (through `List.Vector`), and a function into it is
primitive recursive exactly when each of its components is (`prim_finFun`). Matrices
`Matrix (Fin m) (Fin n) β` are `Primcodable` as the functions `Fin m → Fin n → β` they are
(`matrixPrimcodable`).

The vector literals `![a, b, …]` (`Matrix.vecCons`, `Matrix.vecEmpty`) and `Matrix.of` have
`fun_prop` lemmas, so a matrix written as `!![a, b; c, d]` with primitive recursive entries is
proved primitive recursive by `fun_prop` alone, with no split into entries. Products of integer
square matrices, and of lists of them, are primitive recursive (`prim_intMatMul`,
`prim_intMatProd`).
-/

namespace DiagonaLean.Foundations.Computability

/-- Matrices are `Primcodable`, as functions on their indices. -/
instance matrixPrimcodable {m n : ℕ} {β : Type*} [Primcodable β] :
    Primcodable (Matrix (Fin m) (Fin n) β) :=
  inferInstanceAs (Primcodable (Fin m → Fin n → β))

section Prim

variable {α σ : Type*} [Primcodable α] [Primcodable σ]

/-- A function into `Fin n → σ` is primitive recursive when each of its components is. This is
`fun_prop`'s rule for a `fun i => …` over `Fin n`. -/
@[fun_prop] theorem prim_finFun {n : ℕ} {f : α → Fin n → σ} (h : ∀ i, Primrec fun a => f a i) :
    Primrec f :=
  Primrec.fin_curry.2 ((Primrec.fin_curry₁ (f := fun i a => f a i)).2 h |>.comp Primrec.snd
    Primrec.fst)

/-- A matrix-valued function is primitive recursive when each of its entries is. -/
theorem prim_matrix {m n : ℕ} {β : Type*} [Primcodable β] {f : α → Matrix (Fin m) (Fin n) β}
    (h : ∀ i j, Primrec fun a => f a i j) : Primrec f :=
  prim_finFun (σ := Fin n → β) fun i => prim_finFun fun j => h i j

/-- Applying a primitive recursive vector to a primitive recursive index. -/
theorem prim_finApp {n : ℕ} {f : α → Fin n → σ} {g : α → Fin n} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => f x (g x) :=
  Primrec.fin_app.comp hf hg

@[fun_prop] theorem prim_vecEmpty : Primrec fun _ : α => (![] : Fin 0 → σ) :=
  Primrec.const _

@[fun_prop] theorem prim_vecCons {n : ℕ} {f : α → σ} {g : α → Fin n → σ} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => Matrix.vecCons (f x) (g x) :=
  prim_finFun fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hf
    · simpa using prim_finApp hg (Primrec.const j)

@[fun_prop] theorem prim_matrixOf {m n : ℕ} {β : Type*} [Primcodable β]
    {f : α → Fin m → Fin n → β} (hf : Primrec f) : Primrec fun x => Matrix.of (f x) := hf

@[fun_prop] theorem prim_ofFn {n : ℕ} {f : α → Fin n → σ} (hf : Primrec f) :
    Primrec fun x => List.ofFn (f x) :=
  Primrec.list_ofFn fun i => prim_finApp hf (Primrec.const i)

@[fun_prop] theorem prim_finSucc {n : ℕ} {f : α → Fin n} (hf : Primrec f) :
    Primrec fun x => (f x).succ := Primrec.fin_succ.comp hf

/-- **The product of two integer square matrices is primitive recursive**: each entry is a sum of
`n` products of entries. -/
@[fun_prop] theorem prim_intMatMul {n : ℕ} {f g : α → Matrix (Fin n) (Fin n) ℤ} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => f x * g x := by
  refine prim_matrix fun i k => ?_
  have hv : Primrec fun x (j : Fin n) => f x i j * g x j k := prim_finFun fun j =>
    prim_intMul (prim_finApp (prim_finApp hf (.const i)) (.const j))
      (prim_finApp (prim_finApp hg (.const j)) (.const k))
  have : Primrec fun x => (List.ofFn fun j => f x i j * g x j k).foldr (· + ·) 0 :=
    Primrec.list_foldr (prim_ofFn hv) (.const 0)
      (prim_intAdd (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
  exact this.of_eq fun x => by simp [Matrix.mul_apply, ← List.sum_eq_foldr, List.sum_ofFn]

/-- **The product of a list of integer square matrices is primitive recursive.** -/
@[fun_prop] theorem prim_intMatProd {n : ℕ} {f : α → List (Matrix (Fin n) (Fin n) ℤ)}
    (hf : Primrec f) : Primrec fun x => (f x).prod := by
  have : Primrec fun x => (f x).foldr (· * ·) 1 :=
    Primrec.list_foldr hf (Primrec.const 1)
      (prim_intMatMul (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact this.of_eq fun x => List.prod_eq_foldr.symm

end Prim

end DiagonaLean.Foundations.Computability
