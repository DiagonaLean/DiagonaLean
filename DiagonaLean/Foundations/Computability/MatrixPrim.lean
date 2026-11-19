/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.Prim
import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-! # Vectors `Fin n → σ` and matrices are primitive recursive data

Mathlib makes `Fin n → σ` `Primcodable` (through `List.Vector`), and a function into it is
primitive recursive exactly when each of its components is (`prim_finFun`). Matrices
`Matrix (Fin m) (Fin n) β` are `Primcodable` as the functions `Fin m → Fin n → β` they are
(`matrixPrimcodable`).

The vector literals `![a, b, …]` (`Matrix.vecCons`, `Matrix.vecEmpty`) and `Matrix.of` have
`fun_prop` lemmas, so a matrix written as `!![a, b; c, d]` with primitive recursive entries is
proved primitive recursive by `fun_prop` alone, with no split into entries.
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

end Prim

end DiagonaLean.Foundations.Computability
