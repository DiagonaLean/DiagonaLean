/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MatMort.Reductions.PCP_to_MatMort
import DiagonaLean.PCP.Primrec
import DiagonaLean.Foundations.Computability.FinsetPrim
import DiagonaLean.Foundations.Computability.IntPrim
import DiagonaLean.Foundations.Computability.MatrixPrim

@[expose] public section

/-! # The reduction from PCP to matrix mortality is primitive recursive

Matrices are `Primcodable`, and a matrix literal `!![…]` with primitive recursive entries is
primitive recursive (`MatrixPrim.lean`). The entries of the reduction's matrices are integers
computed from base-10 words by integer arithmetic, which is primitive recursive (`IntPrim.lean`),
so `fun_prop` proves the matrix of a pair of words primitive recursive directly
(`prim_stringPairToW`). The image `MatImage K` is
`toFinset` of an explicit list (`matImage_eq`), and finite sets are `Primcodable`
(`Finset.primcodable`), so the reduction is primitive recursive (`matImage_primrec`).
-/

namespace DiagonaLean.MatMort.Reduction

open DiagonaLean.Foundations.Computability DiagonaLean.PCP

section Prim

variable {α : Type} [Primcodable α]

@[fun_prop] theorem prim_wordToInt {f : α → List S123} (hf : Primrec f) :
    Primrec fun x => wordToInt (f x) := by
  unfold wordToInt; fun_prop

@[fun_prop] theorem prim_shift {f : α → ℕ} (hf : Primrec f) : Primrec fun x => shift (f x) := by
  unfold shift; fun_prop

/-- The matrix of a pair of words is primitive recursive in the words. -/
@[fun_prop] theorem prim_stringPairToW {f g : α → List S123} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => StringPairToW (f x) (g x) := by
  unfold StringPairToW W'; fun_prop

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
