/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Aristotle (Harmonic), Prathamesh Turaga, Claude Opus
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Computability.Language
import Mathlib.Tactic
import DiagonaLean.PCP.Reductions.Halt_to_PCP
import DiagonaLean.MatMort.Basic
import DiagonaLean.PCP.Basic
import DiagonaLean.Synthetic.HaltReduction
import DiagonaLean.Synthetic.Tactics.ReduceFromPCP

@[expose] public section

/-! # PCP ⪯_s MatMort

Reduction from the Post Correspondence Problem (PCP) to the Matrix Mortality Problem (MatMort),
following [Paterson1970]. The Matrix Mortality Problem asks whether a finite set of `3 × 3` integer
matrices admits a finite product, with repetitions allowed, equal to the zero matrix.

A pair of words `(U, V)` becomes the matrix `stringPairToW U V`, which appends `U` and `V`, read
as base-10 numerals, to the first two coordinates of a row vector. Each tile of a PCP instance `K`
gives two such matrices, one with a marker digit on its bottom word (`tileMats`). `S * P * T = 0`
when `[1, 0, 1] * P = [h, h, 1]` (`S_prod_T_eq_zero`), and every zero product
contains such a run (`mortal_iff_exists_prod_of_Ws`). The main results are `pcp_iff_matmort` and
the reduction `pcpReducesMatMort`.

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatMort.Reduction
open Matrix Computability DiagonaLean.PCP DiagonaLean.MatMort

/-- The initialization matrix `S`. When left-multiplied by any row vector `[a, b, c]`, it projects
  the first coordinate and sets up the vector `a • [1, 0, 1]`. -/
def S : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1; 0, 0, 0; 0, 0, 0]

/-- The termination matrix `T`. When left-multiplied by `[a, b, c]`, it yields `[a - b, b - a, 0]`,
  which is the zero vector if and only if `a = b`. -/
def T : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -1, 0; -1, 1, 0; 0, 0, 0]

/-- The matrix `W' p q r s` encodes a PCP tile. Using base-10 shifts `p` and `r` and integer values
  `q` and `s`, left-multiplying by this matrix appends the strings to the current accumulated
  integers. -/
def W' (p q r s : ℤ) (_hpq : p > q ∧ q ≥ 0) (_hrs : r > s ∧ s ≥ 0) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![p, 0, 0; 0, r, 0; q, s, 1]

variable (a b c : ℤ)

/-- Multiplying a row vector by `S` results in a scaled version of `[1, 0, 1]` based on the first
  coordinate. -/
theorem row_prod_S : a • !![1, 0, 1] = !![a, b, c] * S := by simp [S]

/-- Multiplying a row vector by `T` computes the difference of the first two coordinates. -/
theorem row_prod_T : (a - b) • !![1, -1, 0] = !![a, b, c] * T := by simp [T]; grind

/-- The tile matrix `W'` is non-singular because its determinant `p * r` is non-zero. -/
theorem non_singular_W (p q r s : ℤ) (hpq : p > q ∧ q ≥ 0) (hrs : r > s ∧ s ≥ 0) :
    det (W' p q r s hpq hrs) ≠ 0 := by
  have hp : p ≠ 0 := by linarith [hpq.1, hpq.2]
  have hr : r ≠ 0 := by linarith [hrs.1, hrs.2]
  have hdet : det (W' p q r s hpq hrs) = p * r := by
    unfold W'
    simp [Matrix.det_fin_three]
  simp only [hdet]
  exact mul_ne_zero hp hr

/-- Nonempty finite sequences of matrices drawn from `Ws`. -/
def wSeq (Ws : Finset (Matrix (Fin 3) (Fin 3) ℤ)) :=
  { is : List (Matrix (Fin 3) (Fin 3) ℤ) | is ≠ [] ∧ ∀ M ∈ is, M ∈ Ws }

/-- The product of a sequence of W-matrices, left-multiplied by `[1,0,1]`. -/
def wProd (is : List (Matrix (Fin 3) (Fin 3) ℤ)) : Matrix (Fin 1) (Fin 3) ℤ :=
  !![(1 : ℤ), 0, 1] * is.prod

/-- If a matrix `P` produces equal coordinates when multiplied by `[1, 0, 1]`, then `S * P * T`
  evaluates to the zero matrix. -/
theorem S_prod_T_eq_zero (P : Matrix (Fin 3) (Fin 3) ℤ) (h : ℤ)
    (hP : !![(1 : ℤ), 0, 1] * P = !![h, h, 1]) : S * P * T = 0 := by
  have e0 : P 0 0 + P 2 0 = h := by
    have := congr_fun (congr_fun hP 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have e1 : P 0 1 + P 2 1 = h := by
    have := congr_fun (congr_fun hP 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have e2 : P 0 2 + P 2 2 = 1 := by
    have := congr_fun (congr_fun hP 0) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have hSP : S * P = !![h, h, 1; 0, 0, 0; 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, Matrix.mul_apply, Fin.sum_univ_three] <;> omega
  rw [hSP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, Matrix.mul_apply, Fin.sum_univ_three]

/-- Multiplying a row vector `v` by `S` gives `v 0 • [1, 0, 1]`. -/
theorem vecMul_S (v : Fin 3 → ℤ) : v ᵥ* S = v 0 • ![1, 0, 1] := by
  ext i; fin_cases i <;> simp [S, vecMul, dotProduct, Fin.sum_univ_three]

/-- Multiplying a row vector `v` by `T` gives `(v 0 - v 1) • [1, -1, 0]`. -/
theorem vecMul_T (v : Fin 3 → ℤ) : v ᵥ* T = (v 0 - v 1) • ![1, -1, 0] := by
  ext i; fin_cases i <;> simp [T, vecMul, dotProduct, Fin.sum_univ_three] <;> ring

/-- Multiplying `[x, y, z]` by `W' p q r s` gives `[p x + q z, r y + s z, z]`. -/
theorem vecMul_W' (x y z p q r s : ℤ) (hpq : p > q ∧ q ≥ 0) (hrs : r > s ∧ s ≥ 0) :
    ![x, y, z] ᵥ* W' p q r s hpq hrs = ![p * x + q * z, r * y + s * z, z] := by
  ext i; fin_cases i <;> simp [W', vecMul, dotProduct, Fin.sum_univ_three] <;> ring

/-- An equation between row vectors gives the same equation between `1 × 3` matrices. -/
theorem row_mul_eq_of_vecMul_eq {P : Matrix (Fin 3) (Fin 3) ℤ} {a b c x y z : ℤ}
    (h : ![a, b, c] ᵥ* P = ![x, y, z]) : !![a, b, c] * P = !![x, y, z] := by
  ext i j
  fin_cases i
  have := congr_fun h j
  fin_cases j <;> simpa [Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_three] using this

/-- The invariant of `mortal_extract` on the current row vector `v`, where `R` lists the `W'`
  matrices read since the last `S`. Either `v = γ • [a, b, 1]` with `a > 0`, `b ≥ 0` and
  `[1, 0, 1] * R.prod = [a, b, 1]`, or `v = δ • [e, f, 0]` with `e > 0 > f`. -/
def ExtractInv (R : List (Matrix (Fin 3) (Fin 3) ℤ)) (v : Fin 3 → ℤ) : Prop :=
  (∃ γ a b : ℤ, γ ≠ 0 ∧ 0 < a ∧ 0 ≤ b ∧ ![1, 0, 1] ᵥ* R.prod = ![a, b, 1] ∧
    v = γ • ![a, b, 1]) ∨
  (∃ δ e f : ℤ, δ ≠ 0 ∧ 0 < e ∧ f < 0 ∧ v = δ • ![e, f, 0])

/-- Under the invariant, the first coordinate of `v` is nonzero, so `v ≠ 0`. -/
theorem ExtractInv.head_ne_zero {R : List (Matrix (Fin 3) (Fin 3) ℤ)} {v : Fin 3 → ℤ}
    (h : ExtractInv R v) : v 0 ≠ 0 := by
  rcases h with ⟨γ, a, b, hγ, ha, -, -, rfl⟩ | ⟨δ, e, f, hδ, he, -, rfl⟩
  · simpa using And.intro hγ ha.ne'
  · simpa using And.intro hδ he.ne'

/-- Multiplying by `S` restores the invariant with no `W'` matrices read. -/
theorem ExtractInv.mul_S {R : List (Matrix (Fin 3) (Fin 3) ℤ)} {v : Fin 3 → ℤ}
    (h : ExtractInv R v) : ExtractInv [] (v ᵥ* S) :=
  Or.inl ⟨v 0, 1, 0, h.head_ne_zero, one_pos, le_rfl, by simp, by simp [vecMul_S]⟩

/-- Multiplying by `T` either finds a nonempty `R` with equal coordinates, or keeps the
  invariant in its second form. -/
theorem ExtractInv.mul_T {R : List (Matrix (Fin 3) (Fin 3) ℤ)} {v : Fin 3 → ℤ}
    (h : ExtractInv R v) :
    (∃ c : ℤ, 0 < c ∧ R ≠ [] ∧ ![1, 0, 1] ᵥ* R.prod = ![c, c, 1]) ∨
      ExtractInv [] (v ᵥ* T) := by
  rcases h with ⟨γ, a, b, hγ, ha, hb, hR, rfl⟩ | ⟨δ, e, f, hδ, he, hf, rfl⟩
  · by_cases hab : a = b
    · subst hab
      refine Or.inl ⟨a, ha, ?_, hR⟩
      rintro rfl
      have := congr_fun hR 1
      simp at this
      omega
    · refine Or.inr (Or.inr ⟨γ * (a - b), 1, -1, mul_ne_zero hγ (sub_ne_zero.mpr hab),
        one_pos, by norm_num, ?_⟩)
      rw [vecMul_T]
      ext i; fin_cases i <;> simp <;> ring
  · refine Or.inr (Or.inr ⟨δ * (e - f), 1, -1, mul_ne_zero hδ (by omega), one_pos,
      by norm_num, ?_⟩)
    rw [vecMul_T]
    ext i; fin_cases i <;> simp <;> ring

/-- Multiplying by a `W'` matrix keeps the invariant, with the matrix appended to `R`. -/
theorem ExtractInv.mul_W' {R : List (Matrix (Fin 3) (Fin 3) ℤ)} {v : Fin 3 → ℤ}
    (h : ExtractInv R v) (p q r s : ℤ) (hpq : p > q ∧ q ≥ 0) (hrs : r > s ∧ s ≥ 0) :
    ExtractInv (R ++ [W' p q r s hpq hrs]) (v ᵥ* W' p q r s hpq hrs) := by
  rcases h with ⟨γ, a, b, hγ, ha, hb, hR, rfl⟩ | ⟨δ, e, f, hδ, he, hf, rfl⟩
  · refine Or.inl ⟨γ, p * a + q, r * b + s, hγ, by nlinarith, by nlinarith, ?_, ?_⟩
    · rw [List.prod_append, List.prod_singleton, ← vecMul_vecMul, hR, vecMul_W']
      simp
    · rw [smul_vecMul, vecMul_W']
      simp
  · refine Or.inr ⟨δ, p * e, r * f, hδ, by nlinarith, by nlinarith, ?_⟩
    rw [smul_vecMul, vecMul_W']
    simp

/-- If `v ᵥ* Ms.prod = 0` for matrices `Ms` drawn from `{S, T} ∪ Ws` and `v` satisfies the
  invariant, then some nonempty run of matrices from `Ws` maps `[1, 0, 1]` to `[c, c, 1]` with
  `c > 0`. -/
private theorem mortal_extract
    (Ws : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hWs : ∀ M ∈ Ws, ∃ (p q r s : ℤ) (hpq : p > q ∧ q ≥ 0) (hrs : r > s ∧ s ≥ 0),
      M = W' p q r s hpq hrs)
    (Ms : List (Matrix (Fin 3) (Fin 3) ℤ))
    (hMem : ∀ M ∈ Ms, M ∈ ({S, T} : Finset (Matrix (Fin 3) (Fin 3) ℤ)) ∪ Ws)
    (v : Fin 3 → ℤ) (R : List (Matrix (Fin 3) (Fin 3) ℤ)) (hRmem : ∀ M ∈ R, M ∈ Ws)
    (hInv : ExtractInv R v) (hzero : v ᵥ* Ms.prod = 0) :
    ∃ Run : List (Matrix (Fin 3) (Fin 3) ℤ), (∀ M ∈ Run, M ∈ Ws) ∧ Run ≠ [] ∧
      ∃ c : ℤ, 0 < c ∧ ![1, 0, 1] ᵥ* Run.prod = ![c, c, 1] := by
  induction Ms generalizing v R with
  | nil =>
    simp only [List.prod_nil, vecMul_one] at hzero
    exact absurd (congr_fun hzero 0) hInv.head_ne_zero
  | cons M Ms ih =>
    rw [List.prod_cons, ← vecMul_vecMul] at hzero
    have hMs : ∀ N ∈ Ms, N ∈ ({S, T} : Finset (Matrix (Fin 3) (Fin 3) ℤ)) ∪ Ws :=
      fun N hN => hMem N (List.mem_cons_of_mem _ hN)
    rcases Finset.mem_union.mp (hMem M List.mem_cons_self) with hST | hW
    · rcases Finset.mem_insert.mp hST with rfl | hT
      · exact ih hMs _ [] (by simp) hInv.mul_S hzero
      · rw [Finset.mem_singleton.mp hT] at hzero
        rcases hInv.mul_T with ⟨c, hc, hR, hRprod⟩ | hInv'
        · exact ⟨R, hRmem, hR, c, hc, hRprod⟩
        · exact ih hMs _ [] (by simp) hInv' hzero
    · obtain ⟨p, q, r, s, hpq, hrs, rfl⟩ := hWs M hW
      refine ih hMs _ _ ?_ (hInv.mul_W' p q r s hpq hrs) hzero
      intro N hN
      rcases List.mem_append.mp hN with hN | hN
      · exact hRmem N hN
      · rw [List.mem_singleton.mp hN]
        exact hW

/-- If every matrix in `Ws` is a `W'` matrix, then `{S, T} ∪ Ws` is mortal if and only if some
  nonempty sequence from `Ws` maps `[1, 0, 1]` to `[h, h, 1]` with `h > 0`. -/
theorem mortal_iff_exists_prod_of_Ws
    (Ws : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hWs : ∀ M ∈ Ws, ∃ (p q r s : ℤ) (hpq : p > q ∧ q ≥ 0) (hrs : r > s ∧ s ≥ 0),
      M = W' p q r s hpq hrs) :
    DecisionProblem ({S, T} ∪ Ws) ↔
      ∃ (seq : wSeq Ws) (h : ℤ), h > 0 ∧ wProd seq.val = !![h, h, 1] := by
  constructor
  · rintro ⟨Ms, hMem, hMs0⟩
    obtain ⟨Run, hRunMem, hRunNe, h, hpos, hRunProd⟩ :=
      mortal_extract Ws hWs Ms hMem ![1, 0, 1] [] (by simp)
        (Or.inl ⟨1, 1, 0, one_ne_zero, one_pos, le_rfl, by simp, by simp⟩) (by simp [hMs0])
    exact ⟨⟨Run, hRunNe, hRunMem⟩, h, hpos, row_mul_eq_of_vecMul_eq hRunProd⟩
  · rintro ⟨⟨is, his_ne, his_mem⟩, h, hh, hprod⟩
    refine ⟨S :: (is ++ [T]), ?_, ?_⟩
    · intro M hM
      rcases List.mem_cons.mp hM with rfl | hM'
      · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
      · rcases List.mem_append.mp hM' with hM'' | hM''
        · exact Finset.mem_union_right _ (his_mem M hM'')
        · rw [List.mem_singleton.mp hM'']
          exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · have hp : (S :: (is ++ [T])).prod = S * is.prod * T := by
        simp [List.prod_cons, List.prod_append, mul_assoc]
      rw [hp]
      exact S_prod_T_eq_zero is.prod h hprod

/-- The alphabet `{1, 2, 3}`, typed as `Fin 3`. `d : Fin 3` represents digit `d.val + 1`. -/
abbrev S123 := Fin 3

/-- The alphabet `{2, 3}`, typed as `Fin 2`. `d : Fin 2` represents digit `d.val + 2`. -/
abbrev S23 := Fin 2

/-- Lifts a list over `{2, 3}` to a list over `{1, 2, 3}`. -/
def liftS23 (w : List S23) : List S123 := w.map Fin.succ

/-- Reads a list over `{1, 2, 3}` as a base-10 numeral, most significant digit first. The empty
  list reads as `0`. -/
def wordToInt (w : List S123) : ℤ :=
  w.foldl (fun acc d => acc * 10 + (d.val + 1)) 0

/-- `1` followed by `n` `0`s. -/
def shift (n : ℕ) : ℤ := 10 ^ n

/-- The empty word reads as `0`. -/
theorem wordToInt_nil : wordToInt [] = 0 := rfl

/-- Appending a digit `d` multiplies by `10` and adds `d`. -/
theorem wordToInt_append_singleton (w : List S123) (d : S123) :
    wordToInt (w ++ [d]) = wordToInt w * 10 + (d.val + 1) := by
  simp [wordToInt, List.foldl_append]

/-- The integer representation of a list over `{1, 2, 3}` is always non-negative. -/
theorem wordToInt_nonneg (w : List S123) : 0 ≤ wordToInt w := by
  induction w using List.reverseRecOn with
  | nil => simp [wordToInt_nil]
  | append_singleton w d ih =>
    rw [wordToInt_append_singleton]
    omega

/-- The integer representation of a list is strictly less than `10^|w|`. -/
theorem wordToInt_lt_shift (w : List S123) : wordToInt w < shift w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [wordToInt_nil, shift]
  | append_singleton w d ih =>
    rw [wordToInt_append_singleton, List.length_append, List.length_singleton, shift, pow_succ]
    unfold shift at ih
    have := d.isLt
    omega

/-- Appending `U` to `X` shifts the numeral of `X` left by `|U|` digits and adds that of `U`. -/
theorem wordToInt_append (X U : List S123) :
    wordToInt (X ++ U) = wordToInt X * shift U.length + wordToInt U := by
  induction U using List.reverseRecOn with
  | nil => simp [wordToInt_nil, shift]
  | append_singleton U d ih =>
    rw [← List.append_assoc, wordToInt_append_singleton, ih, wordToInt_append_singleton,
      List.length_append, List.length_singleton, shift, shift, pow_succ]
    ring

/-- The matrix of a pair of words `(U, V)` over `{1, 2, 3}`: `W'` with `p = 10^|U|`,
  `q = wordToInt U`, `r = 10^|V|` and `s = wordToInt V`. -/
def stringPairToW (U V : List S123) : Matrix (Fin 3) (Fin 3) ℤ :=
  W' (shift U.length) (wordToInt U) (shift V.length) (wordToInt V)
    ⟨wordToInt_lt_shift U, wordToInt_nonneg U⟩
    ⟨wordToInt_lt_shift V, wordToInt_nonneg V⟩

/-- The mapping from words over `{1, 2, 3}` to their base-10 integer representation is injective:
  no digit is `0`, so the last digit and the remaining prefix can be read back. -/
theorem wordToInt_injective : Function.Injective wordToInt := by
  intro w₁
  induction w₁ using List.reverseRecOn with
  | nil =>
    intro w₂ h
    cases w₂ using List.reverseRecOn with
    | nil => rfl
    | append_singleton w₂ d =>
      rw [wordToInt_nil, wordToInt_append_singleton] at h
      have := wordToInt_nonneg w₂
      omega
  | append_singleton w₁ d₁ ih =>
    intro w₂ h
    cases w₂ using List.reverseRecOn with
    | nil =>
      rw [wordToInt_nil, wordToInt_append_singleton] at h
      have := wordToInt_nonneg w₁
      omega
    | append_singleton w₂ d₂ =>
      rw [wordToInt_append_singleton, wordToInt_append_singleton] at h
      have hd₁ := d₁.isLt
      have hd₂ := d₂.isLt
      have hd : d₁ = d₂ := Fin.ext (by omega)
      have hw : wordToInt w₁ = wordToInt w₂ := by omega
      rw [ih hw, hd]

/-- A word starting with `1` reads as a positive number. -/
theorem wordToInt_one_cons_pos (w : List S123) : 0 < wordToInt ((0 : S123) :: w) := by
  rw [show (0 : S123) :: w = [0] ++ w from rfl, wordToInt_append]
  have h₁ : wordToInt [(0 : S123)] = 1 := rfl
  have : 0 < shift w.length := by unfold shift; positivity
  have := wordToInt_nonneg w
  rw [h₁]
  linarith

/-- `liftS23` is injective. -/
theorem liftS23_injective : Function.Injective liftS23 := by
  intro a b hab
  exact List.map_injective_iff.mpr (fun x y h => Fin.succ_injective _ h) hab

/-- Multiplying `[wordToInt X, wordToInt Y, 1]` by `stringPairToW U V` appends `U` to `X` and
  `V` to `Y`. -/
theorem concatenation_mortal (X Y U V : List S123) :
    !![wordToInt X, wordToInt Y, 1] * stringPairToW U V =
    !![wordToInt (X ++ U), wordToInt (Y ++ V), 1] := by
  simp [stringPairToW, W', wordToInt_append]

/-- Multiplying `[wordToInt X, wordToInt Y, 1]` by a product of `stringPairToW` matrices appends
  all the first words to `X` and all the second words to `Y`. -/
theorem row_mul_prod (X Y : List S123) (pairs : List (List S123 × List S123)) :
    !![wordToInt X, wordToInt Y, 1] *
        (pairs.map (fun p => stringPairToW p.1 p.2)).prod =
    !![wordToInt (X ++ (pairs.map Prod.fst).flatten),
       wordToInt (Y ++ (pairs.map Prod.snd).flatten), 1] := by
  induction pairs generalizing X Y with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, List.flatten_cons, ← Matrix.mul_assoc,
               concatenation_mortal]
    rw [ih (X ++ p.1) (Y ++ p.2)]
    simp [List.append_assoc]

/-- The digit `1` in `S123`. -/
notation "one₁₂₃" => (0 : S123)

variable {K : Stack S23}

/-- `liftS23` distributes over concatenation. -/
theorem liftS23_append (a b : List S23) :
    liftS23 (a ++ b) = liftS23 a ++ liftS23 b := by
  simp [liftS23, List.map_append]

/-- Flattening the (lifted) top words of a stack equals the lift of its top-concatenation. -/
theorem flatten_liftS23_top (A : Stack S23) :
    (A.map (fun t => liftS23 t.top)).flatten = liftS23 (τ1 A) := by
  induction A with
  | nil => simp [liftS23]
  | cons t A ih =>
    rw [List.map_cons, List.flatten_cons, ih, τ1_cons, liftS23_append]

/-- Flattening the (lifted) bottom words of a stack equals the lift of its bottom-concatenation. -/
theorem flatten_liftS23_bot (A : Stack S23) :
    (A.map (fun t => liftS23 t.bot)).flatten = liftS23 (τ2 A) := by
  induction A with
  | nil => simp [liftS23]
  | cons t A ih =>
    rw [List.map_cons, List.flatten_cons, ih, τ2_cons, liftS23_append]

/-- The lifted bottom word of a tile, with a leading `1` if the tile is marked. -/
def markedBot (tb : Tile S23 × Bool) : List S123 :=
  if tb.2 then one₁₂₃ :: liftS23 tb.1.bot else liftS23 tb.1.bot

/-- The matrix of a tile, with a leading `1` on its bottom word if the tile is marked. -/
def markedW (tb : Tile S23 × Bool) : Matrix (Fin 3) (Fin 3) ℤ :=
  stringPairToW (liftS23 tb.1.top) (markedBot tb)

/-- A lifted word contains no `1`, so removing `1`s leaves it unchanged. -/
theorem filter_liftS23 (w : List S23) : (liftS23 w).filter (· ≠ one₁₂₃) = liftS23 w :=
  List.filter_eq_self.mpr fun a ha => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    simp [Fin.succ_ne_zero]

/-- Removing `1`s from a marked bottom word gives the lifted bottom word. -/
theorem filter_markedBot (tb : Tile S23 × Bool) :
    (markedBot tb).filter (· ≠ one₁₂₃) = liftS23 tb.1.bot := by
  unfold markedBot
  split
  · rw [List.filter_cons_of_neg (a := one₁₂₃) (by decide), filter_liftS23]
  · exact filter_liftS23 _

/-- If `1` followed by the lifted top words equals the marked bottom words, then the top and bottom
  words are equal: removing every `1` from both sides leaves the lifted top and bottom words. -/
theorem bots_eq_of_word (L : List (Tile S23 × Bool))
    (heq : one₁₂₃ :: liftS23 (τ1 (L.map Prod.fst)) = (L.map markedBot).flatten) :
    τ1 (L.map Prod.fst) = τ2 (L.map Prod.fst) := by
  apply liftS23_injective
  have h := congrArg (List.filter (· ≠ one₁₂₃)) heq
  rw [List.filter_cons_of_neg (a := one₁₂₃) (by decide), filter_liftS23, List.filter_flatten,
    List.map_map] at h
  rw [h, ← flatten_liftS23_bot, List.map_map]
  congr 1
  exact List.map_congr_left fun tb _ => filter_markedBot tb

/-- Multiplying `[1, 0, 1]` by the matrices of the marked tiles `L` gives `1` followed by the top
  words in the first coordinate and the marked bottom words in the second. -/
theorem wProd_markedW (L : List (Tile S23 × Bool)) :
    wProd (L.map markedW) =
      !![wordToInt (one₁₂₃ :: liftS23 (τ1 (L.map Prod.fst))),
         wordToInt (L.map markedBot).flatten, 1] := by
  have h := row_mul_prod [one₁₂₃] [] (L.map fun tb => (liftS23 tb.1.top, markedBot tb))
  simp only [List.map_map, Function.comp_def, List.nil_append, List.singleton_append] at h
  rw [← flatten_liftS23_top, List.map_map]
  exact h

/-- The tile matrices of `K`: the matrix of each tile, unmarked and marked. -/
def tileMats (K : Stack S23) : Finset (Matrix (Fin 3) (Fin 3) ℤ) :=
  (K.toFinset ×ˢ Finset.univ).image markedW

/-- Every tile matrix is a `W'` matrix. -/
theorem tileMats_W' (K : Stack S23) :
    ∀ M ∈ tileMats K, ∃ (p q r s : ℤ) (hpq : p > q ∧ q ≥ 0) (hrs : r > s ∧ s ≥ 0),
      M = W' p q r s hpq hrs := by
  intro M hM
  obtain ⟨tb, -, rfl⟩ := Finset.mem_image.mp hM
  exact ⟨_, _, _, _, ⟨wordToInt_lt_shift _, wordToInt_nonneg _⟩,
    ⟨wordToInt_lt_shift _, wordToInt_nonneg _⟩, rfl⟩

/-- A list of tile matrices of `K` is the list of matrices of some marked tiles of `K`. -/
theorem exists_marked_of_mem_tileMats {is : List (Matrix (Fin 3) (Fin 3) ℤ)}
    (his : ∀ M ∈ is, M ∈ tileMats K) :
    ∃ L : List (Tile S23 × Bool), is = L.map markedW ∧ ∀ tb ∈ L, tb.1 ∈ K := by
  induction is with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons M is ih =>
    obtain ⟨tb, htb, rfl⟩ := Finset.mem_image.mp (his M List.mem_cons_self)
    obtain ⟨L, rfl, hL⟩ := ih fun N hN => his N (List.mem_cons_of_mem _ hN)
    refine ⟨tb :: L, rfl, ?_⟩
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨List.mem_toFinset.mp (Finset.mem_product.mp htb).1, hL⟩

/-- If a nonempty sequence of tile matrices of `K` maps `[1, 0, 1]` to `[h, h, 1]`, then `K` has a
  solution. -/
theorem pcp_if_exists_prod (K : Stack S23) :
    (∃ (seq : wSeq (tileMats K)) (h : ℤ), h > 0 ∧ wProd seq.val = !![h, h, 1]) →
    PCP.DecisionProblem K := by
  rintro ⟨⟨is, his_ne, his_mem⟩, h, -, hprod⟩
  obtain ⟨L, rfl, hL⟩ := exists_marked_of_mem_tileMats his_mem
  rw [wProd_markedW] at hprod
  have h₀ := congr_fun (congr_fun hprod 0) 0
  have h₁ := congr_fun (congr_fun hprod 0) 1
  simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at h₀ h₁
  refine ⟨L.map Prod.fst, by simpa using his_ne, ?_, bots_eq_of_word L ?_⟩
  · intro t ht
    obtain ⟨tb, htb, rfl⟩ := List.mem_map.mp ht
    exact hL tb htb
  · exact wordToInt_injective (h₀.trans h₁.symm)

/-- The matrix set of a PCP instance `K`: `S`, `T` and the tile matrices of `K`. -/
def matImage (K : Stack S23) := {S, T} ∪ tileMats K

/-- If a PCP instance `K` has a solution, then its corresponding set of constructed matrices has a
  mortality solution: mark the first tile of the solution. -/
theorem matmort_of_pcp (h : PCP.DecisionProblem K) :
    DecisionProblem (matImage K) := by
  obtain ⟨A, hA_ne, hA_mem, hA⟩ := h
  obtain ⟨t₀, rest, rfl⟩ := List.exists_cons_of_ne_nil hA_ne
  let L : List (Tile S23 × Bool) := (t₀, true) :: rest.map (·, false)
  have hfst : L.map Prod.fst = t₀ :: rest := by simp [L, Function.comp_def]
  have hbot : (L.map markedBot).flatten = one₁₂₃ :: liftS23 (τ2 (t₀ :: rest)) := by
    simp only [L, List.map_cons, List.map_map, List.flatten_cons, markedBot, ite_true,
      Function.comp_def, Bool.false_eq_true, ite_false, List.cons_append, τ2_cons, liftS23_append]
    rw [flatten_liftS23_bot]
  refine (mortal_iff_exists_prod_of_Ws _ (tileMats_W' K)).2
    ⟨⟨L.map markedW, by simp [L], ?_⟩, wordToInt (one₁₂₃ :: liftS23 (τ1 (t₀ :: rest))), ?_, ?_⟩
  · intro M hM
    obtain ⟨tb, htb, rfl⟩ := List.mem_map.mp hM
    have : tb.1 ∈ t₀ :: rest := hfst ▸ List.mem_map_of_mem htb
    exact Finset.mem_image_of_mem _
      (Finset.mem_product.mpr ⟨List.mem_toFinset.mpr (hA_mem _ this), Finset.mem_univ _⟩)
  · exact wordToInt_one_cons_pos _
  · rw [wProd_markedW, hfst, hbot, hA]

/-- If the constructed set of matrices for a PCP instance `K` is mortal, then `K` has a solution. -/
theorem pcp_of_matmort (h : DecisionProblem (matImage K)) : PCP.DecisionProblem K :=
  pcp_if_exists_prod K ((mortal_iff_exists_prod_of_Ws _ (tileMats_W' K)).1 h)

/-- A PCP instance `K` over `{2, 3}` has a solution iff its matrix set
  `{S, T} ∪ {W(U, V), W(U, 1 :: V) | (U, V) ∈ K}` is mortal. -/
theorem pcp_iff_matmort (K : Stack S23) :
    PCP.DecisionProblem K ↔
    DecisionProblem (matImage K) :=
  ⟨matmort_of_pcp, pcp_of_matmort⟩

/-- `matImage` reduces PCP over `S23` to matrix mortality: `K` has a solution iff `matImage K` is
  mortal. -/
theorem pcp_reducesto_matMort_spec :
    @PCP.DecisionProblem S23 ⪯_s[matImage] fun Ws => MatMort.DecisionProblem Ws :=
  pcp_iff_matmort

/-- **The reduction.** PCP over `S23` many-one reduces to matrix mortality through `matImage`. -/
def pcpReducesMatMort : @PCP.DecisionProblem S23 ⪯_s fun Ws => MatMort.DecisionProblem Ws :=
  ⟨matImage, pcp_reducesto_matMort_spec⟩

end DiagonaLean.MatMort.Reduction
