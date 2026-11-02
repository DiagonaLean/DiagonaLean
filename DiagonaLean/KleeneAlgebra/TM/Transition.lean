/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.TM.Encoding
import DiagonaLean.KleeneAlgebra.Copy
import DiagonaLean.KleeneAlgebra.SingleStep

@[expose] public section

/-! # The transition term of a Turing machine (Def 13, Lemmas 14 and 35)

For each state `q` and scanned symbol `h`, with `tr q h = (⟨wr, dir⟩, q')`, the term `rule q h`
rewrites the window around the head and copies the rest of the word:

* no move:    `[q,h] ↦ [q',wr]`;
* move right: `[q,h] x ↦ wr [q',x]` (any cell `x`), or `[q,h] ⊣ ↦ wr [q',␣] ⊣` at the right end;
* move left:  `x [q,h] ↦ [q',x] wr`, or `⊢ [q,h] ↦ ⊢ [q',␣] wr` at the left end.

The copying context is `⊢ C∗ ⋯ C∗ ⊣`, where `C = Σₒ (cell o)_l (cell o)_r`. The transition term
is `R_M = Σ_{q,h} rule q h`.

## Main statements

* `Enc.mem_RM` (Lemma 14): `l(R_M) = {(wd d, wd (dstep d)) | d running}`.
* `Enc.rel_RM` (Lemma 35): `R_M` is a representable relation on configuration words.

The alphabet's `DecidableEq` (needed from Lemma 35 on, for `Σ^≠`) is the derived instance on
`Letter`, from `DecidableEq` on the tape symbols and the machine states; no classical choice.
-/

open scoped Computability

namespace DiagonaLean.KAComm.Enc

open Cslib.Turing TD FreePreKA

variable {Sym : Type} [Inhabited Sym] [Fintype Sym] {M : SingleTapeTM Sym}

/-- A list as a word. -/
abbrev w (x : List (Letter Sym M.State)) : FreeMonoid (Letter Sym M.State) := FreeMonoid.ofList x

theorem w_mul (x y : List (Letter Sym M.State)) : w x * w y = w (x ++ y) := rfl

variable (M) in
/-- Copy one tape cell. -/
noncomputable def C : TD (Letter Sym M.State) := cpf fun o : Option Sym => Letter.cell o

/-- `⊢ C∗ (u, v) C∗ ⊣`. -/
noncomputable def ctx (u v : List (Letter Sym M.State)) : TD (Letter Sym M.State) :=
  ofPair (w [.lend], w [.lend]) * (C M)∗ * ofPair (w u, w v) * (C M)∗ *
    ofPair (w [.rend], w [.rend])

/-- `⊢ C∗ (u, v)`: the window contains `⊣`. -/
noncomputable def ctxR (u v : List (Letter Sym M.State)) : TD (Letter Sym M.State) :=
  ofPair (w [.lend], w [.lend]) * (C M)∗ * ofPair (w u, w v)

/-- `(u, v) C∗ ⊣`: the window contains `⊢`. -/
noncomputable def ctxL (u v : List (Letter Sym M.State)) : TD (Letter Sym M.State) :=
  ofPair (w u, w v) * (C M)∗ * ofPair (w [.rend], w [.rend])

variable (M) in
/-- The rewriting rule for state `q` and scanned symbol `h`. -/
noncomputable def rule (q : M.State) (h : Option Sym) : TD (Letter Sym M.State) :=
  match M.tr q h with
  | (⟨wr, none⟩, q') => ctx [.head (some q) h] [.head q' wr]
  | (⟨wr, some .right⟩, q') =>
    (∑ x : Option Sym, ctx [.head (some q) h, .cell x] [.cell wr, .head q' x]) +
      ctxR [.head (some q) h, .rend] [.cell wr, .head q' none, .rend]
  | (⟨wr, some .left⟩, q') =>
    (∑ x : Option Sym, ctx [.cell x, .head (some q) h] [.head q' x, .cell wr]) +
      ctxL [.lend, .head (some q) h] [.lend, .head q' none, .cell wr]

variable (M) in
/-- **Definition 13.** The transition term `R_M`. -/
noncomputable def RM : TD (Letter Sym M.State) := ∑ p : M.State × Option Sym, rule M p.1 p.2

/-! ### Languages of the contexts -/

theorem mem_ctx (u v : List (Letter Sym M.State)) (s : W (Letter Sym M.State)) :
    SetSemiring.Mem s (pl (ctx u v)) ↔ ∃ a b : List (Option Sym),
      s = (w (.lend :: (cells a ++ u ++ cells b ++ [.rend])),
        w (.lend :: (cells a ++ v ++ cells b ++ [.rend]))) := by
  unfold ctx C
  simp only [mem_mul_ofPair, mem_mul_cpf_star, mem_ofPair]
  constructor
  · rintro ⟨_, ⟨_, b, ⟨_, ⟨_, a, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, b, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells, List.cons_append, List.nil_append, List.append_assoc]
  · rintro ⟨a, b, rfl⟩
    refine ⟨_, ⟨_, b, ⟨_, ⟨_, a, rfl, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells, List.cons_append, List.nil_append, List.append_assoc]

theorem mem_ctxR (u v : List (Letter Sym M.State)) (s : W (Letter Sym M.State)) :
    SetSemiring.Mem s (pl (ctxR u v)) ↔ ∃ a : List (Option Sym),
      s = (w (.lend :: (cells a ++ u)), w (.lend :: (cells a ++ v))) := by
  unfold ctxR C
  simp only [mem_mul_ofPair, mem_mul_cpf_star, mem_ofPair]
  constructor
  · rintro ⟨_, ⟨_, a, rfl, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells, List.cons_append, List.nil_append]
  · rintro ⟨a, rfl⟩
    refine ⟨_, ⟨_, a, rfl, rfl⟩, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells, List.cons_append, List.nil_append]

theorem mem_ctxL (u v : List (Letter Sym M.State)) (s : W (Letter Sym M.State)) :
    SetSemiring.Mem s (pl (ctxL u v)) ↔ ∃ b : List (Option Sym),
      s = (w (u ++ cells b ++ [.rend]), w (v ++ cells b ++ [.rend])) := by
  unfold ctxL C
  simp only [mem_mul_ofPair, mem_mul_cpf_star, mem_ofPair]
  constructor
  · rintro ⟨_, ⟨_, b, rfl, rfl⟩, rfl⟩
    refine ⟨b, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells]
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨_, b, rfl, rfl⟩, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells]

/-! ### Lemma 14 -/

theorem wdF_eq (d : Data M) : wdF d = w (wd d) := rfl

theorem mem_rule (q : M.State) (h : Option Sym) (s : W (Letter Sym M.State)) :
    SetSemiring.Mem s (pl (rule M q h)) ↔ ∃ l r : List (Option Sym),
      s = (wdF (⟨some q, l, h, r⟩ : Data M), wdF (dstep M ⟨some q, l, h, r⟩)) := by
  rcases htr : M.tr q h with ⟨⟨wr, _ | _ | _⟩, q'⟩
  · simp only [rule, htr, mem_ctx, dstep, wdF_eq, wd]
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨a.reverse, b, by simp [cells]⟩
    · rintro ⟨l, r, rfl⟩
      exact ⟨l.reverse, r, by simp [cells]⟩
  · simp only [rule, htr, pl_add, SetSemiring.mem_add, mem_pl_sum, Finset.mem_univ, true_and,
      mem_ctx, mem_ctxL]
    constructor
    · rintro (⟨x, a, b, rfl⟩ | ⟨b, rfl⟩)
      · exact ⟨x :: a.reverse, b, by simp [dstep, htr, wdF_eq, wd, cells]⟩
      · exact ⟨[], b, by simp [dstep, htr, wdF_eq, wd, cells]⟩
    · rintro ⟨l, r, rfl⟩
      cases l with
      | nil => exact Or.inr ⟨r, by simp [dstep, htr, wdF_eq, wd, cells]⟩
      | cons x l => exact Or.inl ⟨x, l.reverse, r, by simp [dstep, htr, wdF_eq, wd, cells]⟩
  · simp only [rule, htr, pl_add, SetSemiring.mem_add, mem_pl_sum, Finset.mem_univ, true_and,
      mem_ctx, mem_ctxR]
    constructor
    · rintro (⟨x, a, b, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨a.reverse, x :: b, by simp [dstep, htr, wdF_eq, wd, cells]⟩
      · exact ⟨a.reverse, [], by simp [dstep, htr, wdF_eq, wd, cells]⟩
    · rintro ⟨l, r, rfl⟩
      cases r with
      | nil => exact Or.inr ⟨l.reverse, by simp [dstep, htr, wdF_eq, wd, cells]⟩
      | cons x r => exact Or.inl ⟨x, l.reverse, r, by simp [dstep, htr, wdF_eq, wd, cells]⟩

/-- **Lemma 14.** `R_M` relates exactly each running configuration word to its successor. -/
theorem mem_RM (s : W (Letter Sym M.State)) :
    SetSemiring.Mem s (pl (RM M)) ↔ ∃ d : Data M, d.Running ∧ s = (wdF d, wdF (dstep M d)) := by
  rw [RM, mem_pl_sum]
  constructor
  · rintro ⟨⟨q, h⟩, -, hs⟩
    obtain ⟨l, r, rfl⟩ := (mem_rule q h s).1 hs
    exact ⟨⟨some q, l, h, r⟩, rfl, rfl⟩
  · rintro ⟨⟨_ | q, l, h, r⟩, hrun, rfl⟩
    · simp [Data.Running] at hrun
    · exact ⟨(q, h), Finset.mem_univ _, (mem_rule q h _).2 ⟨l, r, rfl⟩⟩

theorem wdF_injective : Function.Injective (wdF : Data M → FreeMonoid (Letter Sym M.State)) :=
  fun _ _ h => wd_injective h

/-! ### Lemma 35 -/

variable (M) in
/-- The configuration words. -/
def Lset : Set (FreeMonoid (Letter Sym M.State)) := Set.range wdF

theorem finiteState_ctx (u v : List (Letter Sym M.State)) : FiniteState (ctx (M := M) u v) :=
  ((((FiniteState.ofPair _).mul (FiniteState.cpf_star _)).mul (FiniteState.ofPair _)).mul
    (FiniteState.cpf_star _)).mul (FiniteState.ofPair _)

theorem finiteState_rule (q : M.State) (h : Option Sym) : FiniteState (rule M q h) := by
  rcases htr : M.tr q h with ⟨⟨wr, _ | _ | _⟩, q'⟩ <;> simp only [rule, htr]
  · exact finiteState_ctx _ _
  · exact (FiniteState.sum _ _ fun _ _ => finiteState_ctx _ _).add
      (((FiniteState.ofPair _).mul (FiniteState.cpf_star _)).mul (FiniteState.ofPair _))
  · exact (FiniteState.sum _ _ fun _ _ => finiteState_ctx _ _).add
      (((FiniteState.ofPair _).mul (FiniteState.cpf_star _)).mul (FiniteState.ofPair _))

variable [DecidableEq Sym] [DecidableEq M.State]

/-- **Lemma 35.** `R_M` is a representable relation on configuration words. -/
theorem rel_RM : Rel (Lset M) (RM M) := by
  refine lemma34 ?_ ?_ ?_ (FiniteState.sum _ _ fun p _ => finiteState_rule p.1 p.2) ⟨1, ?_⟩
  · rintro _ ⟨d, rfl⟩ _ ⟨d', rfl⟩ h
    exact congrArg wdF (prefixFree h)
  · intro s hs
    obtain ⟨d, -, rfl⟩ := (mem_RM s).1 hs
    exact ⟨d, rfl⟩
  · intro s hs
    obtain ⟨d, -, rfl⟩ := (mem_RM s).1 hs
    exact ⟨dstep M d, rfl⟩
  · intro s hs
    obtain ⟨d, -, rfl⟩ := (mem_RM s).1 hs
    show (wd (dstep M d)).length ≤ ((wd d).length + 1) * 1
    have := length_wd_dstep d
    omega

end DiagonaLean.KAComm.Enc
