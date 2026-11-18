/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import DiagonaLean.Foundations.LambdaCalculus.Code

@[expose] public section

/-! # Enumerating β-conversions

Two λ-terms are β-convertible when they have a common reduct under Cslib's full β-reduction,
`Join (ReflTransGen FullBeta)`. A proof of a β-conversion between locally closed terms is a
program for a stack machine. An entry of the stack is a tuple `(tag, a, b, c, d)` of numbers, and
records one of four facts:

* tag `1`: `a` and `b` are the codes of locally closed β-convertible terms;
* tag `2`: `b` is the code of a term `M` with `LcAt a M`;
* tag `3`: `b`, `c`, `d` are the codes of terms `N`, `M`, `M⟦a ↝ N⟧`;
* tag `4`: `c`, `d` are the codes of terms `M`, `M⟦a ↜ b⟧`.

Entries with other tags record nothing. Every instruction either pushes a good fact, using only
entries already on the stack, or does nothing, so every entry of every reachable stack is good
(`run_inv`), with no parsing of terms and no substitution computed. Conversely, every
β-conversion between locally closed terms has a program (`exists_prog`).

`Checks` is the primitive recursive test that a code is a program proving a given conversion,
and β-convertibility of locally closed terms is `∃ k, Checks k (tc M) (tc N)`
(`betaConv_iff_checks`). The design follows `Foundations/CombinatoryLogic/ProofSearch.lean`.
-/

namespace DiagonaLean.Foundations.LambdaCalculus

open Cslib LambdaCalculus.LocallyNameless.Untyped Term Relation
  DiagonaLean.Foundations.Computability

/-- Two λ-terms are β-convertible: they have a common reduct under full β-reduction. -/
abbrev BetaConv (M N : Term ℕ) : Prop := Join (ReflTransGen FullBeta) M N

/-- β-convertibility is an equivalence relation. -/
theorem betaConv_equivalence : Equivalence BetaConv :=
  Confluent.equivalence_join_reflTransGen confluent_fullBeta

/-- A β-reduction is a β-conversion. -/
theorem betaConv_of_steps {M N : Term ℕ} (h : M ↠βᶠ N) : BetaConv M N := ⟨N, h, .refl⟩

/-- A reduct of a locally closed term is locally closed. -/
theorem lc_of_steps {M N : Term ℕ} (h : M ↠βᶠ N) (hM : LC M) : LC N := by
  rcases FullBeta.steps_lc_or_rfl h with ⟨_, hN⟩ | rfl
  · exact hN
  · exact hM

/-- If `M` and `N'` are locally closed, `M` is convertible to `M'` and `N` to `N'`, then
`app M N` is convertible to `app M' N'`. -/
theorem betaConv_app {M M' N N' : Term ℕ} (hM : LC M) (hN' : LC N') (h₁ : BetaConv M M')
    (h₂ : BetaConv N N') : BetaConv (app M N) (app M' N') := by
  obtain ⟨P, hMP, hM'P⟩ := h₁
  obtain ⟨Q, hNQ, hN'Q⟩ := h₂
  have hP := lc_of_steps hMP hM
  have hQ := lc_of_steps hN'Q hN'
  have hN : LC N := by
    rcases FullBeta.steps_lc_or_rfl hNQ with ⟨h, _⟩ | rfl
    · exact h
    · exact hQ
  have hM' : LC M' := by
    rcases FullBeta.steps_lc_or_rfl hM'P with ⟨h, _⟩ | rfl
    · exact h
    · exact hP
  exact ⟨app P Q,
    (FullBeta.redex_app_l_cong hMP hN).trans (FullBeta.redex_app_r_cong hNQ hP),
    (FullBeta.redex_app_l_cong hM'P hN').trans (FullBeta.redex_app_r_cong hN'Q hP)⟩

/-- Closing preserves local closure, one level up. -/
theorem lcAt_closeRec {k x : ℕ} {M : Term ℕ} (h : LcAt k M) : LcAt (k + 1) (M⟦k ↜ x⟧) := by
  induction M generalizing k with
  | bvar i => simp only [LcAt, decide_eq_true_eq, closeRec_bvar] at h ⊢; omega
  | fvar y =>
    rw [closeRec_fvar]
    split <;> simp
  | abs M ih => exact ih (k := k + 1) h
  | app M N ihM ihN =>
    simp only [LcAt, Bool.and_eq_true] at h
    simp [closeRec_app, LcAt, ihM h.1, ihN h.2]

/-- Closing `x` in a locally closed term and abstracting gives a locally closed term. -/
theorem lc_abs_close {x : ℕ} {M : Term ℕ} (h : LC M) : LC (Term.abs (M⟦0 ↜ x⟧)) := by
  rw [← lcAt_iff_LC] at h ⊢
  exact lcAt_closeRec h

/-- β-convertibility is a congruence for abstraction, through closing a variable. -/
theorem betaConv_abs {x : ℕ} {M N : Term ℕ} (h : BetaConv M N) :
    BetaConv (Term.abs (M⟦0 ↜ x⟧)) (Term.abs (N⟦0 ↜ x⟧)) := by
  obtain ⟨P, hMP, hNP⟩ := h
  exact ⟨Term.abs (P⟦0 ↜ x⟧), FullBeta.redex_abs_close hMP, FullBeta.redex_abs_close hNP⟩

/-- A stack entry. -/
abbrev Ent := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The stack machine's stack. -/
abbrev Stk := List Ent

/-- `e` records a true fact, read according to its tag. -/
def Good (e : Ent) : Prop :=
  if e.1 = 1 then
    ∃ M N, e.2.1 = tc M ∧ e.2.2.1 = tc N ∧ LC M ∧ LC N ∧ BetaConv M N
  else if e.1 = 2 then
    ∃ M, e.2.2.1 = tc M ∧ LcAt e.2.1 M
  else if e.1 = 3 then
    ∃ N M, e.2.2.1 = tc N ∧ e.2.2.2.1 = tc M ∧ e.2.2.2.2 = tc (M⟦e.2.1 ↝ N⟧)
  else if e.1 = 4 then
    ∃ M, e.2.2.2.1 = tc M ∧ e.2.2.2.2 = tc (M⟦e.2.1 ↜ e.2.2.1⟧)
  else True

/-- A conversion between locally closed terms gives a good entry. -/
theorem good_cv {M N : Term ℕ} (hM : LC M) (hN : LC N) (h : BetaConv M N) :
    Good (1, tc M, tc N, 0, 0) := by
  simp only [Good, ite_true]
  exact ⟨M, N, rfl, rfl, hM, hN, h⟩

/-- A local closure fact gives a good entry. -/
theorem good_lc {k : ℕ} {M : Term ℕ} (h : LcAt k M) : Good (2, k, tc M, 0, 0) := by
  simp only [Good]
  exact ⟨M, rfl, h⟩

/-- Every opening fact gives a good entry. -/
theorem good_op (i : ℕ) (N M : Term ℕ) : Good (3, i, tc N, tc M, tc (M⟦i ↝ N⟧)) := by
  simp only [Good]
  exact ⟨N, M, rfl, rfl, rfl⟩

/-- Every closing fact gives a good entry. -/
theorem good_cl (k x : ℕ) (M : Term ℕ) : Good (4, k, x, tc M, tc (M⟦k ↜ x⟧)) := by
  simp only [Good]
  exact ⟨M, rfl, rfl⟩

/-- A good conversion entry relates the codes of two convertible locally closed terms. -/
theorem Good.cv {e : Ent} (h : Good e) (ht : e.1 = 1) :
    ∃ M N, e.2.1 = tc M ∧ e.2.2.1 = tc N ∧ LC M ∧ LC N ∧ BetaConv M N := by
  simpa [Good, ht] using h

/-- A good local closure entry records a term that is locally closed at its level. -/
theorem Good.lc {e : Ent} (h : Good e) (ht : e.1 = 2) : ∃ M, e.2.2.1 = tc M ∧ LcAt e.2.1 M := by
  simpa [Good, ht] using h

/-- A good opening entry records the code of an opening. -/
theorem Good.op {e : Ent} (h : Good e) (ht : e.1 = 3) :
    ∃ N M, e.2.2.1 = tc N ∧ e.2.2.2.1 = tc M ∧ e.2.2.2.2 = tc (M⟦e.2.1 ↝ N⟧) := by
  simpa [Good, ht] using h

/-- A good closing entry records the code of a closing. -/
theorem Good.cl {e : Ent} (h : Good e) (ht : e.1 = 4) :
    ∃ M, e.2.2.2.1 = tc M ∧ e.2.2.2.2 = tc (M⟦e.2.1 ↜ e.2.2.1⟧) := by
  simpa [Good, ht] using h

/-- The result of each instruction, by its tag, given the instruction's argument. The
instructions build local closure facts (`0`–`3`), opening facts (`4`–`8`), closing facts
(`9`–`12`), and conversions: reflexivity, symmetry, transitivity, application, abstraction and
β (`13`–`18`). -/
def results (arg : ℕ) (s : Stk) : List Stk :=
  let a := s.headI
  let b := s.tail.headI
  let c := s.tail.tail.headI
  let r₁ := s.tail
  let r₂ := s.tail.tail
  let r₃ := s.tail.tail.tail
  let u := arg.unpair.1
  let v := arg.unpair.2
  [ if v < u then (2, u, cb v, 0, 0) :: s else s,
    (2, u, cf v, 0, 0) :: s,
    if a.1 = 2 ∧ 1 ≤ a.2.1 then (2, a.2.1 - 1, cl a.2.2.1, 0, 0) :: r₁ else s,
    if a.1 = 2 ∧ b.1 = 2 ∧ a.2.1 = b.2.1 then (2, a.2.1, cp b.2.2.1 a.2.2.1, 0, 0) :: r₂ else s,
    if a.1 = 2 then (3, arg, a.2.2.1, cb arg, a.2.2.1) :: r₁ else s,
    if a.1 = 2 ∧ u ≠ v then (3, u, a.2.2.1, cb v, cb v) :: r₁ else s,
    if a.1 = 2 then (3, u, a.2.2.1, cf v, cf v) :: r₁ else s,
    if a.1 = 3 ∧ 1 ≤ a.2.1 then
      (3, a.2.1 - 1, a.2.2.1, cl a.2.2.2.1, cl a.2.2.2.2) :: r₁ else s,
    if a.1 = 3 ∧ b.1 = 3 ∧ a.2.1 = b.2.1 ∧ a.2.2.1 = b.2.2.1 then
      (3, a.2.1, a.2.2.1, cp b.2.2.2.1 a.2.2.2.1, cp b.2.2.2.2 a.2.2.2.2) :: r₂ else s,
    (4, u, v.unpair.1, cb v.unpair.2, cb v.unpair.2) :: s,
    (4, u, v.unpair.1, cf v.unpair.2,
      if v.unpair.1 = v.unpair.2 then cb u else cf v.unpair.2) :: s,
    if a.1 = 4 ∧ 1 ≤ a.2.1 then
      (4, a.2.1 - 1, a.2.2.1, cl a.2.2.2.1, cl a.2.2.2.2) :: r₁ else s,
    if a.1 = 4 ∧ b.1 = 4 ∧ a.2.1 = b.2.1 ∧ a.2.2.1 = b.2.2.1 then
      (4, a.2.1, a.2.2.1, cp b.2.2.2.1 a.2.2.2.1, cp b.2.2.2.2 a.2.2.2.2) :: r₂ else s,
    if a.1 = 2 ∧ a.2.1 = 0 then (1, a.2.2.1, a.2.2.1, 0, 0) :: r₁ else s,
    if a.1 = 1 then (1, a.2.2.1, a.2.1, 0, 0) :: r₁ else s,
    if a.1 = 1 ∧ b.1 = 1 ∧ b.2.2.1 = a.2.1 then (1, b.2.1, a.2.2.1, 0, 0) :: r₂ else s,
    if a.1 = 1 ∧ b.1 = 1 then (1, cp b.2.1 a.2.1, cp b.2.2.1 a.2.2.1, 0, 0) :: r₂ else s,
    if a.1 = 4 ∧ b.1 = 4 ∧ c.1 = 1 ∧ a.2.1 = 0 ∧ b.2.1 = 0 ∧ a.2.2.1 = b.2.2.1 ∧
        b.2.2.2.1 = c.2.1 ∧ a.2.2.2.1 = c.2.2.1 then
      (1, cl b.2.2.2.2, cl a.2.2.2.2, 0, 0) :: r₃ else s,
    if a.1 = 3 ∧ a.2.1 = 0 ∧ b.1 = 2 ∧ b.2.1 = 0 ∧ b.2.2.1 = cl a.2.2.2.1 ∧ c.1 = 2 ∧
        c.2.1 = 0 ∧ c.2.2.1 = a.2.2.1 then
      (1, cp (cl a.2.2.2.1) a.2.2.1, a.2.2.2.2, 0, 0) :: r₃ else s ]

/-- One instruction: a tag and an argument. Unknown tags do nothing. -/
def stepS (s : Stk) (n : ℕ) : Stk := (results n.unpair.2 s).getD n.unpair.1 s

/-- Run a program from a stack. -/
def run (p : List ℕ) (s : Stk) : Stk := p.foldl stepS s

/-- Running `p ++ q` runs `p`, then `q`. -/
theorem run_append (p q : List ℕ) (s : Stk) : run (p ++ q) s = run q (run p s) := by
  simp [run, List.foldl_append]

/-- Every entry is good. -/
def Inv (s : Stk) : Prop := ∀ e ∈ s, Good e

/-- The default entry records nothing, so it is good. -/
theorem good_default : Good (default : Ent) := by simp [Good]

/-- The head of a good stack is good. -/
theorem Inv.head {s : Stk} (h : Inv s) : Good s.headI := by
  cases s with
  | nil => exact good_default
  | cons e s => exact h e List.mem_cons_self

/-- The tail of a good stack is good. -/
theorem Inv.tail {s : Stk} (h : Inv s) : Inv s.tail := by
  cases s with
  | nil => exact h
  | cons e s => exact fun f hf => h f (List.mem_cons_of_mem _ hf)

/-- Pushing a good entry onto a good stack gives a good stack. -/
theorem Inv.cons {s : Stk} {e : Ent} (he : Good e) (h : Inv s) : Inv (e :: s) := by
  intro f hf
  rcases List.mem_cons.1 hf with rfl | hf
  · exact he
  · exact h f hf

/-- Every instruction sends a good stack to a good stack. -/
theorem results_inv (arg : ℕ) {s : Stk} (hs : Inv s) : ∀ t ∈ results arg s, Inv t := by
  have ga := hs.head
  have gb := hs.tail.head
  have gc := hs.tail.tail.head
  have h₁ := hs.tail
  have h₂ := hs.tail.tail
  have h₃ := hs.tail.tail.tail
  simp only [results]
  generalize s.tail.tail.headI = c at gc ⊢
  generalize s.tail.headI = b at gb ⊢
  generalize s.headI = a at ga ⊢
  generalize arg.unpair.1 = u
  generalize arg.unpair.2 = v
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · split
    · rename_i h
      exact Inv.cons (good_lc (M := .bvar v) (by simpa using h)) hs
    · exact hs
  · exact Inv.cons (good_lc (M := .fvar v) rfl) hs
  · split
    · rename_i h
      obtain ⟨M, hm, hlc⟩ := ga.lc h.1
      have hk : a.2.1 - 1 + 1 = a.2.1 := by omega
      rw [hm]
      exact Inv.cons (good_lc (M := .abs M) (by simpa [LcAt, hk] using hlc)) h₁
    · exact hs
  · split
    · rename_i h
      obtain ⟨M₂, hm₂, hlc₂⟩ := ga.lc h.1
      obtain ⟨M₁, hm₁, hlc₁⟩ := gb.lc h.2.1
      rw [hm₁, hm₂]
      rw [← h.2.2] at hlc₁
      exact Inv.cons (good_lc (M := .app M₁ M₂) (by simp [LcAt, hlc₁, hlc₂])) h₂
    · exact hs
  · split
    · rename_i h
      obtain ⟨N, hn, -⟩ := ga.lc h
      have hg := good_op arg N (.bvar arg)
      rw [openRec_bvar, ite_eq_left rfl] at hg
      rw [hn]
      exact Inv.cons hg h₁
    · exact hs
  · split
    · rename_i h
      obtain ⟨N, hn, -⟩ := ga.lc h.1
      have hg := good_op u N (.bvar v)
      rw [openRec_bvar, ite_eq_right h.2] at hg
      rw [hn]
      exact Inv.cons hg h₁
    · exact hs
  · split
    · rename_i h
      obtain ⟨N, hn, -⟩ := ga.lc h
      have hg := good_op u N (.fvar v)
      rw [openRec_fvar] at hg
      rw [hn]
      exact Inv.cons hg h₁
    · exact hs
  · split
    · rename_i h
      obtain ⟨N, M, hn, hm, hr⟩ := ga.op h.1
      have hg := good_op (a.2.1 - 1) N (.abs M)
      have hk : a.2.1 - 1 + 1 = a.2.1 := by omega
      rw [openRec_abs, hk] at hg
      rw [hn, hm, hr]
      exact Inv.cons hg h₁
    · exact hs
  · split
    · rename_i h
      obtain ⟨N₂, M₂, hn₂, hm₂, hr₂⟩ := ga.op h.1
      obtain ⟨N₁, M₁, hn₁, hm₁, hr₁⟩ := gb.op h.2.1
      have hN : N₁ = N₂ := tc_injective (hn₁.symm.trans (h.2.2.2.symm.trans hn₂))
      subst hN
      have hg := good_op a.2.1 N₁ (.app M₁ M₂)
      rw [openRec_app] at hg
      rw [hn₂, hm₁, hm₂, hr₂, hr₁, ← h.2.2.1]
      exact Inv.cons hg h₂
    · exact hs
  · have hg := good_cl u v.unpair.1 (.bvar v.unpair.2)
    rw [closeRec_bvar] at hg
    exact Inv.cons hg hs
  · have hg := good_cl u v.unpair.1 (.fvar v.unpair.2)
    rw [closeRec_fvar] at hg
    refine Inv.cons ?_ hs
    split_ifs at hg ⊢ <;> exact hg
  · split
    · rename_i h
      obtain ⟨M, hm, hr⟩ := ga.cl h.1
      have hg := good_cl (a.2.1 - 1) a.2.2.1 (.abs M)
      have hk : a.2.1 - 1 + 1 = a.2.1 := by omega
      rw [closeRec_abs, hk] at hg
      rw [hm, hr]
      exact Inv.cons hg h₁
    · exact hs
  · split
    · rename_i h
      obtain ⟨M₂, hm₂, hr₂⟩ := ga.cl h.1
      obtain ⟨M₁, hm₁, hr₁⟩ := gb.cl h.2.1
      have hg := good_cl a.2.1 a.2.2.1 (.app M₁ M₂)
      rw [closeRec_app] at hg
      rw [hm₁, hm₂, hr₂, hr₁, ← h.2.2.1, ← h.2.2.2]
      exact Inv.cons hg h₂
    · exact hs
  · split
    · rename_i h
      obtain ⟨M, hm, hlc⟩ := ga.lc h.1
      rw [h.2] at hlc
      have hM : LC M := (lcAt_iff_LC M).1 hlc
      rw [hm]
      exact Inv.cons (good_cv hM hM (betaConv_equivalence.refl M)) h₁
    · exact hs
  · split
    · rename_i h
      obtain ⟨M, N, hm, hn, hM, hN, hc⟩ := ga.cv h
      rw [hm, hn]
      exact Inv.cons (good_cv hN hM (betaConv_equivalence.symm hc)) h₁
    · exact hs
  · split
    · rename_i h
      obtain ⟨B', C, hb', hc, hB', hC, h₂'⟩ := ga.cv h.1
      obtain ⟨A, B, ha, hb, hA, hB, h₁'⟩ := gb.cv h.2.1
      have hBB : B = B' := tc_injective (hb.symm.trans (h.2.2.trans hb'))
      subst hBB
      rw [ha, hc]
      exact Inv.cons (good_cv hA hC (betaConv_equivalence.trans h₁' h₂')) h₂
    · exact hs
  · split
    · rename_i h
      obtain ⟨N, N', hn, hn', hN, hN', hc₂⟩ := ga.cv h.1
      obtain ⟨M, M', hm, hm', hM, hM', hc₁⟩ := gb.cv h.2
      rw [hm, hm', hn, hn']
      exact Inv.cons (good_cv (M := .app M N) (N := .app M' N') (LC.app hM hN) (LC.app hM' hN')
        (betaConv_app hM hN' hc₁ hc₂)) h₂
    · exact hs
  · split
    · rename_i h
      obtain ⟨hta, htb, htc, ha0, hb0, hx, hbm, ham⟩ := h
      obtain ⟨B', hb', hrb⟩ := ga.cl hta
      obtain ⟨A', ha', hra⟩ := gb.cl htb
      obtain ⟨A, B, hA, hB, hlA, hlB, hc⟩ := gc.cv htc
      have hAA : A' = A := tc_injective (ha'.symm.trans (hbm.trans hA))
      have hBB : B' = B := tc_injective (hb'.symm.trans (ham.trans hB))
      subst hAA hBB
      rw [ha0, hx] at hrb
      rw [hb0] at hra
      rw [hra, hrb]
      exact Inv.cons (good_cv (M := .abs (A'⟦0 ↜ b.2.2.1⟧)) (N := .abs (B'⟦0 ↜ b.2.2.1⟧))
        (lc_abs_close hlA) (lc_abs_close hlB) (betaConv_abs hc)) h₃
    · exact hs
  · split
    · rename_i h
      obtain ⟨hta, ha0, htb, hb0, hbm, htc, hc0, hcn⟩ := h
      obtain ⟨N, M, hn, hm, hr⟩ := ga.op hta
      obtain ⟨L, hl, hlcL⟩ := gb.lc htb
      obtain ⟨N', hn', hlcN⟩ := gc.lc htc
      have hL : L = .abs M := tc_injective (hl.symm.trans (by rw [hbm, hm]; rfl))
      have hN : N' = N := tc_injective (hn'.symm.trans (hcn.trans hn))
      subst hL hN
      rw [hb0] at hlcL
      rw [hc0] at hlcN
      rw [ha0] at hr
      have hAbs : LC (Term.abs M) := (lcAt_iff_LC _).1 hlcL
      have hN : LC N' := (lcAt_iff_LC _).1 hlcN
      have hstep : Term.app (Term.abs M) N' ⭢βᶠ M ^ N' := Xi.base (Beta.beta hAbs hN)
      rw [hm, hn, hr]
      exact Inv.cons (good_cv (M := .app (.abs M) N') (N := M ^ N') (LC.app hAbs hN)
        (FullBeta.step_lc_r hstep) (betaConv_of_steps (.single hstep))) h₃
    · exact hs

/-- One instruction sends a good stack to a good stack. -/
theorem stepS_inv {s : Stk} (hs : Inv s) (n : ℕ) : Inv (stepS s n) := by
  unfold stepS
  rw [List.getD_eq_getElem?_getD]
  cases h : (results n.unpair.2 s)[n.unpair.1]? with
  | none => exact hs
  | some t => exact results_inv _ hs t (List.mem_of_getElem? h)

/-- Running a program sends a good stack to a good stack. -/
theorem run_inv (p : List ℕ) {s : Stk} (hs : Inv s) : Inv (run p s) := by
  induction p generalizing s with
  | nil => exact hs
  | cons n p ih => exact ih (stepS_inv hs n)

/-- Running a one-instruction program applies that instruction. -/
theorem run_one (t a : ℕ) (s : Stk) : run [Nat.pair t a] s = (results a s).getD t s := by
  simp [run, stepS]

/-- `p` pushes the entry `e` onto any stack. -/
def Pushes (p : List ℕ) (e : Ent) : Prop := ∀ s, run p s = e :: s

/-- If `p` pushes `e` and `q` pushes `f`, then `p ++ q` pushes `f` on top of `e`. -/
theorem run_pushes {p q : List ℕ} {e f : Ent} (hp : Pushes p e) (hq : Pushes q f) (s : Stk) :
    run (p ++ q) s = f :: e :: s := by
  rw [run_append, hp, hq]

/-- Every local closure fact has a program that pushes it. -/
theorem exists_lc {k : ℕ} {M : Term ℕ} (h : LcAt k M) : ∃ p, Pushes p (2, k, tc M, 0, 0) := by
  induction M generalizing k with
  | bvar j =>
    have hj : j < k := by simpa using h
    exact ⟨[Nat.pair 0 (Nat.pair k j)], fun s => by simp [run_one, results, hj, tc]⟩
  | fvar x => exact ⟨[Nat.pair 1 (Nat.pair k x)], fun s => by simp [run_one, results, tc]⟩
  | abs M ih =>
    obtain ⟨p, hp⟩ := ih (k := k + 1) h
    exact ⟨p ++ [Nat.pair 2 0], fun s => by rw [run_append, hp, run_one]; simp [results, tc]⟩
  | app M N ihM ihN =>
    simp only [LcAt, Bool.and_eq_true] at h
    obtain ⟨p, hp⟩ := ihM h.1
    obtain ⟨q, hq⟩ := ihN h.2
    exact ⟨p ++ q ++ [Nat.pair 3 0], fun s => by
      rw [run_append, run_pushes hp hq, run_one]; simp [results, tc]⟩

/-- For a locally closed `N`, every opening by `N` has a program that pushes it. -/
theorem exists_op {N : Term ℕ} (hN : LcAt 0 N) (i : ℕ) (M : Term ℕ) :
    ∃ p, Pushes p (3, i, tc N, tc M, tc (M⟦i ↝ N⟧)) := by
  obtain ⟨q, hq⟩ := exists_lc hN
  induction M generalizing i with
  | bvar j =>
    by_cases hij : i = j
    · subst hij
      exact ⟨q ++ [Nat.pair 4 i], fun s => by
        rw [run_append, hq, run_one]; simp [results, tc, openRec_bvar]⟩
    · exact ⟨q ++ [Nat.pair 5 (Nat.pair i j)], fun s => by
        rw [run_append, hq, run_one]; simp [results, tc, openRec_bvar, hij]⟩
  | fvar x =>
    exact ⟨q ++ [Nat.pair 6 (Nat.pair i x)], fun s => by
      rw [run_append, hq, run_one]; simp [results, tc, openRec_fvar]⟩
  | abs M ih =>
    obtain ⟨p, hp⟩ := ih (i + 1)
    exact ⟨p ++ [Nat.pair 7 0], fun s => by
      rw [run_append, hp, run_one]; simp [results, tc, openRec_abs]⟩
  | app M M' ih ih' =>
    obtain ⟨p, hp⟩ := ih i
    obtain ⟨p', hp'⟩ := ih' i
    exact ⟨p ++ p' ++ [Nat.pair 8 0], fun s => by
      rw [run_append, run_pushes hp hp', run_one]; simp [results, tc, openRec_app]⟩

/-- Every closing has a program that pushes it. -/
theorem exists_cl (k x : ℕ) (M : Term ℕ) : ∃ p, Pushes p (4, k, x, tc M, tc (M⟦k ↜ x⟧)) := by
  induction M generalizing k with
  | bvar i =>
    exact ⟨[Nat.pair 9 (Nat.pair k (Nat.pair x i))], fun s => by
      simp [run_one, results, tc, closeRec_bvar]⟩
  | fvar y =>
    refine ⟨[Nat.pair 10 (Nat.pair k (Nat.pair x y))], fun s => ?_⟩
    simp only [run_one, results, Nat.unpair_pair, List.getD_cons_succ, List.getD_cons_zero,
      closeRec_fvar]
    split_ifs <;> rfl
  | abs M ih =>
    obtain ⟨p, hp⟩ := ih (k + 1)
    exact ⟨p ++ [Nat.pair 11 0], fun s => by
      rw [run_append, hp, run_one]; simp [results, tc, closeRec_abs]⟩
  | app M M' ih ih' =>
    obtain ⟨p, hp⟩ := ih k
    obtain ⟨p', hp'⟩ := ih' k
    exact ⟨p ++ p' ++ [Nat.pair 12 0], fun s => by
      rw [run_append, run_pushes hp hp', run_one]; simp [results, tc, closeRec_app]⟩

/-- Every locally closed term has a program that pushes its reflexive conversion. -/
theorem exists_refl {M : Term ℕ} (hM : LC M) : ∃ p, Pushes p (1, tc M, tc M, 0, 0) := by
  obtain ⟨p, hp⟩ := exists_lc ((lcAt_iff_LC M).2 hM)
  exact ⟨p ++ [Nat.pair 13 0], fun s => by rw [run_append, hp, run_one]; simp [results]⟩

/-- If `p` pushes `M = N` and `q` pushes `N = P`, then `p ++ q ++ [Nat.pair 15 0]` pushes
`M = P`. -/
theorem pushes_trans {p q : List ℕ} {a b c : ℕ} (hp : Pushes p (1, a, b, 0, 0))
    (hq : Pushes q (1, b, c, 0, 0)) : Pushes (p ++ q ++ [Nat.pair 15 0]) (1, a, c, 0, 0) :=
  fun s => by rw [run_append, run_pushes hp hq, run_one]; simp [results]

/-- If `p` pushes `M = N`, then `p ++ [Nat.pair 14 0]` pushes `N = M`. -/
theorem pushes_symm {p : List ℕ} {a b : ℕ} (hp : Pushes p (1, a, b, 0, 0)) :
    Pushes (p ++ [Nat.pair 14 0]) (1, b, a, 0, 0) :=
  fun s => by rw [run_append, hp, run_one]; simp [results]

/-- Every β-step has a program that pushes it. -/
theorem exists_step {M N : Term ℕ} (h : M ⭢βᶠ N) : ∃ p, Pushes p (1, tc M, tc N, 0, 0) := by
  induction h with
  | base hb =>
    cases hb with
    | beta hAbs hN =>
      rename_i M' N'
      obtain ⟨p, hp⟩ := exists_lc ((lcAt_iff_LC _).2 hN)
      obtain ⟨q, hq⟩ := exists_lc ((lcAt_iff_LC _).2 hAbs)
      obtain ⟨r, hr⟩ := exists_op ((lcAt_iff_LC _).2 hN) 0 M'
      exact ⟨p ++ q ++ r ++ [Nat.pair 18 0], fun s => by
        rw [run_append, run_append, run_pushes hp hq, hr, run_one]; simp [results, tc]; rfl⟩
  | appL hZ _ ih =>
    rename_i Z _ _
    obtain ⟨p, hp⟩ := exists_refl hZ
    obtain ⟨q, hq⟩ := ih
    exact ⟨p ++ q ++ [Nat.pair 16 0], fun s => by
      rw [run_append, run_pushes hp hq, run_one]; simp [results, tc]⟩
  | appR hZ _ ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := exists_refl hZ
    exact ⟨p ++ q ++ [Nat.pair 16 0], fun s => by
      rw [run_append, run_pushes hp hq, run_one]; simp [results, tc]⟩
  | @abs M N xs _ ih =>
    obtain ⟨x, hx⟩ := fresh_exists (xs ∪ M.fv ∪ N.fv)
    simp only [Finset.mem_union, not_or] at hx
    obtain ⟨p, hp⟩ := ih x hx.1.1
    obtain ⟨q, hq⟩ := exists_cl 0 x (M ^ fvar x)
    obtain ⟨r, hr⟩ := exists_cl 0 x (N ^ fvar x)
    have hM : (M ^ fvar x)⟦0 ↜ x⟧ = M := (open_close_var x M hx.1.2).symm
    have hN : (N ^ fvar x)⟦0 ↜ x⟧ = N := (open_close_var x N hx.2).symm
    rw [hM] at hq
    rw [hN] at hr
    exact ⟨p ++ q ++ r ++ [Nat.pair 17 0], fun s => by
      rw [run_append, run_append, run_pushes hp hq, hr, run_one]; simp [results, tc]⟩

/-- Every β-reduction from a locally closed term has a program that pushes it. -/
theorem exists_steps {M N : Term ℕ} (h : M ↠βᶠ N) (hM : LC M) :
    ∃ p, Pushes p (1, tc M, tc N, 0, 0) := by
  induction h with
  | refl => exact exists_refl hM
  | tail _ hs ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := exists_step hs
    exact ⟨_, pushes_trans hp hq⟩

/-- Every β-conversion between locally closed terms has a program that pushes it. -/
theorem exists_prog {M N : Term ℕ} (hM : LC M) (hN : LC N) (h : BetaConv M N) :
    ∃ p, Pushes p (1, tc M, tc N, 0, 0) := by
  obtain ⟨P, hMP, hNP⟩ := h
  obtain ⟨p, hp⟩ := exists_steps hMP hM
  obtain ⟨q, hq⟩ := exists_steps hNP hN
  exact ⟨_, pushes_trans hp (pushes_symm hq)⟩

/-- The program with code `k` ends with the conversion `(a, b)` on top. -/
def Checks (k a b : ℕ) : Prop := (run (Denumerable.ofNat (List ℕ) k) []).headI = (1, a, b, 0, 0)

/-- `Checks k a b` is decidable. -/
instance (k a b : ℕ) : Decidable (Checks k a b) := inferInstanceAs (Decidable (_ = _))

/-- If a program checks the codes of `M` and `N`, then `M` and `N` are β-convertible. -/
theorem betaConv_of_checks {k : ℕ} {M N : Term ℕ} (h : Checks k (tc M) (tc N)) :
    BetaConv M N := by
  have hi : Inv (run (Denumerable.ofNat (List ℕ) k) []) := run_inv _ (by simp [Inv])
  have hg := hi.head
  rw [h] at hg
  obtain ⟨M', N', hm, hn, -, -, hc⟩ := hg.cv rfl
  rwa [tc_injective hm, tc_injective hn]

/-- Two locally closed terms are β-convertible iff some program checks their codes. -/
theorem betaConv_iff_checks {M N : Term ℕ} (hM : LC M) (hN : LC N) :
    BetaConv M N ↔ ∃ k, Checks k (tc M) (tc N) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_prog hM hN h
    exact ⟨Encodable.encode p, by simp [Checks, Denumerable.ofNat_encode, hp []]⟩
  · rintro ⟨k, hk⟩
    exact betaConv_of_checks hk

/-- `results` is primitive recursive. -/
theorem results_prim : Primrec fun y : Stk × ℕ => results y.2 y.1 := by
  unfold results
  fun_prop

attribute [local irreducible] results in
/-- `stepS` is primitive recursive. -/
theorem stepS_prim : Primrec fun y : Stk × ℕ => stepS y.1 y.2 := by
  have h : Primrec fun y : Stk × ℕ => ((results y.2.unpair.2 y.1)[y.2.unpair.1]?).getD y.1 :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp
        (results_prim.comp (prim_pair Primrec.fst (prim_snd (prim_unpair Primrec.snd))))
        (prim_fst (prim_unpair Primrec.snd)))
      Primrec.fst
  exact h.of_eq fun y => (List.getD_eq_getElem?_getD ..).symm

/-- Running the program with code `k` from the empty stack is primitive recursive in `k`. -/
theorem run_prim : Primrec fun k : ℕ => run (Denumerable.ofNat (List ℕ) k) [] :=
  Primrec.list_foldl (Primrec.ofNat _) (Primrec.const []) (stepS_prim.comp Primrec.snd).to₂

/-- `Checks` is a primitive recursive predicate. -/
theorem checks_prim : PrimrecPred fun x : ℕ × ℕ × ℕ => Checks x.1 x.2.1 x.2.2 := by
  unfold Checks
  exact pred_eq (prim_headI (run_prim.comp Primrec.fst))
    (prim_pair (Primrec.const 1) (prim_pair (prim_fst Primrec.snd)
      (prim_pair (prim_snd Primrec.snd) (Primrec.const (0, 0)))))

end DiagonaLean.Foundations.LambdaCalculus
