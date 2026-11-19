/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Cslib.Languages.CombinatoryLogic.Evaluation
import DiagonaLean.Foundations.LambdaCalculus.ProofSearch

@[expose] public section

/-! # SKI terms as λ-terms

`tr` sends an SKI term to a locally nameless λ-term, with `S`, `K` and `I` as the closed terms
`λxyz.xz(yz)`, `λxy.x` and `λx.x`. Every `tr x` is locally closed (`lc_tr`), and SKI reduction
becomes β-reduction (`tr_mRed`). The translation does not reflect convertibility
(`tr_not_reflect`): `S ⬝ K` and `K ⬝ I` have no common SKI reduct, while their translations both
β-reduce to `λyz.z`.

The translations of the booleans `TT` and `FF` are not β-convertible (`not_betaConv_tr_TT_FF`):
`tr TT = λxy.x` and `tr FF` reduces to `λyz.z`, and a term with no application has no β-step.
-/

namespace DiagonaLean.Foundations.LambdaCalculus

open Cslib SKI LambdaCalculus.LocallyNameless.Untyped Term Relation

/-- The λ-term `λxyz.xz(yz)`. -/
def lS : Term ℕ :=
  .abs (.abs (.abs (.app (.app (.bvar 2) (.bvar 0)) (.app (.bvar 1) (.bvar 0)))))

/-- The λ-term `λxy.x`. -/
def lK : Term ℕ := .abs (.abs (.bvar 1))

/-- The λ-term `λx.x`. -/
def lI : Term ℕ := .abs (.bvar 0)

/-- The λ-term of an SKI term. -/
def tr : SKI → Term ℕ
  | .S => lS
  | .K => lK
  | .I => lI
  | .app x y => .app (tr x) (tr y)

/-- Every translated term is locally closed. -/
theorem lc_tr (x : SKI) : LC (tr x) := by
  rw [← lcAt_iff_LC]
  induction x with
  | S => rfl
  | K => rfl
  | I => rfl
  | app x y ihx ihy => simp [tr, LcAt, ihx, ihy]

/-- The abstraction of a locally closed term is locally closed. -/
theorem lc_abs_of_lc {M : Term ℕ} (h : LC M) : LC (Term.abs M) := by
  rw [← lcAt_iff_LC] at h ⊢
  exact lcAt_le M 0 1 (Nat.zero_le 1) h

/-- A β-redex of locally closed terms reduces to its contractum `M ^ N`. -/
theorem steps_beta {M N R : Term ℕ} (hM : LC (Term.abs M)) (hN : LC N) (h : M ^ N = R) :
    Term.app (Term.abs M) N ↠βᶠ R :=
  h ▸ .single (Xi.base (Beta.beta hM hN))

/-- `tr (I ⬝ x)` reduces to `tr x`. -/
theorem tr_I (x : SKI) : tr (I ⬝ x) ↠βᶠ tr x :=
  steps_beta (lc_tr I) (lc_tr x) rfl

/-- `λxy.x` applied to two locally closed terms reduces to the first. -/
theorem steps_K {M N : Term ℕ} (hM : LC M) (hN : LC N) : Term.app (Term.app lK M) N ↠βᶠ M := by
  have h₁ : Term.app lK M ↠βᶠ Term.abs M := steps_beta (lc_tr K) hM rfl
  have h₂ : Term.app (Term.abs M) N ↠βᶠ M := steps_beta (lc_abs_of_lc hM) hN (open_lc 0 N M hM)
  exact (FullBeta.redex_app_l_cong h₁ hN).trans h₂

/-- `tr (K ⬝ x ⬝ y)` reduces to `tr x`. -/
theorem tr_K (x y : SKI) : tr (K ⬝ x ⬝ y) ↠βᶠ tr x := steps_K (lc_tr x) (lc_tr y)

/-- `tr (S ⬝ x ⬝ y ⬝ z)` reduces to `tr (x ⬝ z ⬝ (y ⬝ z))`. -/
theorem tr_S (x y z : SKI) : tr (S ⬝ x ⬝ y ⬝ z) ↠βᶠ tr (x ⬝ z ⬝ (y ⬝ z)) := by
  have hx := lc_tr x
  have hy := lc_tr y
  have hz := lc_tr z
  have h₁ : Term.app lS (tr x) ↠βᶠ
      Term.abs (.abs (.app (.app (tr x) (.bvar 0)) (.app (.bvar 1) (.bvar 0)))) :=
    steps_beta (lc_tr S) hx (by simp [Term.open', openRec_abs, openRec_app, openRec_bvar])
  have hlc₁ : LC (Term.abs (.abs (.app (.app (tr x) (.bvar 0)) (.app (.bvar 1) (.bvar 0))))) :=
    lc_of_steps h₁ (LC.app (lc_tr S) hx)
  have h₂ : Term.app (Term.abs (.abs (.app (.app (tr x) (.bvar 0)) (.app (.bvar 1) (.bvar 0)))))
      (tr y) ↠βᶠ Term.abs (.app (.app (tr x) (.bvar 0)) (.app (tr y) (.bvar 0))) :=
    steps_beta hlc₁ hy
      (by simp [Term.open', openRec_abs, openRec_app, openRec_bvar, open_lc _ _ _ hx])
  have hlc₂ : LC (Term.abs (.app (.app (tr x) (.bvar 0)) (.app (tr y) (.bvar 0)))) :=
    lc_of_steps h₂ (LC.app hlc₁ hy)
  have h₃ : Term.app (Term.abs (.app (.app (tr x) (.bvar 0)) (.app (tr y) (.bvar 0)))) (tr z)
      ↠βᶠ tr (x ⬝ z ⬝ (y ⬝ z)) :=
    steps_beta hlc₂ hz (by
      simp [tr, Term.open', openRec_app, openRec_bvar, open_lc _ _ _ hx, open_lc _ _ _ hy])
  exact (FullBeta.redex_app_l_cong (FullBeta.redex_app_l_cong h₁ hy) hz).trans
    ((FullBeta.redex_app_l_cong h₂ hz).trans h₃)

/-- An SKI reduction step becomes a β-reduction. -/
theorem tr_red {x y : SKI} (h : x ⭢ y) : tr x ↠βᶠ tr y := by
  induction h with
  | red_S x y z => exact tr_S x y z
  | red_K x y => exact tr_K x y
  | red_I x => exact tr_I x
  | red_head x x' y _ ih => exact FullBeta.redex_app_l_cong ih (lc_tr y)
  | red_tail x y y' _ ih => exact FullBeta.redex_app_r_cong ih (lc_tr x)

/-- An SKI reduction becomes a β-reduction. -/
theorem tr_mRed {x y : SKI} (h : x ↠ y) : tr x ↠βᶠ tr y := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans (tr_red hs)

/-- `tr (K ⬝ I)` reduces to `λyz.z`. -/
theorem tr_KI : tr (K ⬝ I) ↠βᶠ Term.abs lI := steps_beta (lc_tr K) (lc_tr I) rfl

/-- `tr (S ⬝ K)` reduces to `λyz.z`. -/
theorem tr_SK : tr (S ⬝ K) ↠βᶠ Term.abs lI := by
  have hK : LC lK := lc_tr K
  have h₁ : Term.app lS lK ↠βᶠ
      Term.abs (.abs (.app (.app lK (.bvar 0)) (.app (.bvar 1) (.bvar 0)))) :=
    steps_beta (lc_tr S) hK (by simp [Term.open', openRec_abs, openRec_app, openRec_bvar])
  refine h₁.trans (FullBeta.redex_abs_cong ∅ fun x _ => ?_)
  have e₁ : (Term.abs (.app (.app lK (.bvar 0)) (.app (.bvar 1) (.bvar 0)))) ^ fvar x =
      Term.abs (.app (.app lK (.bvar 0)) (.app (.fvar x) (.bvar 0))) := by
    simp [Term.open', openRec_abs, openRec_app, openRec_bvar, open_lc _ _ _ hK]
  have e₂ : lI ^ fvar x = lI := open_lc _ _ _ (lc_tr I)
  rw [e₁, e₂]
  refine FullBeta.redex_abs_cong ∅ fun y _ => ?_
  have e₃ : (Term.app (.app lK (.bvar 0)) (.app (.fvar x) (.bvar 0))) ^ fvar y =
      Term.app (.app lK (.fvar y)) (.app (.fvar x) (.fvar y)) := by
    simp [Term.open', openRec_app, openRec_bvar, openRec_fvar, open_lc _ _ _ hK]
  have e₄ : (Term.bvar 0 : Term ℕ) ^ fvar y = fvar y := by simp [Term.open', openRec_bvar]
  rw [e₃, e₄]
  exact steps_K (.fvar y) (.app (.fvar x) (.fvar y))

/-- The translation does not reflect convertibility: `S ⬝ K` and `K ⬝ I` have no common
SKI reduct, but their translations have a common β-reduct. -/
theorem tr_not_reflect :
    ¬ Join (ReflTransGen Red) (S ⬝ K) (K ⬝ I) ∧ BetaConv (tr (S ⬝ K)) (tr (K ⬝ I)) :=
  ⟨fun h => by simpa using eq_of_join_mRed_redexFree h (by decide) (by decide),
    ⟨Term.abs lI, tr_SK, tr_KI⟩⟩

/-- `M` contains no application. -/
def NoApp : Term ℕ → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .abs M => NoApp M
  | .app _ _ => False

/-- Opening with a free variable keeps a term free of applications. -/
theorem noApp_openRec {M : Term ℕ} {i x : ℕ} (h : NoApp M) : NoApp (M⟦i ↝ fvar x⟧) := by
  induction M generalizing i with
  | bvar j =>
    rw [openRec_bvar]
    split <;> trivial
  | fvar y => trivial
  | abs M ih => exact ih (i := i + 1) h
  | app M N => exact h.elim

/-- A term with no application has no β-step. -/
theorem not_step_of_noApp {M N : Term ℕ} (h : NoApp M) : ¬ M ⭢βᶠ N := by
  intro hs
  induction hs with
  | base hb => cases hb; exact h
  | appL => exact h
  | appR => exact h
  | abs xs _ ih =>
    obtain ⟨x, hx⟩ := fresh_exists xs
    exact ih x hx (noApp_openRec h)

/-- A term with no application reduces only to itself. -/
theorem eq_of_noApp_steps {M N : Term ℕ} (h : NoApp M) (hs : M ↠βᶠ N) : N = M := by
  rcases hs.cases_head with rfl | ⟨P, hP, -⟩
  · rfl
  · exact (not_step_of_noApp h hP).elim

/-- `tr TT` and `tr FF` are not β-convertible. -/
theorem not_betaConv_tr_TT_FF : ¬ BetaConv (tr TT) (tr FF) := by
  intro h
  have hFF : tr FF ↠βᶠ Term.abs lI := tr_KI
  obtain ⟨P, hK, hI⟩ := betaConv_equivalence.trans h (betaConv_of_steps hFF)
  have e₁ : P = lK := eq_of_noApp_steps trivial hK
  have e₂ : P = Term.abs lI := eq_of_noApp_steps trivial hI
  have e : lK = Term.abs lI := e₁.symm.trans e₂
  simp [lK, lI] at e

end DiagonaLean.Foundations.LambdaCalculus
