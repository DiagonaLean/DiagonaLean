/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KleeneAlgebra.Doubled

@[expose] public section

/-! # The free Kleene algebra `K X` with commutativity conditions

The free Kleene algebra `K X` over `X` with commutation hypotheses `C`, the quotient of
expressions by provable equality `RExp.KAEquiv C`, together with the maps `T X → K X` and
`K Σ̈ → P(S Σ̈)` that factor the language interpretation of `T Σ̈` (Theorem 18). The power set
of a monoid is shown to be a Kleene algebra.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Section 2, Theorem 18
-/

open scoped Computability

namespace DiagonaLean.KAComm.KleeneAlgebra

namespace RExp

variable {X : Type*}

/-- Provable equality in Kleene algebra with commutation hypotheses `C`: the pre-Kleene algebra
theory `Equiv C`, closed under congruence, plus `e∗ e ≤ e∗` and both induction rules. Here `a ≤ b`
is written `a + b = b`. -/
inductive KAEquiv (C : X → X → Prop) : RExp X → RExp X → Prop where
  /-- Provable equality in the pre-Kleene theory. -/
  | ofEquiv {e f} : Equiv C e f → KAEquiv C e f
  /-- Symmetry. -/
  | symm {e f} : KAEquiv C e f → KAEquiv C f e
  /-- Transitivity. -/
  | trans {e f g} : KAEquiv C e f → KAEquiv C f g → KAEquiv C e g
  /-- Congruence for `plus`. -/
  | plus {e e' f f'} : KAEquiv C e e' → KAEquiv C f f' → KAEquiv C (plus e f) (plus e' f')
  /-- Congruence for `mul`. -/
  | mul {e e' f f'} : KAEquiv C e e' → KAEquiv C f f' → KAEquiv C (mul e f) (mul e' f')
  /-- Congruence for `star`. -/
  | star {e e'} : KAEquiv C e e' → KAEquiv C (star e) (star e')
  /-- Right unfolding: `e∗ e ≤ e∗`. -/
  | kstar_mul_le (e) : KAEquiv C (plus (mul (star e) e) (star e)) (star e)
  /-- Right induction: `b a ≤ b` implies `b a∗ ≤ b`. -/
  | mul_kstar_le_self {a b} : KAEquiv C (plus (mul b a) b) b →
      KAEquiv C (plus (mul b (star a)) b) b
  /-- Left induction: `a b ≤ b` implies `a∗ b ≤ b`. -/
  | kstar_mul_le_self {a b} : KAEquiv C (plus (mul a b) b) b →
      KAEquiv C (plus (mul (star a) b) b) b

/-- Reflexivity of `KAEquiv`. -/
theorem KAEquiv.refl {C : X → X → Prop} (e : RExp X) : KAEquiv C e e := .ofEquiv (.refl e)

/-- The setoid of provable equality in Kleene algebra. -/
def kaSetoid (C : X → X → Prop) : Setoid (RExp X) where
  r := KAEquiv C
  iseqv := ⟨KAEquiv.refl, KAEquiv.symm, KAEquiv.trans⟩

/-- Soundness: `KAEquiv`-equal expressions have equal interpretations in every Kleene algebra in
which the images of `C`-related generators commute. -/
theorem eval_ka_sound {α : Type*} [KleeneAlgebra α] {C : X → X → Prop} (f : X → α)
    (hf : ∀ x y, C x y → f x * f y = f y * f x) {e g : RExp X} (h : KAEquiv C e g) :
    eval f e = eval f g := by
  induction h with
  | ofEquiv h => exact eval_sound f hf h
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | plus _ _ ih₁ ih₂ => simp only [eval, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp only [eval, ih₁, ih₂]
  | star _ ih => simp only [eval, ih]
  | kstar_mul_le e => exact add_eq_right_iff_le.2 (kstar_mul_le_kstar (a := eval f e))
  | mul_kstar_le_self _ ih =>
    exact add_eq_right_iff_le.2 (mul_kstar_le_self (add_eq_right_iff_le.1 ih))
  | kstar_mul_le_self _ ih =>
    exact add_eq_right_iff_le.2 (kstar_mul_le_self (add_eq_right_iff_le.1 ih))

/-- Provable equality in Kleene algebra with commutation hypotheses `C`, exactly as the paper
defines Kleene algebra (Section 2): the pre-Kleene theory `Equiv C`, closed under congruence, plus
left and right induction. Unlike `KAEquiv`, which follows Mathlib's `KleeneAlgebra`, it has no
right unfolding `e∗ e ≤ e∗`; that rule is derivable (`paperKAEquiv_kstar_mul_le`), so the two
theories coincide (`kaEquiv_iff_paperKAEquiv`). -/
inductive PaperKAEquiv (C : X → X → Prop) : RExp X → RExp X → Prop where
  /-- Provable equality in the pre-Kleene theory. -/
  | ofEquiv {e f} : Equiv C e f → PaperKAEquiv C e f
  /-- Symmetry. -/
  | symm {e f} : PaperKAEquiv C e f → PaperKAEquiv C f e
  /-- Transitivity. -/
  | trans {e f g} : PaperKAEquiv C e f → PaperKAEquiv C f g → PaperKAEquiv C e g
  /-- Congruence for `plus`. -/
  | plus {e e' f f'} : PaperKAEquiv C e e' → PaperKAEquiv C f f' →
      PaperKAEquiv C (plus e f) (plus e' f')
  /-- Congruence for `mul`. -/
  | mul {e e' f f'} : PaperKAEquiv C e e' → PaperKAEquiv C f f' →
      PaperKAEquiv C (mul e f) (mul e' f')
  /-- Congruence for `star`. -/
  | star {e e'} : PaperKAEquiv C e e' → PaperKAEquiv C (star e) (star e')
  /-- Right induction: `x y ≤ x` implies `x y∗ ≤ x`. -/
  | mul_kstar_le_self {a b} : PaperKAEquiv C (plus (mul b a) b) b →
      PaperKAEquiv C (plus (mul b (star a)) b) b
  /-- Left induction: `x y ≤ y` implies `x∗ y ≤ y`. -/
  | kstar_mul_le_self {a b} : PaperKAEquiv C (plus (mul a b) b) b →
      PaperKAEquiv C (plus (mul (star a) b) b) b

section PaperKA

variable {C : X → X → Prop}

/-- An inequality of the free pre-Kleene algebra is a provable equation `a + b = b`. -/
theorem equiv_of_le {a b : RExp X} (h : (FreePreKA.mk a : FreePreKA X C) ≤ FreePreKA.mk b) :
    Equiv C (plus a b) b :=
  FreePreKA.mk_eq_mk.1 (add_eq_right_iff_le.2 h)

/-- **Right unfolding is derivable** from the paper's axioms: `a∗ a ≤ a∗ a∗ ≤ a∗`, where the
second step is left induction applied to `a a∗ ≤ a∗`. -/
theorem paperKAEquiv_kstar_mul_le (a : RExp X) :
    PaperKAEquiv C (plus (mul (star a) a) (star a)) (star a) := by
  have h₁ : PaperKAEquiv C (plus (mul (star a) (star a)) (star a)) (star a) :=
    .kstar_mul_le_self (.ofEquiv (equiv_of_le (C := C)
      (mul_kstar_le_kstar' (FreePreKA.mk a : FreePreKA X C))))
  have h₂ : Equiv C (plus (mul (star a) a) (mul (star a) (star a))) (mul (star a) (star a)) :=
    equiv_of_le (C := C)
      (mul_le_mul_right (le_kstar' (FreePreKA.mk a : FreePreKA X C)) (FreePreKA.mk (star a)))
  exact ((PaperKAEquiv.plus (.ofEquiv (.refl _)) h₁.symm).trans
    (.ofEquiv (.symm (.plus_assoc _ _ _)))).trans ((PaperKAEquiv.plus (.ofEquiv h₂)
      (.ofEquiv (.refl _))).trans h₁)

/-- **`KAEquiv` is the paper's Kleene algebra theory.** -/
theorem kaEquiv_iff_paperKAEquiv {e f : RExp X} : KAEquiv C e f ↔ PaperKAEquiv C e f := by
  constructor
  · intro h
    induction h with
    | ofEquiv h => exact .ofEquiv h
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    | plus _ _ ih₁ ih₂ => exact ih₁.plus ih₂
    | mul _ _ ih₁ ih₂ => exact ih₁.mul ih₂
    | star _ ih => exact ih.star
    | kstar_mul_le e => exact paperKAEquiv_kstar_mul_le e
    | mul_kstar_le_self _ ih => exact .mul_kstar_le_self ih
    | kstar_mul_le_self _ ih => exact .kstar_mul_le_self ih
  · intro h
    induction h with
    | ofEquiv h => exact .ofEquiv h
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    | plus _ _ ih₁ ih₂ => exact ih₁.plus ih₂
    | mul _ _ ih₁ ih₂ => exact ih₁.mul ih₂
    | star _ ih => exact ih.star
    | mul_kstar_le_self _ ih => exact .mul_kstar_le_self ih
    | kstar_mul_le_self _ ih => exact .kstar_mul_le_self ih

end PaperKA

end RExp

/-- The free Kleene algebra `K X` over `X` with commutation hypotheses `C`. -/
def FreeKA (X : Type*) (C : X → X → Prop) : Type _ := Quotient (RExp.kaSetoid C)

namespace FreeKA

open RExp

variable {X : Type*} {C : X → X → Prop}

/-- The class of an expression. -/
def mk (e : RExp X) : FreeKA X C := Quotient.mk (RExp.kaSetoid C) e

/-- Two classes are equal iff the expressions are `KAEquiv`-equal. -/
theorem mk_eq_mk {e f : RExp X} : (mk e : FreeKA X C) = mk f ↔ KAEquiv C e f :=
  Quotient.eq (r := RExp.kaSetoid C)

/-- `KAEquiv`-equal expressions have equal classes. -/
theorem sound {e f : RExp X} (h : KAEquiv C e f) : (mk e : FreeKA X C) = mk f :=
  mk_eq_mk.2 h

/-- Pre-Kleene-provably equal expressions have equal classes. -/
theorem ax {e f : RExp X} (h : Equiv C e f) : (mk e : FreeKA X C) = mk f :=
  sound (.ofEquiv h)

/-- Induction on `K X`: a property of every class `mk e` holds everywhere. -/
@[elab_as_elim]
theorem ind {p : FreeKA X C → Prop} (h : ∀ e, p (mk e)) (a : FreeKA X C) : p a :=
  Quotient.inductionOn a h

/-- Zero is the class of `zero`. -/
instance : Zero (FreeKA X C) := ⟨mk zero⟩
/-- One is the class of `one`. -/
instance : One (FreeKA X C) := ⟨mk one⟩
/-- Addition is induced by `plus`. -/
instance : Add (FreeKA X C) :=
  ⟨Quotient.map₂ plus fun _ _ h₁ _ _ h₂ => KAEquiv.plus h₁ h₂⟩
/-- Multiplication is induced by `mul`. -/
instance : Mul (FreeKA X C) :=
  ⟨Quotient.map₂ RExp.mul fun _ _ h₁ _ _ h₂ => KAEquiv.mul h₁ h₂⟩
/-- Kleene star is induced by `star`. -/
instance : KStar (FreeKA X C) := ⟨Quotient.map star fun _ _ h => KAEquiv.star h⟩

/-- `K X` is a semiring. -/
instance : Semiring (FreeKA X C) where
  add_assoc a b c := by
    induction a using ind; induction b using ind; induction c using ind
    exact ax (Equiv.plus_assoc _ _ _)
  zero_add a := by induction a using ind; exact ax (Equiv.zero_plus _)
  add_zero a := by
    induction a using ind
    exact ax ((Equiv.plus_comm _ _).trans (Equiv.zero_plus _))
  add_comm a b := by
    induction a using ind; induction b using ind; exact ax (Equiv.plus_comm _ _)
  mul_assoc a b c := by
    induction a using ind; induction b using ind; induction c using ind
    exact ax (Equiv.mul_assoc _ _ _)
  one_mul a := by induction a using ind; exact ax (Equiv.one_mul _)
  mul_one a := by induction a using ind; exact ax (Equiv.mul_one _)
  zero_mul a := by induction a using ind; exact ax (Equiv.zero_mul _)
  mul_zero a := by induction a using ind; exact ax (Equiv.mul_zero _)
  left_distrib a b c := by
    induction a using ind; induction b using ind; induction c using ind
    exact ax (Equiv.left_distrib _ _ _)
  right_distrib a b c := by
    induction a using ind; induction b using ind; induction c using ind
    exact ax (Equiv.right_distrib _ _ _)
  nsmul := nsmulRec

/-- `K X` is an idempotent semiring. -/
instance : IdemSemiring (FreeKA X C) :=
  IdemSemiring.ofSemiring fun a => by induction a using ind; exact ax (Equiv.plus_idem _)

/-- Left unfolding, packaged only to reuse the pre-Kleene lemmas in the instance below. -/
private abbrev preKA : PreKleeneAlgebra (FreeKA X C) where
  kstar_unfold a := by induction a using ind; exact ax (Equiv.unfold _)

/-- `K X` is a Kleene algebra. -/
instance : KleeneAlgebra (FreeKA X C) where
  one_le_kstar a := @one_le_kstar' _ preKA a
  mul_kstar_le_kstar a := @mul_kstar_le_kstar' _ preKA a
  kstar_mul_le_kstar a := by
    induction a using ind
    exact add_eq_right_iff_le.1 (sound (KAEquiv.kstar_mul_le _))
  mul_kstar_le_self a b h := by
    induction a using ind; induction b using ind
    exact add_eq_right_iff_le.1 (sound (KAEquiv.mul_kstar_le_self
      (mk_eq_mk.1 (add_eq_right_iff_le.2 h))))
  kstar_mul_le_self a b h := by
    induction a using ind; induction b using ind
    exact add_eq_right_iff_le.1 (sound (KAEquiv.kstar_mul_le_self
      (mk_eq_mk.1 (add_eq_right_iff_le.2 h))))

/-- `K X` satisfies the commutation hypotheses. -/
theorem of_comm {x y : X} (h : C x y) :
    (mk (sym x) : FreeKA X C) * mk (sym y) = mk (sym y) * mk (sym x) :=
  ax (Equiv.comm h)

/-- The morphism `K X → α` into a Kleene algebra, determined by its action on generators. -/
def lift {α : Type*} [KleeneAlgebra α] (f : X → α) (hf : ∀ x y, C x y → f x * f y = f y * f x) :
    FreeKA X C → α :=
  Quotient.lift (RExp.eval f) fun _ _ h => RExp.eval_ka_sound f hf h

/-- The map `T X → K X`. -/
def ofPre : FreePreKA X C → FreeKA X C :=
  Quotient.lift mk fun _ _ h => ax h

end FreeKA

namespace SetSemiring

variable {M : Type*} [Monoid M]

/-- The power set of a monoid is a Kleene algebra: the language model validates the induction
rules that `T X` omits. -/
noncomputable instance instKleeneAlgebra : KleeneAlgebra (_root_.SetSemiring M) where
  one_le_kstar s := one_le_kstar' s
  mul_kstar_le_kstar s := mul_kstar_le_kstar' s
  kstar_mul_le_kstar s := by
    rintro x hx
    obtain ⟨_, ⟨l, hl, rfl⟩, b, hb, rfl⟩ := (mem_mul _ _ _).1 hx
    refine (mem_kstar _ _).2 ⟨l ++ [b], fun y hy => ?_, by simp⟩
    rcases List.mem_append.1 hy with hy | hy
    · exact hl y hy
    · rwa [List.mem_singleton.1 hy]
  mul_kstar_le_self a b h := by
    rintro x hx
    obtain ⟨y, hy, _, ⟨l, hl, rfl⟩, rfl⟩ := (mem_mul _ _ _).1 hx
    clear hx
    induction l generalizing y with
    | nil => rwa [List.prod_nil, mul_one]
    | cons c l ih =>
      rw [List.prod_cons, ← mul_assoc]
      exact ih (y * c) (h ((mem_mul _ _ _).2 ⟨y, hy, c, hl c (by simp), rfl⟩))
        fun z hz => hl z (by simp [hz])
  kstar_mul_le_self a b h := by
    rintro x hx
    obtain ⟨_, ⟨l, hl, rfl⟩, y, hy, rfl⟩ := (mem_mul _ _ _).1 hx
    clear hx
    induction l with
    | nil => rwa [List.prod_nil, one_mul]
    | cons c l ih =>
      rw [List.prod_cons, mul_assoc]
      exact h ((mem_mul _ _ _).2 ⟨c, hl c (by simp), l.prod * y,
        ih fun z hz => hl z (by simp [hz]), rfl⟩)

end SetSemiring

namespace TD

variable {A : Type*}

/-- The language interpretation of the free Kleene algebra, `K Σ̈ → P(S Σ̈)`. -/
noncomputable def plK : FreeKA (A ⊕ A) DComm → _root_.SetSemiring (W A) :=
  FreeKA.lift gen gen_comm

/-- The language interpretation of `T Σ̈` factors through `K Σ̈`. -/
theorem plK_ofPre (a : TD A) : plK (FreeKA.ofPre a) = pl a := by
  induction a using FreePreKA.ind
  rfl

end TD

end DiagonaLean.KAComm.KleeneAlgebra
