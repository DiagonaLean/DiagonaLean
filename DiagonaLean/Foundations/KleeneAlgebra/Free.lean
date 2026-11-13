/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.PreKleene
import Mathlib.Computability.Language
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # The free pre-Kleene algebra over a commutable set

The paper builds `T X` with category theory (`T = T' ∘ S` in Figure 1). This file uses an
equivalent concrete construction: regular-expression syntax over `X`, quotiented by the least
congruence that contains the pre-Kleene algebra axioms and `x y = y x` for every commuting pair
`C x y`. It also defines the morphism `lift f` into any pre-Kleene algebra whose images of
`C`-related generators commute, and the language interpretation for `C = Eq`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Sections 2.1 and 2.2
-/

open scoped Computability

namespace DiagonaLean.Foundations.KleeneAlgebra

/-- Regular-expression syntax over an alphabet `X`. -/
inductive RExp (X : Type*) where
  /-- The constant `0`. -/
  | zero
  /-- The constant `1`. -/
  | one
  /-- A generator `x ∈ X`. -/
  | sym (x : X)
  /-- The sum `e + f`. -/
  | plus (e f : RExp X)
  /-- The product `e * f`. -/
  | mul (e f : RExp X)
  /-- The star `e∗`. -/
  | star (e : RExp X)
  deriving DecidableEq

namespace RExp

variable {X : Type*}

/-- Provable equality in pre-Kleene algebra with commutation hypotheses `C`: the least
congruence containing the axioms of Section 2 and `x y = y x` for `C x y`. -/
inductive Equiv (C : X → X → Prop) : RExp X → RExp X → Prop where
  /-- Reflexivity. -/
  | refl (e) : Equiv C e e
  /-- Symmetry. -/
  | symm {e f} : Equiv C e f → Equiv C f e
  /-- Transitivity. -/
  | trans {e f g} : Equiv C e f → Equiv C f g → Equiv C e g
  /-- Congruence for `plus`. -/
  | plus {e e' f f'} : Equiv C e e' → Equiv C f f' → Equiv C (plus e f) (plus e' f')
  /-- Congruence for `mul`. -/
  | mul {e e' f f'} : Equiv C e e' → Equiv C f f' → Equiv C (mul e f) (mul e' f')
  /-- Congruence for `star`. -/
  | star {e e'} : Equiv C e e' → Equiv C (star e) (star e')
  /-- Addition is associative. -/
  | plus_assoc (e f g) : Equiv C (plus (plus e f) g) (plus e (plus f g))
  /-- Addition is commutative. -/
  | plus_comm (e f) : Equiv C (plus e f) (plus f e)
  /-- `0` is a left identity for addition. -/
  | zero_plus (e) : Equiv C (plus zero e) e
  /-- Addition is idempotent. -/
  | plus_idem (e) : Equiv C (plus e e) e
  /-- Multiplication is associative. -/
  | mul_assoc (e f g) : Equiv C (mul (mul e f) g) (mul e (mul f g))
  /-- `1` is a left identity for multiplication. -/
  | one_mul (e) : Equiv C (mul one e) e
  /-- `1` is a right identity for multiplication. -/
  | mul_one (e) : Equiv C (mul e one) e
  /-- `0` is a left zero for multiplication. -/
  | zero_mul (e) : Equiv C (mul zero e) zero
  /-- `0` is a right zero for multiplication. -/
  | mul_zero (e) : Equiv C (mul e zero) zero
  /-- Multiplication distributes over addition on the left. -/
  | left_distrib (e f g) : Equiv C (mul e (plus f g)) (plus (mul e f) (mul e g))
  /-- Multiplication distributes over addition on the right. -/
  | right_distrib (e f g) : Equiv C (mul (plus e f) g) (plus (mul e g) (mul f g))
  /-- Left unfolding `e∗ = 1 + e * e∗`. -/
  | unfold (e) : Equiv C (star e) (plus one (mul e (star e)))
  /-- Generators related by `C` commute. -/
  | comm {x y} : C x y → Equiv C (mul (sym x) (sym y)) (mul (sym y) (sym x))

/-- The setoid of provable equality. -/
def setoid (C : X → X → Prop) : Setoid (RExp X) where
  r := Equiv C
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- Interpretation of syntax in a pre-Kleene algebra. -/
def eval {α : Type*} [PreKleeneAlgebra α] (f : X → α) : RExp X → α
  | zero => 0
  | one => 1
  | sym x => f x
  | plus e g => eval f e + eval f g
  | mul e g => eval f e * eval f g
  | star e => (eval f e)∗

/-- Soundness: provably equal expressions have equal interpretations whenever `f` maps
`C`-related generators to commuting elements. -/
theorem eval_sound {α : Type*} [PreKleeneAlgebra α] {C : X → X → Prop} (f : X → α)
    (hf : ∀ x y, C x y → f x * f y = f y * f x) {e g : RExp X} (h : Equiv C e g) :
    eval f e = eval f g := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | plus _ _ ih₁ ih₂ => simp only [eval, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp only [eval, ih₁, ih₂]
  | star _ ih => simp only [eval, ih]
  | plus_assoc => exact add_assoc _ _ _
  | plus_comm => exact add_comm _ _
  | zero_plus => exact zero_add _
  | plus_idem => exact add_idem _
  | mul_assoc => exact mul_assoc _ _ _
  | one_mul => exact one_mul _
  | mul_one => exact mul_one _
  | zero_mul => exact zero_mul _
  | mul_zero => exact mul_zero _
  | left_distrib => exact mul_add _ _ _
  | right_distrib => exact add_mul _ _ _
  | unfold => exact kstar_unfold _
  | comm hxy => exact hf _ _ hxy

end RExp

/-- The free pre-Kleene algebra `T X` over `X` with commutation hypotheses `C`. -/
def FreePreKA (X : Type*) (C : X → X → Prop) : Type _ := Quotient (RExp.setoid C)

namespace FreePreKA

open RExp

variable {X : Type*} {C : X → X → Prop}

/-- The class of an expression. -/
def mk (e : RExp X) : FreePreKA X C := Quotient.mk (RExp.setoid C) e

/-- The generator `x ∈ X`. -/
def of (x : X) : FreePreKA X C := mk (sym x)

/-- Two classes are equal iff their expressions are provably equal. -/
theorem mk_eq_mk {e f : RExp X} : (mk e : FreePreKA X C) = mk f ↔ Equiv C e f :=
  Quotient.eq (r := RExp.setoid C)

/-- Provably equal expressions have equal classes. -/
theorem sound {e f : RExp X} (h : Equiv C e f) : (mk e : FreePreKA X C) = mk f :=
  mk_eq_mk.2 h

/-- Induction principle: a property of all classes `mk e` holds for every element. -/
@[elab_as_elim]
theorem ind {p : FreePreKA X C → Prop} (h : ∀ e, p (mk e)) (a : FreePreKA X C) : p a :=
  Quotient.inductionOn a h

/-- Zero is the class of `RExp.zero`. -/
instance : Zero (FreePreKA X C) := ⟨mk zero⟩
/-- One is the class of `RExp.one`. -/
instance : One (FreePreKA X C) := ⟨mk one⟩
/-- Addition is induced by `RExp.plus`. -/
instance : Add (FreePreKA X C) :=
  ⟨Quotient.map₂ plus fun _ _ h₁ _ _ h₂ => Equiv.plus h₁ h₂⟩
/-- Multiplication is induced by `RExp.mul`. -/
instance : Mul (FreePreKA X C) :=
  ⟨Quotient.map₂ RExp.mul fun _ _ h₁ _ _ h₂ => Equiv.mul h₁ h₂⟩
/-- Star is induced by `RExp.star`. -/
instance : KStar (FreePreKA X C) := ⟨Quotient.map star fun _ _ h => Equiv.star h⟩

/-- The class of `zero` is `0`. -/
@[simp] theorem mk_zero : (mk zero : FreePreKA X C) = 0 := rfl
/-- The class of `one` is `1`. -/
@[simp] theorem mk_one : (mk one : FreePreKA X C) = 1 := rfl
/-- `mk` sends `plus` to `+`. -/
@[simp] theorem mk_plus (e f : RExp X) : (mk (plus e f) : FreePreKA X C) = mk e + mk f := rfl
/-- `mk` sends `mul` to `*`. -/
@[simp] theorem mk_mul (e f : RExp X) : (mk (RExp.mul e f) : FreePreKA X C) = mk e * mk f := rfl
/-- `mk` sends `star` to `∗`. -/
@[simp] theorem mk_star (e : RExp X) : (mk (star e) : FreePreKA X C) = (mk e)∗ := rfl

/-- `FreePreKA X C` is a semiring. -/
instance : Semiring (FreePreKA X C) where
  add_assoc a b c := by
    induction a using ind; induction b using ind; induction c using ind
    exact sound (Equiv.plus_assoc _ _ _)
  zero_add a := by induction a using ind; exact sound (Equiv.zero_plus _)
  add_zero a := by
    induction a using ind
    exact sound ((Equiv.plus_comm _ _).trans (Equiv.zero_plus _))
  add_comm a b := by
    induction a using ind; induction b using ind; exact sound (Equiv.plus_comm _ _)
  mul_assoc a b c := by
    induction a using ind; induction b using ind; induction c using ind
    exact sound (Equiv.mul_assoc _ _ _)
  one_mul a := by induction a using ind; exact sound (Equiv.one_mul _)
  mul_one a := by induction a using ind; exact sound (Equiv.mul_one _)
  zero_mul a := by induction a using ind; exact sound (Equiv.zero_mul _)
  mul_zero a := by induction a using ind; exact sound (Equiv.mul_zero _)
  left_distrib a b c := by
    induction a using ind; induction b using ind; induction c using ind
    exact sound (Equiv.left_distrib _ _ _)
  right_distrib a b c := by
    induction a using ind; induction b using ind; induction c using ind
    exact sound (Equiv.right_distrib _ _ _)
  nsmul := nsmulRec

/-- Addition in `FreePreKA X C` is idempotent. -/
instance : IdemSemiring (FreePreKA X C) :=
  IdemSemiring.ofSemiring fun a => by induction a using ind; exact sound (Equiv.plus_idem _)

/-- `FreePreKA X C` is a pre-Kleene algebra. -/
instance : PreKleeneAlgebra (FreePreKA X C) where
  kstar_unfold a := by induction a using ind; exact sound (Equiv.unfold _)

/-- Generators related by `C` commute in `FreePreKA X C`. -/
theorem of_comm {x y : X} (h : C x y) : (of x : FreePreKA X C) * of y = of y * of x :=
  sound (Equiv.comm h)

section lift

variable {α : Type*} [PreKleeneAlgebra α]

/-- The morphism `T X → α` determined by its action on generators. -/
def lift (f : X → α) (hf : ∀ x y, C x y → f x * f y = f y * f x) : FreePreKA X C → α :=
  Quotient.lift (RExp.eval f) fun _ _ h => RExp.eval_sound f hf h

variable (f : X → α) (hf : ∀ x y, C x y → f x * f y = f y * f x)

/-- `lift f` on the class of `e` is the interpretation of `e`. -/
@[simp] theorem lift_mk (e : RExp X) : lift f hf (mk e) = e.eval f := rfl
/-- `lift f` sends the generator `x` to `f x`. -/
@[simp] theorem lift_of (x : X) : lift f hf (of x) = f x := rfl
/-- `lift f` preserves `0`. -/
@[simp] theorem lift_zero : lift f hf 0 = 0 := rfl
/-- `lift f` preserves `1`. -/
@[simp] theorem lift_one : lift f hf 1 = 1 := rfl
/-- `lift f` preserves addition. -/
@[simp] theorem lift_add (a b : FreePreKA X C) : lift f hf (a + b) = lift f hf a + lift f hf b := by
  induction a using ind; induction b using ind; rfl
/-- `lift f` preserves multiplication. -/
@[simp] theorem lift_mul (a b : FreePreKA X C) : lift f hf (a * b) = lift f hf a * lift f hf b := by
  induction a using ind; induction b using ind; rfl
/-- `lift f` preserves star. -/
@[simp] theorem lift_kstar (a : FreePreKA X C) : lift f hf a∗ = (lift f hf a)∗ := by
  induction a using ind; rfl

/-- `lift` as an additive monoid morphism. -/
def liftAddHom : FreePreKA X C →+ α where
  toFun := lift f hf
  map_zero' := lift_zero f hf
  map_add' := lift_add f hf

/-- `lift f` preserves finite sums. -/
theorem lift_sum {ι : Type*} (s : Finset ι) (g : ι → FreePreKA X C) :
    lift f hf (∑ i ∈ s, g i) = ∑ i ∈ s, lift f hf (g i) :=
  map_sum (liftAddHom f hf) g s

/-- `lift f` is monotone. -/
theorem lift_mono {a b : FreePreKA X C} (h : a ≤ b) : lift f hf a ≤ lift f hf b := by
  rw [← add_eq_right_iff_le] at h ⊢
  rw [← lift_add, h]

end lift

section lang

/-- The language interpretation `l : T X → L X` for discrete commutation (`C = Eq`). Each
generator `x` goes to the singleton `{[x]}`. -/
def lang : FreePreKA X (· = ·) → Language X :=
  lift (fun x => ({[x]} : Set (List X))) fun _ _ h => by subst h; rfl

/-- The language of `1` is the language `{[]}`. -/
@[simp] theorem lang_one : lang (1 : FreePreKA X (· = ·)) = 1 := rfl

/-- `lang` preserves star. -/
@[simp] theorem lang_kstar (a : FreePreKA X (· = ·)) : lang a∗ = (lang a)∗ :=
  lift_kstar _ _ a

end lang

end FreePreKA

end DiagonaLean.Foundations.KleeneAlgebra
