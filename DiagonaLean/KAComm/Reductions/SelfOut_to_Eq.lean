/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.FreeKA
import DiagonaLean.KAComm.Reductions.SelfOut_to_ModelLe

@[expose] public section

/-! # Theorem 18: equality on `T Σ̈`, `K Σ̈` and `L Σ̈`

The paper states Theorem 18 for equality: if the language map factors as `l = g ∘ l'` with
`l' : T Σ̈ → X` (`LangFactor X`), then equality on `X` is undecidable. Since `e ≤ f` means
`e + f = f`, the reduction sends `M` to `(eL + eR, eR)`, where `(eL, eR) = kaRed M`. This file
proves that form, specializes it to `T Σ̈`, `K Σ̈` and `L Σ̈`, and relates the inequalities
`Provable` and `ModelLe` of `SelfOut_to_ModelLe.lean` to equality.

Unlike the paper, the separation statements (`SepReduces`, `InsepUndecidable`) do not ask the
separating function to be computable, so the machine forms assume a machine computing `eqRed`; the
result with no such hypothesis is `not_machineDecidable_selfEq`, for the paper's set `A'`. The
alphabet here is `ℕ`, not `{0, 1}`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, Section 3
-/

open scoped Computability

namespace DiagonaLean.KAComm.Undec

open DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Undecidable DiagonaLean.Synthetic.Definitions RExp TD FreePreKA

variable {X : Type*}

/-- The diagram of Theorem 18: the language map `l` of `T Σ̈` factors through `l' : T Σ̈ → X`. -/
structure LangFactor (X : Type*) where
  /-- The map out of `T Σ̈`. -/
  l' : TD ℕ → X
  /-- The map into the language model. -/
  g : X → _root_.SetSemiring (W ℕ)
  /-- The triangle commutes. -/
  fac : ∀ a, g (l' a) = pl a

/-- Equality on `X`, as a predicate on pairs. -/
def EqOn (X : Type*) (p : X × X) : Prop := p.1 = p.2

/-- The paper's `X=` on syntax: the two expressions denote the same element of `X`. -/
def EqVia (F : LangFactor X) (i : Inst) : Prop := F.l' (mk i.1) = F.l' (mk i.2)

/-- `(eL + eR, eR)`, the syntax of the paper's `η`. It does not depend on `X`. -/
def eqRed (M : EncodableTM Bool) : Inst := (plus (kaRed M).1 (kaRed M).2, (kaRed M).2)

/-- The paper's `η⟨M, n⟩ = ⟨l'(eL + eR), l'(eR)⟩`. -/
def eta (F : LangFactor X) (M : EncodableTM Bool) : X × X :=
  (F.l' (mk (eqRed M).1), F.l' (mk (eqRed M).2))

/-- If `M` outputs `true` on its own code, then `eqRed M` holds via `F`. -/
theorem eqVia_eqRed_pos (F : LangFactor X) {M : EncodableTM Bool} (h : SelfOut true M) :
    EqVia F (eqRed M) :=
  congrArg F.l' (add_eq_right_iff_le.2 (kaRed_pos h))

/-- If `M` outputs `false` on its own code, then `eqRed M` fails via `F`. -/
theorem eqVia_eqRed_neg (F : LangFactor X) {M : EncodableTM Bool} (h : SelfOut false M) :
    ¬ EqVia F (eqRed M) := fun hEq => by
  have hl := congrArg F.g hEq
  rw [F.fac, F.fac] at hl
  refine kaRed_neg h (add_eq_right_iff_le.1 ?_)
  rwa [eqRed, mk_plus, pl_add] at hl

/-- **Theorem 18, synthetic form on pairs of elements of `X`.** -/
def sepReducesEqOn (F : LangFactor X) : SepReduces (SelfOut true) (SelfOut false) (EqOn X) :=
  ⟨eta F, fun _ h => eqVia_eqRed_pos F h, fun _ h => eqVia_eqRed_neg F h⟩

/-- **Theorem 18, synthetic form on pairs of expressions.** -/
def sepReducesEqVia (F : LangFactor X) : SepReduces (SelfOut true) (SelfOut false) (EqVia F) :=
  ⟨eqRed, fun _ h => eqVia_eqRed_pos F h, fun _ h => eqVia_eqRed_neg F h⟩

/-- **Theorem 18, machine form.** If `l'` is computable, in the sense that some machine computes
`η`, then no machine decides equality on `X`. The paper assumes the computability of `η`. -/
theorem not_machineDecidable_eqOn_of_computes (F : LangFactor X) {enc : X × X → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encodeBoolTM enc (eta F)) : ¬ MachineDecidable enc (EqOn X) :=
  not_machineDecidable_of_sepReduces (sepReducesEqOn F) hR

/-- Machine form on pairs of expressions, which is the natural input for `T Σ̈` and `K Σ̈`, whose
elements are equivalence classes. The one hypothesis is that a machine computes `eqRed`. -/
theorem not_machineDecidable_eqVia_of_computes (F : LangFactor X) {enc : Inst → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encodeBoolTM enc eqRed) :
    ¬ MachineDecidable enc (EqVia F) :=
  not_machineDecidable_of_sepReduces (sepReducesEqVia F) hR

/-- `X = T Σ̈`. -/
noncomputable def factorT : LangFactor (TD ℕ) := ⟨id, pl, fun _ => rfl⟩

/-- `X = K Σ̈`. -/
noncomputable def factorK : LangFactor (FreeKA (ℕ ⊕ ℕ) DComm) := ⟨FreeKA.ofPre, plK, plK_ofPre⟩

/-- `X = L Σ̈`. -/
noncomputable def factorL : LangFactor (_root_.SetSemiring (W ℕ)) := ⟨pl, id, fun _ => rfl⟩

/-- Equality via `factorT` is provable equality in pre-Kleene algebra. -/
theorem eqVia_factorT (i : Inst) : EqVia factorT i ↔ Equiv DComm i.1 i.2 := mk_eq_mk

/-- Equality via `factorK` is provable equality in Kleene algebra. -/
theorem eqVia_factorK (i : Inst) : EqVia factorK i ↔ KAEquiv DComm i.1 i.2 := FreeKA.mk_eq_mk

/-- Equality via `factorL` is equality of languages. -/
theorem eqVia_factorL (i : Inst) : EqVia factorL i ↔ pl (mk i.1 : TD ℕ) = pl (mk i.2) := Iff.rfl

/-- `eqRed` separates the inseparable pair by provable equality of terms in pre-Kleene algebra
with commutativity. -/
theorem termEq_separated : InsepUndecidable fun i : Inst => Equiv DComm i.1 i.2 :=
  ⟨⟨eqRed, fun _ h => (eqVia_factorT _).1 (eqVia_eqRed_pos factorT h),
    fun _ h hE => eqVia_eqRed_neg factorT h ((eqVia_factorT _).2 hE)⟩⟩

/-- `eqRed` separates the inseparable pair by provable equality of terms in Kleene algebra with
commutativity, the theory of the paper's title. -/
theorem kaTermEq_separated : InsepUndecidable fun i : Inst => KAEquiv DComm i.1 i.2 :=
  ⟨⟨eqRed, fun _ h => (eqVia_factorK _).1 (eqVia_eqRed_pos factorK h),
    fun _ h hE => eqVia_eqRed_neg factorK h ((eqVia_factorK _).2 hE)⟩⟩

/-- `eqRed` separates the inseparable pair by equality of the languages of two terms. -/
theorem langEq_separated : InsepUndecidable fun i : Inst => pl (mk i.1 : TD ℕ) = pl (mk i.2) :=
  ⟨sepReducesEqVia factorL⟩

/-- `Provable` is provable equality of `e + f` and `f` in `T Σ̈`. -/
theorem provable_iff_equiv (i : Inst) : Provable i ↔ Equiv DComm (plus i.1 i.2) i.2 := mk_le_mk

/-- `ModelLe` is equality of the languages of `e + f` and `f`. -/
theorem modelLe_iff_langEq (i : Inst) :
    ModelLe i ↔ pl (mk (plus i.1 i.2) : TD ℕ) = pl (mk i.2) := by
  rw [mk_plus, pl_add]
  exact add_eq_right_iff_le.symm

/-- `e ≤ f` is provable in Kleene algebra with commutativity. -/
def KAProvable (i : Inst) : Prop := KAEquiv DComm (plus i.1 i.2) i.2

/-- `KAProvable i` holds iff `i.1 ≤ i.2` in the free Kleene algebra. -/
theorem kaProvable_iff_le (i : Inst) :
    KAProvable i ↔ (FreeKA.mk i.1 : FreeKA (ℕ ⊕ ℕ) DComm) ≤ FreeKA.mk i.2 :=
  FreeKA.mk_eq_mk.symm.trans (add_eq_right_iff_le (a := FreeKA.mk i.1) (b := FreeKA.mk i.2))

/-- An inequality provable in `T Σ̈` is provable in Kleene algebra. -/
theorem Provable.kaProvable {i : Inst} (h : Provable i) : KAProvable i :=
  .ofEquiv ((provable_iff_equiv i).1 h)

/-- An inequality provable in Kleene algebra holds in the language model. -/
theorem KAProvable.modelLe {i : Inst} (h : KAProvable i) : ModelLe i :=
  (modelLe_iff_langEq i).2 (RExp.eval_ka_sound gen gen_comm h)

/-- **`KAProvable` satisfies `InsepUndecidable`**, since it lies between `Provable` and
`ModelLe`. -/
theorem insepUndecidable_kaProvable : InsepUndecidable KAProvable :=
  insepUndecidable_of_between _ (fun _ h => h.kaProvable) fun _ h => h.modelLe

section Synthetic

open DiagonaLean.Synthetic.Notation

/-- Equality via `F` is language equality, when `F` identifies terms with equal languages. -/
theorem eqVia_iff_langEq (F : LangFactor X) (hF : ∀ a b : TD ℕ, pl a = pl b → F.l' a = F.l' b)
    (i : Inst) : EqVia F i ↔ pl (mk i.1 : TD ℕ) = pl (mk i.2) :=
  ⟨fun h => by simpa only [F.fac] using congrArg F.g h, hF _ _⟩

/-- `(eL + eR, eR)` for the `HaltProblem` instance `haltRed`. -/
def haltEqRed (p : EncodableTM Bool × List Bool) : Inst :=
  (plus (haltRed p).1 (haltRed p).2, (haltRed p).2)

/-- `HaltProblem` many-one reduces to the failure of equality on `X`, for any `X` whose equality
agrees with language equality. -/
def haltReducesNotEqVia (F : LangFactor X)
    (hF : ∀ a b : TD ℕ, pl a = pl b → F.l' a = F.l' b) : HaltProblem ⪯ₘ Complement (EqVia F) :=
  ⟨haltEqRed, fun p => (halt_iff_not_modelLe p).trans
    (not_congr ((modelLe_iff_langEq _).trans (eqVia_iff_langEq F hF (haltEqRed p)).symm))⟩

/-- **`Undecidable` for the failure of equality on `X`.** -/
theorem undecidable_not_eqVia (F : LangFactor X)
    (hF : ∀ a b : TD ℕ, pl a = pl b → F.l' a = F.l' b) : Undecidable (Complement (EqVia F)) :=
  ⟨haltReducesNotEqVia F hF⟩

/-- **`Undecidable` for language inequality of two terms.** -/
theorem undecidable_not_langEq :
    Undecidable (Complement (@LangEq.DecisionProblem ℕ)) :=
  undecidable_not_eqVia factorL fun _ _ h => h

/-- The machines whose instance `eqRed M` holds in `X`: the paper's set `A'` (Theorem 19). -/
def SelfEq (F : LangFactor X) (M : EncodableTM Bool) : Prop := EqVia F (eqRed M)

/-- `SelfEq F` many-one reduces to equality on `X`, through the concrete `eqRed`. -/
def selfEqReduces (F : LangFactor X) : SelfEq F ⪯ₘ EqVia F := ⟨eqRed, fun _ => Iff.rfl⟩

/-- **No Turing machine decides `SelfEq F`.** There is no computability hypothesis: `SelfEq F`
separates the inseparable pair, and its input is the machine's own code. -/
theorem not_machineDecidable_selfEq (F : LangFactor X) :
    ¬ MachineDecidable encodeBoolTM (SelfEq F) :=
  selfOut_inseparable ⟨fun _ h => eqVia_eqRed_pos F h, fun _ h => eqVia_eqRed_neg F h⟩

/-- The case `X = T Σ̈`: on machine codes, provable equality in pre-KA has no machine decider. -/
theorem not_machineDecidable_termEq :
    ¬ MachineDecidable encodeBoolTM fun M => Equiv DComm (eqRed M).1 (eqRed M).2 := fun ⟨D, hD⟩ =>
  not_machineDecidable_selfEq factorT ⟨D, fun M =>
    ⟨fun h => (hD M).1 ((eqVia_factorT _).1 h), fun h => (hD M).2 (h ∘ (eqVia_factorT _).2)⟩⟩

/-- The case `X = K Σ̈`: on machine codes, provable equality in KA has no machine decider. -/
theorem not_machineDecidable_kaTermEq :
    ¬ MachineDecidable encodeBoolTM fun M => KAEquiv DComm (eqRed M).1 (eqRed M).2 :=
  fun ⟨D, hD⟩ => not_machineDecidable_selfEq factorK ⟨D, fun M =>
    ⟨fun h => (hD M).1 ((eqVia_factorK _).1 h), fun h => (hD M).2 (h ∘ (eqVia_factorK _).2)⟩⟩

end Synthetic

end DiagonaLean.KAComm.Undec
