/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.FreeKA
import DiagonaLean.KleeneAlgebra.Reductions.SelfOut_to_ModelLe

@[expose] public section

/-! # Theorem 18 as stated in the paper: equality on `T Σ̈`, `K Σ̈` and `L Σ̈`

`Reductions/SelfOut_to_ModelLe.lean` works with the inequalities `Provable` (in `T Σ̈`) and `ModelLe` (in the
language model). The paper states Theorem 18 for *equality*. Given a factoring of the language map

  `l = g ∘ l'`, with `l' : T Σ̈ → X` and `g : X → L Σ̈`,

equality on `X` is undecidable, and in particular equality on `T Σ̈`, `K Σ̈` and `L Σ̈`. This file
proves that form and connects it to the inequalities.

## How the inequality becomes an equality

`e ≤ f` means `e + f = f`. So the reduction sends a machine to `(eL + eR, eR)`, where
`(eL, eR) = kaRed M`. If `M` outputs `1`, then `eL ≤ eR` in `T Σ̈`, so the two sides are equal in `T Σ̈`
and hence have equal images under `l'`. If `M` outputs `0` and the images under `l'` were equal,
applying `g` would give `l(eL) + l(eR) = l(eR)`, which is `ModelLe (eL, eR)`, contradicting
`kaRed_neg`.

## Main statements

* `LangFactor X`: the paper's diagram.
* `sepReduces_eqOn`: the separation reduction for equality on `X`, on pairs of elements of `X`.
* `sepReduces_eqVia`: the same, on pairs of expressions.
* `not_machineDecidable_eqOn_of_computes`: no Turing machine decides equality on `X`, given a machine computing `η`.
* `termEq_separated`, `kaTermEq_separated`, `langEq_separated`: the three named cases, as
  separation statements. See the warning below.
* `provable_iff_equiv`, `modelLe_iff_langEq`, `kaProvable_iff_le`: inequalities as equalities.
* `insepUndecidable_kaProvable`: the Kleene algebra case of `insepUndecidable_of_between`.
* `undecidable_not_eqVia`, `undecidable_not_langEq`: `Undecidable`, through `HALT ⪯ₘ`.
* `selfEq_reduces`, `not_machineDecidable_selfEq`, `not_machineDecidable_termEq`,
  `not_machineDecidable_kaTermEq`: no machine decides the problem on machine codes.

## Differences from the paper

`InsepUndecidable p` and `SepReduces` do not by themselves say that `p` is undecidable. They ask
for a function that separates the pair, and do not ask that it be computable. So the `_separated`
theorems are named for what they state. The content that carries over to computation is that the
reduction is the concrete `eqRed`, together with `not_machineDecidable_eqOn_of_computes` and
`not_machineDecidable_eqVia_of_computes`, which conclude that no Turing machine decides equality, given a machine
that computes the reduction. That machine is not constructed (`GAPS.md`, item 1).

The alphabet is `ℕ`, not `{0, 1}`: `kaRed` renames each machine's letters to natural numbers,
where the paper encodes them as binary strings. See `GAPS.md`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, §3
-/

open scoped Computability

namespace DiagonaLean.KAComm.Undec

open Cslib.Turing SingleTapeTM DiagonaLean.Halt.Encoding DiagonaLean.Halt.Undecidable
  DiagonaLean.Synthetic.Definitions RExp TD FreePreKA

variable {X : Type*}

/-! ### The paper's diagram -/

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

theorem eqVia_eqRed_pos (F : LangFactor X) {M : EncodableTM Bool} (h : SelfOut true M) :
    EqVia F (eqRed M) :=
  congrArg F.l' (add_eq_right_iff_le.2 (kaRed_pos h))

theorem eqVia_eqRed_neg (F : LangFactor X) {M : EncodableTM Bool} (h : SelfOut false M) :
    ¬ EqVia F (eqRed M) := fun hEq => by
  have hl := congrArg F.g hEq
  rw [F.fac, F.fac] at hl
  refine kaRed_neg h (add_eq_right_iff_le.1 ?_)
  rwa [eqRed, mk_plus, pl_add] at hl

/-! ### Theorem 18 -/

/-- **Theorem 18, synthetic form on pairs of elements of `X`.** -/
def sepReduces_eqOn (F : LangFactor X) : SepReduces (SelfOut true) (SelfOut false) (EqOn X) :=
  ⟨eta F, fun _ h => eqVia_eqRed_pos F h, fun _ h => eqVia_eqRed_neg F h⟩

/-- **Theorem 18, synthetic form on pairs of expressions.** -/
def sepReduces_eqVia (F : LangFactor X) : SepReduces (SelfOut true) (SelfOut false) (EqVia F) :=
  ⟨eqRed, fun _ h => eqVia_eqRed_pos F h, fun _ h => eqVia_eqRed_neg F h⟩

/-- **Theorem 18, machine form.** If `l'` is computable, in the sense that some machine computes
`η`, then no machine decides equality on `X`. The paper assumes the computability of `η`. -/
theorem not_machineDecidable_eqOn_of_computes (F : LangFactor X) {enc : X × X → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encodeBoolTM enc (eta F)) : ¬ MachineDecidable enc (EqOn X) :=
  not_machineDecidable_of_sepReduces (sepReduces_eqOn F) hR

/-- Machine form on pairs of expressions, which is the natural input for `T Σ̈` and `K Σ̈`, whose
elements are equivalence classes. The one hypothesis is that a machine computes `eqRed`. -/
theorem not_machineDecidable_eqVia_of_computes (F : LangFactor X) {enc : Inst → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encodeBoolTM enc eqRed) :
    ¬ MachineDecidable enc (EqVia F) :=
  not_machineDecidable_of_sepReduces (sepReduces_eqVia F) hR

/-! ### The three named cases -/

/-- `X = T Σ̈`. -/
noncomputable def factorT : LangFactor (TD ℕ) := ⟨id, pl, fun _ => rfl⟩

/-- `X = K Σ̈`. -/
noncomputable def factorK : LangFactor (FreeKA (ℕ ⊕ ℕ) DComm) := ⟨FreeKA.ofPre, plK, plK_ofPre⟩

/-- `X = L Σ̈`. -/
noncomputable def factorL : LangFactor (_root_.SetSemiring (W ℕ)) := ⟨pl, id, fun _ => rfl⟩

theorem eqVia_factorT (i : Inst) : EqVia factorT i ↔ Equiv DComm i.1 i.2 := mk_eq_mk

theorem eqVia_factorK (i : Inst) : EqVia factorK i ↔ KAEquiv DComm i.1 i.2 := FreeKA.mk_eq_mk

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
  ⟨sepReduces_eqVia factorL⟩

/-! ### From inequalities to equalities

These relate the predicates of `Reductions/SelfOut_to_ModelLe.lean` to equality. -/

/-- `Provable` is provable equality of `e + f` and `f` in `T Σ̈`. -/
theorem provable_iff_equiv (i : Inst) : Provable i ↔ Equiv DComm (plus i.1 i.2) i.2 := mk_le_mk

/-- `ModelLe` is equality of the languages of `e + f` and `f`. -/
theorem modelLe_iff_langEq (i : Inst) :
    ModelLe i ↔ pl (mk (plus i.1 i.2) : TD ℕ) = pl (mk i.2) := by
  rw [mk_plus, pl_add]
  exact add_eq_right_iff_le.symm

/-- `e ≤ f` is provable in Kleene algebra with commutativity. -/
def KAProvable (i : Inst) : Prop := KAEquiv DComm (plus i.1 i.2) i.2

theorem kaProvable_iff_le (i : Inst) :
    KAProvable i ↔ (FreeKA.mk i.1 : FreeKA (ℕ ⊕ ℕ) DComm) ≤ FreeKA.mk i.2 :=
  FreeKA.mk_eq_mk.symm.trans (add_eq_right_iff_le (a := FreeKA.mk i.1) (b := FreeKA.mk i.2))

theorem Provable.kaProvable {i : Inst} (h : Provable i) : KAProvable i :=
  .ofEquiv ((provable_iff_equiv i).1 h)

theorem KAProvable.modelLe {i : Inst} (h : KAProvable i) : ModelLe i :=
  (modelLe_iff_langEq i).2 (RExp.eval_ka_sound gen gen_comm h)

/-- **`KAProvable` lies between `Provable` and `ModelLe`,** so `kaRed` covers Kleene algebra. -/
theorem insepUndecidable_kaProvable : InsepUndecidable KAProvable :=
  insepUndecidable_of_between _ (fun _ h => h.kaProvable) fun _ h => h.modelLe

/-! ### In the synthetic framework

`Undecidable p` is `Nonempty (HALT ⪯ₘ p)`, which asks for an exact `HALT x ↔ p (f x)`. The two
sides of the paper's theory need different treatment.

* **Language equality.** For a diverging machine the inequality holds in the language model, so
  halting is exactly its failure. This gives `Undecidable` for the complement of equality on any
  `X` whose equality agrees with language equality (`undecidable_not_eqVia`,
  `undecidable_not_langEq`).
* **`T Σ̈` and `K Σ̈`.** `eqRed` is only known to behave on machines that output a bit, so it gives
  no many-one reduction from `HALT`. We instead take the source problem `SelfEq F`, the machines
  `M` with `eqRed M` true in `X`. It many-one reduces to equality on `X` (`selfEq_reduces`), and no
  Turing machine decides it (`not_machineDecidable_selfEq`), with no computability hypothesis. This
  is the set `A'` of the paper's Theorem 19. `HALT ⪯ₘ` equality on `T Σ̈` or `K Σ̈` is `GAPS.md`,
  item 2. -/

section Synthetic

open DiagonaLean.Synthetic.Notation

/-- Equality via `F` is language equality, when `F` identifies terms with equal languages. -/
theorem eqVia_iff_langEq (F : LangFactor X) (hF : ∀ a b : TD ℕ, pl a = pl b → F.l' a = F.l' b)
    (i : Inst) : EqVia F i ↔ pl (mk i.1 : TD ℕ) = pl (mk i.2) :=
  ⟨fun h => by simpa only [F.fac] using congrArg F.g h, hF _ _⟩

/-- `(eL + eR, eR)` for the `HALT` instance `haltRed`. -/
def haltEqRed (p : EncodableTM Bool × List Bool) : Inst :=
  (plus (haltRed p).1 (haltRed p).2, (haltRed p).2)

/-- `HALT` many-one reduces to the failure of equality on `X`, for any `X` whose equality agrees
with language equality. -/
def haltReduces_not_eqVia (F : LangFactor X)
    (hF : ∀ a b : TD ℕ, pl a = pl b → F.l' a = F.l' b) : HALT ⪯ₘ Complement (EqVia F) :=
  ⟨haltEqRed, fun p => (halt_iff_not_modelLe p).trans
    (not_congr ((modelLe_iff_langEq _).trans (eqVia_iff_langEq F hF (haltEqRed p)).symm))⟩

/-- **`Undecidable` for the failure of equality on `X`.** -/
theorem undecidable_not_eqVia (F : LangFactor X)
    (hF : ∀ a b : TD ℕ, pl a = pl b → F.l' a = F.l' b) : Undecidable (Complement (EqVia F)) :=
  ⟨haltReduces_not_eqVia F hF⟩

/-- **`Undecidable` for language inequality of two terms.** -/
theorem undecidable_not_langEq :
    Undecidable (Complement fun i : Inst => pl (mk i.1 : TD ℕ) = pl (mk i.2)) :=
  undecidable_not_eqVia factorL fun _ _ h => h

/-- The machines whose instance `eqRed M` holds in `X`: the paper's set `A'` (Theorem 19). -/
def SelfEq (F : LangFactor X) (M : EncodableTM Bool) : Prop := EqVia F (eqRed M)

/-- `SelfEq F` many-one reduces to equality on `X`, through the concrete `eqRed`. -/
def selfEq_reduces (F : LangFactor X) : SelfEq F ⪯ₘ EqVia F := ⟨eqRed, fun _ => Iff.rfl⟩

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
