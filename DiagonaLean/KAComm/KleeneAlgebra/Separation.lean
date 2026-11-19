/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KleeneAlgebra.Inequality
import DiagonaLean.KAComm.KleeneAlgebra.MachineEncoding.Halting
import DiagonaLean.Halt.Inseparable
import DiagonaLean.Synthetic.Undecidability

@[expose] public section

/-! # Separating the pair `SelfOut true`, `SelfOut false` by Kleene algebra

`kaRed` sends a machine that outputs `1` on its own code to an inequality provable in pre-Kleene
algebra, and a machine that outputs `0` to an inequality that fails in the language model
(`kaRed_pos`, `kaRed_neg`). So every theory between `Provable` and `ModelLe` separates the
computably inseparable pair `SelfOut true`, `SelfOut false`, and no machine decides it given a
machine that computes `kaRed` (`not_machineDecidable_of_between`). The same statements without that
hypothesis are in `Between.lean`, which uses the interpreter's instances instead of `kaRed`.
`haltRed` drops the halting term: `M` halts on `w` iff `haltRed (M, w)` fails in the language
model.

For equality, the paper states Theorem 18 for any factoring `l = g ∘ l'` of the language map through
`l' : T Σ̈ → X` (`LangFactor X`). Since `e ≤ f` means `e + f = f`, `eqRed` sends `M` to
`(eL + eR, eR)`, where `(eL, eR) = kaRed M`. `factorT`, `factorK` and `factorL` are the factorings
through `T Σ̈`, `K Σ̈` and `L Σ̈`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

open scoped Computability

namespace DiagonaLean.KAComm.KleeneAlgebra

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Undecidable DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation
  DiagonaLean.Halt.Inseparable DiagonaLean.Foundations.Computability RExp TD FreePreKA

variable {X : Type*}

/-- **The reduction.** The inequality `(init)_r R_M∗ ≤ Σ∗ (C_M + T_true)_r + Σ∗ Σ^≠ ρ_M` for `M`
run on its own code, with letters renamed to their codes. -/
def kaRed (M : EncodableTM Bool) : Inst :=
  letI := M.stateEncodable
  letI : DecidableEq M.State := Encodable.decidableEqOfEncodable _
  ((Enc.lhsS M.toSingleTapeTM (encodeBoolTM M)).map (dmap Encodable.encode),
    (Enc.rhsS M.toSingleTapeTM true).map (dmap Encodable.encode))

/-- If `M` outputs `true` on its own code, then `kaRed M` is provable. -/
theorem kaRed_pos {M : EncodableTM Bool} (h : SelfOut true M) : Provable (kaRed M) := by
  let := M.stateEncodable
  let : DecidableEq M.State := Encodable.decidableEqOfEncodable _
  exact le_map _ (Enc.le_of_outputs h)

/-- If `M` outputs `false` on its own code, then `kaRed M` fails in the language model. -/
theorem kaRed_neg {M : EncodableTM Bool} (h : SelfOut false M) : ¬ ModelLe (kaRed M) := by
  let := M.stateEncodable
  let : DecidableEq M.State := Encodable.decidableEqOfEncodable _
  exact fun hle => Enc.not_pl_le_of_outputs h (by decide)
    (pl_le_of_map Encodable.encode_injective hle)

/-- **No Turing machine decides any theory between pre-KA provability and the language model**,
for any encoding of instances under which a Turing machine computes `kaRed`. For the encoding
`encNat`, `not_machineDecidable_between` proves this without the hypothesis. -/
theorem not_machineDecidable_of_between {enc : Inst → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encodeBoolTM enc kaRed) (S : Inst → Prop)
    (h₁ : ∀ i, Provable i → S i) (h₂ : ∀ i, S i → ModelLe i) : ¬ MachineDecidable enc S :=
  not_machineDecidable_of_separation (f := kaRed) (fun _ h => h₁ _ (kaRed_pos h))
    (fun _ h hS => kaRed_neg h (h₂ _ hS)) hR

/-- **The reduction from `HaltProblem`.** `(M, w) ↦ ((init w)_r R_M∗, Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ_M)`,
with letters renamed to their codes. -/
def haltRed (p : EncodableTM Bool × List Bool) : Inst :=
  letI := p.1.stateEncodable
  letI : DecidableEq p.1.State := Encodable.decidableEqOfEncodable _
  ((Enc.lhsS p.1.toSingleTapeTM p.2).map (dmap Encodable.encode),
    (Enc.rhsHS p.1.toSingleTapeTM).map (dmap Encodable.encode))

/-- `M` halts on `w` iff the instance `haltRed (M, w)` fails in the language model. -/
theorem halt_iff_not_modelLe (p : EncodableTM Bool × List Bool) :
    HaltProblem p ↔ ¬ ModelLe (haltRed p) := by
  obtain ⟨M, w⟩ := p
  let := M.stateEncodable
  let : DecidableEq M.State := Encodable.decidableEqOfEncodable _
  show Halts M.toSingleTapeTM w ↔ _
  rw [Enc.halts_iff_not_pl_le_syntax]
  exact not_congr ⟨pl_map_le_of_le _, pl_le_of_map Encodable.encode_injective⟩

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

/-- **Theorem 18, machine form.** If `l'` is computable, in the sense that some machine computes
`η`, then no machine decides equality on `X`. The paper assumes the computability of `η`.
`not_machineDecidable_eqOn` (`Between.lean`) assumes instead that a machine computes `l'` on the
codes of expressions. -/
theorem not_machineDecidable_eqOn_of_computes (F : LangFactor X) {enc : X × X → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encodeBoolTM enc (eta F)) : ¬ MachineDecidable enc (EqOn X) :=
  not_machineDecidable_of_separation (f := eta F) (fun _ h => eqVia_eqRed_pos F h)
    (fun _ h => eqVia_eqRed_neg F h) hR

/-- Machine form on pairs of expressions, which is the natural input for `T Σ̈` and `K Σ̈`, whose
elements are equivalence classes. The one hypothesis is that a machine computes `eqRed`. -/
theorem not_machineDecidable_eqVia_of_computes (F : LangFactor X) {enc : Inst → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encodeBoolTM enc eqRed) :
    ¬ MachineDecidable enc (EqVia F) :=
  not_machineDecidable_of_separation (f := eqRed) (fun _ h => eqVia_eqRed_pos F h)
    (fun _ h => eqVia_eqRed_neg F h) hR

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
def undecidableNotEqVia (F : LangFactor X)
    (hF : ∀ a b : TD ℕ, pl a = pl b → F.l' a = F.l' b) : Undecidable (Complement (EqVia F)) :=
  haltReducesNotEqVia F hF

/-- The machines whose instance `eqRed M` holds in `X`: the paper's set `A'` (Theorem 19). -/
def SelfEq (F : LangFactor X) (M : EncodableTM Bool) : Prop := EqVia F (eqRed M)

/-- `SelfEq F` many-one reduces to equality on `X`, through the concrete `eqRed`. -/
def selfEqReduces (F : LangFactor X) : SelfEq F ⪯ₘ EqVia F := ⟨eqRed, fun _ => Iff.rfl⟩

/-- **No Turing machine decides `SelfEq F`.** There is no computability hypothesis: `SelfEq F`
separates the inseparable pair, and its input is the machine's own code. -/
theorem not_machineDecidable_selfEq (F : LangFactor X) :
    ¬ MachineDecidable encodeBoolTM (SelfEq F) :=
  selfOut_inseparable ⟨fun _ h => eqVia_eqRed_pos F h, fun _ h => eqVia_eqRed_neg F h⟩

end DiagonaLean.KAComm.KleeneAlgebra
