/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Reductions.BinarySubst
import DiagonaLean.KleeneAlgebra.Reductions.Halt_to_TermEq

@[expose] public section

/-! # `HaltProblem ⪯ₘ` equality over the two-letter alphabet

The theorems of `Halt_to_TermEq.lean` over `Bool ⊕ Bool`, the paper's `Σ = {0, 1}`.

## Main statements

* `reductionB`: the reduction, as an untagged function of the data of `p`.
* `undecidable_termEq_bool`, `undecidable_kaTermEq_bool`: equality on `T Σ̈` and `K Σ̈`.
* `undecidable_not_langEq_bool`: the failure of equality on `L Σ̈`.
-/

open scoped Computability

namespace DiagonaLean.KAComm.Reduction

open Cslib.Turing Enc RExp FreePreKA TD Nat.Partrec DiagonaLean.Foundations.Computability
open DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation Undec

/-- The two-letter version of an instance. -/
def sbI (i : Inst) : InstB := (sbB i.1, sbB i.2)

/-- The codes of the two-letter instance of `NM K l`, over the letters `0` and `1` of `ℕ`. -/
def instCodeB (K : UConst) (l : List Bool) : ℕ × ℕ :=
  (subC (instCode K l).1, subC (instCode K l).2)

theorem instCodeB_prim (K : UConst) : Primrec (instCodeB K) :=
  prim_pair (subC_prim.comp (prim_fst (instCode_prim K)))
    (subC_prim.comp (prim_snd (instCode_prim K)))

theorem instCodeB_eq (K : UConst) (l : List Bool) :
    instCodeB K l = (rc (toNat (sbI (rInst K l)).1), rc (toNat (sbI (rInst K l)).2)) := by
  have h := instCode_eq K l
  unfold instCodeB
  generalize instCode K l = x at h ⊢
  generalize rInst K l = i at h ⊢
  subst h
  exact Prod.ext (subC_rc i.1) (subC_rc i.2)

/-- `rInst` after substitution holds, in the relation of the flag and over the letters `0`, `1`. -/
def QB (ka : Bool) (K : UConst) (l : List Bool) : Prop :=
  Rel ka (toNat (sbI (rInst K l)).1) (toNat (sbI (rInst K l)).2)

theorem qb_pos {ka : Bool} {K : UConst} {l : List Bool} (h : (NM K l).Outputs [] [true]) :
    QB ka K l :=
  (closed_rel ka).ofEquiv (RExp.Equiv.map _ (dComm_dmap boolNat) (Equiv.sb wordOf (rInst_pos h)))

theorem modelLe_of_rel {ka : Bool} {x y : RExp (ℕ ⊕ ℕ)} (h : Rel ka (plus x y) y) :
    ModelLe (x, y) := by
  cases ka
  · have h' : Equiv DComm (plus x y) y := by simpa [Rel] using h
    exact ((provable_iff_equiv (x, y)).2 h').modelLe
  · have h' : KAEquiv DComm (plus x y) y := by simpa [Rel] using h
    exact KAProvable.modelLe (i := (x, y)) h'

theorem qb_neg {ka : Bool} {K : UConst} {l : List Bool} (h : (NM K l).Outputs [] [false]) :
    ¬ QB ka K l := fun hq => by
  have h₁ : ModelLe (toNat (sbB (redA K l)), toNat (sbB (redB K l))) := modelLe_of_rel hq
  have h₂ := pl_le_of_map (g := boolNat) (fun a b hab => by
    cases a <;> cases b <;> simp_all [boolNat]) h₁
  exact not_modelLe h (pl_le_of_sb cd_injective h₂)

/-- **The reduction over `{0, 1}`.** -/
def reductionB (B : Base) (C : Code) (p : EncodableTM Bool × List Bool) : InstB :=
  sbI (rInst B.K (tapeOf B (Encodable.encode (progOf C p))))

/-- `C` is the race program for the instances of `reductionB`. -/
def RaceProgB (ka : Bool) (B : Base) (C : Code) : Prop := RaceOn ka B (instCodeB B.K) C

theorem exists_raceProgB (ka : Bool) (B : Base) : ∃ C, RaceProgB ka B C :=
  exists_raceOn ka B (instCodeB_prim B.K)

theorem halt_iff_qb {ka : Bool} {B : Base} {C : Code} (hB : B.Good) (hC : RaceProgB ka B C)
    (p : EncodableTM Bool × List Bool) :
    HaltProblem p ↔ QB ka B.K (tapeOf B (Encodable.encode (progOf C p))) :=
  halt_iff_of_family (Q := QB ka B.K) hB hC
    (fun l => by
      rw [QB, rel_iff_checks, instCodeB_eq])
    (fun _ h => qb_pos h) (fun _ h => qb_neg h) p

/-- `reductionB B C` reduces `HaltProblem` to provable equality in pre-Kleene algebra over
`{0, 1}`. -/
theorem halt_reducesto_termEq_bool_spec {B : Base} {C : Code} (hB : B.Good)
    (hC : RaceProgB false B C) :
    HaltProblem ⪯ₘ[reductionB B C] TermEqProblem := fun p =>
  (halt_iff_qb hB hC p).trans (by
    simpa [QB, Rel, reductionB, TermEq.DecisionProblem] using equiv_iff_map)

/-- `reductionB B C` reduces `HaltProblem` to provable equality in Kleene algebra over `{0, 1}`. -/
theorem halt_reducesto_kaTermEq_bool_spec {B : Base} {C : Code} (hB : B.Good)
    (hC : RaceProgB true B C) :
    HaltProblem ⪯ₘ[reductionB B C] KATermEqProblem := fun p =>
  (halt_iff_qb hB hC p).trans (by
    simpa [QB, Rel, reductionB, KATermEq.DecisionProblem] using kaEquiv_iff_map)

/-- `HaltProblem` many-one reduces to provable equality in pre-Kleene algebra over `{0, 1}`. -/
def haltReduces_termEq_bool (B : Base) (C : Code) (hB : B.Good) (hC : RaceProgB false B C) :
    HaltProblem ⪯ₘ TermEqProblem :=
  ⟨reductionB B C, halt_reducesto_termEq_bool_spec hB hC⟩

/-- `HaltProblem` many-one reduces to provable equality in Kleene algebra over `{0, 1}`. -/
def haltReduces_kaTermEq_bool (B : Base) (C : Code) (hB : B.Good) (hC : RaceProgB true B C) :
    HaltProblem ⪯ₘ KATermEqProblem :=
  ⟨reductionB B C, halt_reducesto_kaTermEq_bool_spec hB hC⟩

/-- **Provable equality in pre-Kleene algebra with commutativity over `{0, 1}` is `Undecidable`.** -/
theorem undecidable_termEq_bool : Undecidable TermEqProblem := by
  obtain ⟨B, hB⟩ := exists_base
  obtain ⟨C, hC⟩ := exists_raceProgB false B
  exact ⟨haltReduces_termEq_bool B C hB hC⟩

/-- **Provable equality in Kleene algebra with commutativity over `{0, 1}` is `Undecidable`.** -/
theorem undecidable_kaTermEq_bool : Undecidable KATermEqProblem := by
  obtain ⟨B, hB⟩ := exists_base
  obtain ⟨C, hC⟩ := exists_raceProgB true B
  exact ⟨haltReduces_kaTermEq_bool B C hB hC⟩

/-- The reduction to language inequality over `{0, 1}`. -/
def haltEqRedB (p : EncodableTM Bool × List Bool) : InstB := sbI (haltEqRed p)

/-- `haltEqRedB` reduces `HaltProblem` to the failure of language equality over `{0, 1}`. -/
theorem halt_reducesto_not_langEq_bool :
    HaltProblem ⪯ₘ[haltEqRedB] Complement LangEqProblem :=
  fun p => (halt_iff_not_modelLe p).trans (not_congr
    ((modelLe_iff_langEq _).trans (pl_sb_eq_iff cd_injective).symm))

/-- `HaltProblem` many-one reduces to the failure of language equality over `{0, 1}`. -/
def haltReduces_not_langEq_bool :
    HaltProblem ⪯ₘ Complement LangEqProblem :=
  ⟨haltEqRedB, halt_reducesto_not_langEq_bool⟩

/-- **The failure of language equality over `{0, 1}` is `Undecidable`.** -/
theorem undecidable_not_langEq_bool :
    Undecidable (Complement LangEqProblem) :=
  ⟨haltReduces_not_langEq_bool⟩

end DiagonaLean.KAComm.Reduction
