/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.Reductions.Halt_to_TermEqBool
import DiagonaLean.Foundations.Computability.CodeSim
import DiagonaLean.Foundations.Computability.Computer

@[expose] public section

/-! # No Turing machine decides equality

These are the statements about real machines: under the natural encoding of a pair of expressions,
as the binary digits of its code, no `SingleTapeTM Bool` decides provable equality on `T Σ̈` or
`K Σ̈`, over `ℕ` or over the paper's alphabet `{0, 1}`.

A decider `D` would give a decider for "`M` halts on its own code", contradicting
`self_halt_undecidable`: from the code of `M`, a machine `R` computes the instance of the race
program, by `exists_computer`, and `D` decides that instance. `R` is obtained classically inside
the proof, and that is harmless, because it is an actual machine.
-/

open scoped Computability

namespace DiagonaLean.KAComm.Reduction

open DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing SingleTapeTM RExp TD Nat.Partrec DiagonaLean.Foundations.Computability
open DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Halt.Undecidable
  DiagonaLean.Halt.Compositions DiagonaLean.Synthetic.Definitions

/-- The value of a digit string. -/
def valG : List Turing.PartrecToTM2.Γ' → ℕ
  | [] => 0
  | d :: t => 2 * valG t + (if d = Turing.PartrecToTM2.Γ'.bit1 then 1 else 0)

/-- `valG` inverts `trNat`. -/
theorem valG_trNat (n : ℕ) : valG (Turing.PartrecToTM2.trNat n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0
      simp [valG, Turing.PartrecToTM2.trNat_zero]
    · rw [trNat_step h0, valG, ih (n / 2) (by omega)]
      by_cases h1 : n % 2 = 1
      · simp [bitG, h1]
        omega
      · simp [bitG, h1]
        omega

/-- `bitsOf` is injective. -/
theorem bitsOf_injective : Function.Injective bitsOf := fun a b h => by
  have := congrArg (fun l => valG (l.map bitG)) h
  simpa [bitsOf_map, valG_trNat] using this

/-- The binary digits of the pair of two numbers. -/
def bitsPair (a b : ℕ) : List Bool := bitsOf (Nat.pair a b)

/-- `bitsPair` is injective in both arguments. -/
theorem bitsPair_injective {a b c d : ℕ} (h : bitsPair a b = bitsPair c d) : a = c ∧ b = d :=
  Nat.pair_eq_pair.1 (bitsOf_injective h)

/-- **No machine decides a predicate with a suitable family of instances.** For each constant `K`,
`G K` is a primitive recursive family of codes, and `inst K l` an instance with those codes under
`enc`. If the predicate on instances holds exactly when the proof test passes on those codes, holds
when `NM K l` outputs `1`, and fails when it outputs `0`, then no machine decides it. -/
theorem not_machineDecidable_of_family {Y : Type*} {enc : Y → List Bool} {P : Y → Prop} {ka : Bool}
    (G : UConst → List Bool → ℕ × ℕ) (hG : ∀ K, Primrec (G K)) (inst : UConst → List Bool → Y)
    (henc : ∀ K l, enc (inst K l) = bitsPair (G K l).1 (G K l).2)
    (hQ : ∀ K l, P (inst K l) ↔ ∃ k, Checks ka k (G K l).1 (G K l).2)
    (pos : ∀ K l, (NM K l).Outputs [] [true] → P (inst K l))
    (neg : ∀ K l, (NM K l).Outputs [] [false] → ¬ P (inst K l)) :
    ¬ MachineDecidable enc P := by
  rintro ⟨D, hD⟩
  obtain ⟨B, hB⟩ := exists_base
  obtain ⟨C, hC⟩ := exists_raceOn ka B (hG B.K)
  -- the tape of the race program of a code
  let tape : List Bool → List Bool := fun w =>
    tapeOf B (Encodable.encode (C.curry (Encodable.encode (dataC w))))
  have htape : Primrec tape := (tapeOf_prim B).comp (Primrec.encode.comp
    (Code.primrec₂_curry.comp (Primrec.const C) (Primrec.encode.comp dataC_prim)))
  let F : List Bool → List Bool := fun w => bitsPair (G B.K (tape w)).1 (G B.K (tape w)).2
  have hF : Primrec F := by
    have h := (hG B.K).comp htape
    exact bitsOf_prim.comp (prim_natPair (prim_fst h) (prim_snd h))
  obtain ⟨R, hR⟩ := exists_computer F hF.to_comp
  have hiff : ∀ M : EncodableTM Bool, Halts M.toSingleTapeTM (encodeBoolTM M) ↔
      P (inst B.K (tape (encodeBoolTM M))) := fun M =>
    race_iff (Q := fun l => P (inst B.K l)) hB hC (hQ B.K) (pos B.K) (neg B.K)
      (dataC (encodeBoolTM M)) selfHalt_iff_test
  refine self_halt_undecidable ⟨compComputer R D, fun M => ⟨fun hM => ?_, fun hM => ?_⟩⟩
  · have h₁ := (hD (inst B.K (tape (encodeBoolTM M)))).1 ((hiff M).1 hM)
    rw [henc] at h₁
    exact compComputer_seq_outputs (hR _) h₁
  · have h₁ := (hD (inst B.K (tape (encodeBoolTM M)))).2 (fun h => hM ((hiff M).2 h))
    rw [henc] at h₁
    exact compComputer_seq_outputs (hR _) h₁

/-- A pair of expressions over `ℕ ⊕ ℕ`, as the binary digits of its code. -/
def encNat (i : Undec.Inst) : List Bool := bitsPair (rc i.1) (rc i.2)

/-- A pair of expressions over `Bool ⊕ Bool`, as the binary digits of its code. -/
def encBool (i : InstB) : List Bool := bitsPair (rc (toNat i.1)) (rc (toNat i.2))

/-- `encNat` is injective. -/
theorem encNat_injective : Function.Injective encNat := fun i j h => by
  obtain ⟨h₁, h₂⟩ := bitsPair_injective h
  exact Prod.ext (rc_injective h₁) (rc_injective h₂)

/-- `toNat` is injective. -/
theorem toNat_injective : Function.Injective toNat := fun e f h => by
  have := congrArg (RExp.map (dmap natBool)) h
  rwa [map_map', map_map', dmap_natBool_comp, map_id', map_id'] at this

/-- `encBool` is injective. -/
theorem encBool_injective : Function.Injective encBool := fun i j h => by
  obtain ⟨h₁, h₂⟩ := bitsPair_injective h
  exact Prod.ext (toNat_injective (rc_injective h₁)) (toNat_injective (rc_injective h₂))

section side

variable (K : UConst) (l : List Bool)

/-- `encNat (rInst K l)` is the binary digits of the pair `instCode K l`. -/
theorem enc_nat : encNat (rInst K l) = bitsPair (instCode K l).1 (instCode K l).2 := by
  have h := instCode_eq K l
  generalize instCode K l = x at h ⊢
  generalize rInst K l = i at h ⊢
  subst h
  rfl

/-- `rInst K l` is provable in pre-Kleene algebra iff the proof test passes on its codes. -/
theorem iff_nat : Equiv DComm (rInst K l).1 (rInst K l).2 ↔
    ∃ k, Checks false k (instCode K l).1 (instCode K l).2 := by
  have h := instCode_eq K l
  generalize instCode K l = x at h ⊢
  generalize rInst K l = i at h ⊢
  subst h
  exact equiv_iff_checks

/-- `rInst K l` is provable in Kleene algebra iff the proof test passes on its codes. -/
theorem iff_nat_ka : KAEquiv DComm (rInst K l).1 (rInst K l).2 ↔
    ∃ k, Checks true k (instCode K l).1 (instCode K l).2 := by
  have h := instCode_eq K l
  generalize instCode K l = x at h ⊢
  generalize rInst K l = i at h ⊢
  subst h
  exact kaEquiv_iff_checks

/-- `encBool` of the two-letter instance is the binary digits of the pair `instCodeB K l`. -/
theorem enc_bool : encBool (sbI (rInst K l)) = bitsPair (instCodeB K l).1 (instCodeB K l).2 := by
  have h := instCodeB_eq K l
  generalize instCodeB K l = x at h ⊢
  generalize rInst K l = i at h ⊢
  subst h
  rfl

/-- The two-letter instance is provable in pre-Kleene algebra iff the proof test passes on its
codes. -/
theorem iff_bool : Equiv DComm (sbI (rInst K l)).1 (sbI (rInst K l)).2 ↔
    ∃ k, Checks false k (instCodeB K l).1 (instCodeB K l).2 := by
  have h := instCodeB_eq K l
  generalize instCodeB K l = x at h ⊢
  generalize rInst K l = i at h ⊢
  subst h
  exact equiv_iff_map.symm.trans equiv_iff_checks

/-- The two-letter instance is provable in Kleene algebra iff the proof test passes on its codes. -/
theorem iff_bool_ka : KAEquiv DComm (sbI (rInst K l)).1 (sbI (rInst K l)).2 ↔
    ∃ k, Checks true k (instCodeB K l).1 (instCodeB K l).2 := by
  have h := instCodeB_eq K l
  generalize instCodeB K l = x at h ⊢
  generalize rInst K l = i at h ⊢
  subst h
  exact kaEquiv_iff_map.symm.trans kaEquiv_iff_checks

variable {K l}

/-- If `NM K l` outputs `true`, the two-letter instance is provable in pre-Kleene algebra. -/
theorem pos_bool (h : (NM K l).Outputs [] [true]) :
    Equiv DComm (sbI (rInst K l)).1 (sbI (rInst K l)).2 := by
  have hE := rInst_pos h
  generalize rInst K l = i at hE ⊢
  exact Equiv.sb wordOf hE

/-- If `NM K l` outputs `true`, the two-letter instance is provable in Kleene algebra. -/
theorem pos_bool_ka (h : (NM K l).Outputs [] [true]) :
    KAEquiv DComm (sbI (rInst K l)).1 (sbI (rInst K l)).2 :=
  .ofEquiv (pos_bool h)

/-- If `NM K l` outputs `false`, the two-letter instance is not provable in pre-Kleene algebra. -/
theorem neg_bool (h : (NM K l).Outputs [] [false]) :
    ¬ Equiv DComm (sbI (rInst K l)).1 (sbI (rInst K l)).2 := fun hE =>
  qb_neg (ka := false) h ((closed_rel false).ofEquiv (RExp.Equiv.map _ (dComm_dmap boolNat) hE))

/-- If `NM K l` outputs `false`, the two-letter instance is not provable in Kleene algebra. -/
theorem neg_bool_ka (h : (NM K l).Outputs [] [false]) :
    ¬ KAEquiv DComm (sbI (rInst K l)).1 (sbI (rInst K l)).2 := fun hE =>
  qb_neg (ka := true) h (rel_true.2 (KAEquiv.map' boolNat hE))

end side

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `{0, 1}`.** -/
theorem not_machineDecidable_termEq_bool :
    ¬ MachineDecidable encBool fun i : InstB => Equiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := false) instCodeB instCodeB_prim
    (fun K l => sbI (rInst K l)) enc_bool iff_bool (fun _ _ h => pos_bool h) (fun _ _ h => neg_bool h)

/-- **No Turing machine decides provable equality in Kleene algebra over `{0, 1}`.** -/
theorem not_machineDecidable_kaTermEq_bool :
    ¬ MachineDecidable encBool fun i : InstB => KAEquiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := true) instCodeB instCodeB_prim
    (fun K l => sbI (rInst K l)) enc_bool iff_bool_ka (fun _ _ h => pos_bool_ka h)
    (fun _ _ h => neg_bool_ka h)

/-- **No Turing machine decides provable equality in pre-Kleene algebra over `ℕ`.** -/
theorem not_machineDecidable_termEq_nat :
    ¬ MachineDecidable encNat fun i : Undec.Inst => Equiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := false) instCode instCode_prim rInst enc_nat iff_nat
    (fun _ _ h => rInst_pos h) (fun _ _ h => rInst_neg h)

/-- **No Turing machine decides provable equality in Kleene algebra over `ℕ`.** -/
theorem not_machineDecidable_kaTermEq_nat :
    ¬ MachineDecidable encNat fun i : Undec.Inst => KAEquiv DComm i.1 i.2 :=
  not_machineDecidable_of_family (ka := true) instCode instCode_prim rInst enc_nat iff_nat_ka
    (fun _ _ h => rInst_pos_ka h) (fun _ _ h => rInst_neg_ka h)

/-- The theorems transfer to any encoding that a machine can compute from the given one. -/
theorem not_machineDecidable_of_conv {Y : Type*} {enc enc' : Y → List Bool} {P : Y → Prop}
    (h : ¬ MachineDecidable enc P) {R : SingleTapeTM Bool}
    (hR : ComputesReduction R enc enc' id) : ¬ MachineDecidable enc' P := fun hd =>
  h (machineDecidable_of_computes_reduction hR (fun _ => Iff.rfl) hd)

end DiagonaLean.KAComm.Reduction
