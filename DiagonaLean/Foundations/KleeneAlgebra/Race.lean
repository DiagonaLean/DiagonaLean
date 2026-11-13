/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.HaltSearch
import DiagonaLean.Foundations.Computability.Interpreter
import DiagonaLean.Foundations.Computability.CodeSim
import DiagonaLean.Foundations.Computability.Computer
import DiagonaLean.Foundations.KleeneAlgebra.InstanceCode
import DiagonaLean.Foundations.KleeneAlgebra.ProofSearch
import DiagonaLean.Foundations.KleeneAlgebra.BinarySubst

@[expose] public section

/-! # The race program

For a `HaltProblem` instance `p`, the program `curry C ⟨p⟩` runs a race on `p`: it searches for a
halting run of `p`, and for a proof that the instance of its own machine holds. If the halting run
comes first it returns `1`, and otherwise `0`. Its machine writes its own code on the tape and then
runs a fixed interpreter. The flag `ka` selects the proof test for pre-Kleene algebra (`false`) or
Kleene algebra (`true`).

`reduction B C p` is the instance of that machine over `ℕ`, and `reductionB B C p` its substitution
over `{0, 1}`. Both are untagged functions of the data of `p`. Their only classical ingredients are
finite constants: the interpreter's table and tape symbols (`Base`), and the code `C` from
Mathlib's recursion theorem. So they follow the convention on `ManyOneReduces`. Smullyan's argument
gives `HaltProblem p ↔` the instance holds (`halt_iff_rel`, `halt_iff_qb`).

`not_machineDecidable_of_family` is the same argument for real machines: a decider for the instance
would decide "`M` halts on its own code", since a machine computes the instance of the race program
from the code of `M` (`exists_computer`). The instances are encoded as the binary digits of their
codes (`encNat`, `encBool`).

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 19
* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

open scoped Computability

namespace DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing SingleTapeTM Enc RExp FreePreKA TD Turing Nat.Partrec
  DiagonaLean.Foundations.Computability DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Undecidable DiagonaLean.Halt.Compositions DiagonaLean.Synthetic.Definitions

/-- The data of a `HaltProblem` instance. -/
abbrev HD := List (ℕ × ℕ) × SC

/-- At `k`, a halting run or a proof of the equation `i` has been found. -/
def Hit (ka : Bool) (d : HD) (i : ℕ × ℕ) (k : ℕ) : Prop := Test d k ∨ Checks ka k i.1 i.2

/-- `Test d k` is decidable. -/
instance (d : HD) (k : ℕ) : Decidable (Test d k) := inferInstanceAs (Decidable (_ = _))
/-- `Checks ka k a b` is decidable. -/
instance (ka : Bool) (k a b : ℕ) : Decidable (Checks ka k a b) :=
  inferInstanceAs (Decidable (_ = _))
/-- `Hit ka d i k` is decidable. -/
instance (ka : Bool) (d : HD) (i : ℕ × ℕ) (k : ℕ) : Decidable (Hit ka d i k) :=
  inferInstanceAs (Decidable (_ ∨ _))

attribute [local irreducible] Test Checks

/-- The race: `1` if the first hit is a halting run, and `0` otherwise. -/
def race (ka : Bool) (d : HD) (i : ℕ × ℕ) : Part ℕ :=
  (Nat.rfind fun k => Part.some (decide (Hit ka d i k))).map fun k => if Test d k then 1 else 0

/-- If some `k` is a hit, then the race returns the outcome of some hit `k`. -/
theorem mem_race {ka : Bool} {d : HD} {i : ℕ × ℕ} (h : ∃ k, Hit ka d i k) :
    ∃ k, Hit ka d i k ∧ (if Test d k then 1 else 0) ∈ race ka d i := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, (Part.mem_map_iff _).2 ⟨_, ?_, rfl⟩⟩
  refine Nat.mem_rfind.2 ⟨?_, fun {m} hm => ?_⟩
  · simpa using Nat.find_spec h
  · simpa using Nat.find_min h hm

/-- `Hit` is a primitive recursive predicate. -/
theorem hit_prim (ka : Bool) :
    PrimrecPred fun x : (HD × (ℕ × ℕ)) × ℕ => Hit ka x.1.1 x.1.2 x.2 := by
  have h₁ : PrimrecPred fun x : (HD × (ℕ × ℕ)) × ℕ => Test x.1.1 x.2 :=
    test_prim.comp (f := fun x : (HD × (ℕ × ℕ)) × ℕ => (x.1.1, x.2))
      (prim_pair (prim_fst Primrec.fst) Primrec.snd)
  have h₂ : PrimrecPred fun x : (HD × (ℕ × ℕ)) × ℕ => Checks ka x.2 x.1.2.1 x.1.2.2 :=
    (checks_prim ka).comp (f := fun x : (HD × (ℕ × ℕ)) × ℕ => (x.2, x.1.2.1, x.1.2.2))
      (prim_pair Primrec.snd (prim_pair (prim_fst (prim_snd Primrec.fst))
        (prim_snd (prim_snd Primrec.fst))))
  exact h₁.or h₂

/-- `race` is partial recursive. -/
theorem race_part (ka : Bool) : Partrec fun x : HD × (ℕ × ℕ) => race ka x.1 x.2 := by
  unfold race
  refine Partrec.map (Partrec.rfind ?_) ?_
  · have h : Primrec fun y : (HD × (ℕ × ℕ)) × ℕ => decide (Hit ka y.1.1 y.1.2 y.2) :=
      (hit_prim ka).decide
    exact (h.to_comp.partrec).of_eq fun y => rfl
  · have h : PrimrecPred fun y : (HD × (ℕ × ℕ)) × ℕ => Test y.1.1 y.2 :=
      test_prim.comp (f := fun x : (HD × (ℕ × ℕ)) × ℕ => (x.1.1, x.2))
        (prim_pair (prim_fst Primrec.fst) Primrec.snd)
    exact (Primrec.ite h (Primrec.const 1) (Primrec.const 0)).to_comp

attribute [local irreducible] race

/-- The function whose fixed point is the race program, for an instance family `G`: the race on
the data in `n`, against the instance of the machine for the program `c.curry ⟨data⟩`. -/
def raceOn (ka : Bool) (B : Base) (G : List Bool → ℕ × ℕ) (c : Code) (n : ℕ) : Part ℕ :=
  race ka (Denumerable.ofNat HD n.unpair.1)
    (G (tapeOf B (Encodable.encode (c.curry n.unpair.1))))

/-- `raceOn ka B G` is partial recursive when `G` is primitive recursive. -/
theorem raceOn_part (ka : Bool) (B : Base) {G : List Bool → ℕ × ℕ} (hG : Primrec G) :
    Partrec₂ (raceOn ka B G) := by
  have hd : Primrec fun x : Code × ℕ => Denumerable.ofNat HD x.2.unpair.1 :=
    (Primrec.ofNat HD).comp (prim_fst (prim_unpair Primrec.snd))
  have hi : Primrec fun x : Code × ℕ =>
      G (tapeOf B (Encodable.encode (x.1.curry x.2.unpair.1))) :=
    hG.comp ((tapeOf_prim B).comp (Primrec.encode.comp
      (Code.primrec₂_curry.comp Primrec.fst (prim_fst (prim_unpair Primrec.snd)))))
  exact (race_part ka).comp (g := fun x : Code × ℕ =>
    (Denumerable.ofNat HD x.2.unpair.1,
      G (tapeOf B (Encodable.encode (x.1.curry x.2.unpair.1))))) (hd.pair hi).to_comp

/-- `C` is the race program for the instance family `G`. -/
def RaceOn (ka : Bool) (B : Base) (G : List Bool → ℕ × ℕ) (C : Code) : Prop :=
  C.eval = raceOn ka B G C

/-- A race program exists for every primitive recursive instance family. -/
theorem exists_raceOn (ka : Bool) (B : Base) {G : List Bool → ℕ × ℕ} (hG : Primrec G) :
    ∃ C, RaceOn ka B G C :=
  Code.fixed_point₂ (raceOn_part ka B hG)

/-- The code of the race program of `p`. -/
def progOf (C : Code) (p : EncodableTM Bool × List Bool) : Code :=
  C.curry (Encodable.encode (dataOf p))

/-- **Smullyan's argument, for any instance family and any search.** Suppose `Q` holds of a tape
exactly when some program passes the proof test on `G`, that output `1` makes `Q` hold, and that
output `0` makes it fail. If `Hd` is the proposition that the search on the data `d` succeeds, then
`Hd` holds iff `Q` holds of the tape of the race program of `d`. -/
theorem race_iff {ka : Bool} {B : Base} {G : List Bool → ℕ × ℕ} {C : Code} (hB : B.Good)
    (hC : RaceOn ka B G C) {Q : List Bool → Prop}
    (hQ : ∀ l, Q l ↔ ∃ k, Checks ka k (G l).1 (G l).2)
    (pos : ∀ l, (NM B.K l).Outputs [] [true] → Q l)
    (neg : ∀ l, (NM B.K l).Outputs [] [false] → ¬ Q l)
    (d : HD) {Hd : Prop} (hd : Hd ↔ ∃ k, Test d k) :
    Hd ↔ Q (tapeOf B (Encodable.encode (C.curry (Encodable.encode d)))) := by
  have heval : (C.curry (Encodable.encode d)).eval 0 =
      race ka d (G (tapeOf B (Encodable.encode (C.curry (Encodable.encode d))))) := by
    rw [Code.eval_curry, hC, raceOn, Nat.unpair_pair, Denumerable.ofNat_encode]
  have hout₀ := hB (C.curry (Encodable.encode d))
  rw [heval] at hout₀
  generalize tapeOf B (Encodable.encode (C.curry (Encodable.encode d))) = l at hout₀ ⊢
  have hout : ∀ m, m ∈ race ka d (G l) → (NM B.K l).Outputs [] [decide (m ≠ 0)] := hout₀
  have hrel := hQ l
  generalize G l = i at hout hrel
  constructor
  · intro hH
    by_contra hS
    obtain ⟨k₀, hk₀⟩ := hd.1 hH
    obtain ⟨k, hk, hm⟩ := mem_race (ka := ka) (d := d) (i := i) ⟨k₀, Or.inl hk₀⟩
    have hT : Test d k := hk.resolve_right fun hch => hS (hrel.2 ⟨k, hch⟩)
    rw [ite_eq_left_of_eq_true _ _ (eq_true hT)] at hm
    exact hS (pos l (by simpa using hout 1 hm))
  · intro hS
    by_contra hH
    obtain ⟨k₀, hk₀⟩ := hrel.1 hS
    obtain ⟨k, _, hm⟩ := mem_race (ka := ka) (d := d) (i := i) ⟨k₀, Or.inr hk₀⟩
    have hT : ¬ Test d k := fun h => hH (hd.2 ⟨k, h⟩)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hT)] at hm
    exact neg l (by simpa using hout 0 hm) hS

/-- **Smullyan's argument, for any instance family.** -/
theorem halt_iff_of_family {ka : Bool} {B : Base} {G : List Bool → ℕ × ℕ} {C : Code} (hB : B.Good)
    (hC : RaceOn ka B G C) {Q : List Bool → Prop}
    (hQ : ∀ l, Q l ↔ ∃ k, Checks ka k (G l).1 (G l).2)
    (pos : ∀ l, (NM B.K l).Outputs [] [true] → Q l)
    (neg : ∀ l, (NM B.K l).Outputs [] [false] → ¬ Q l)
    (p : EncodableTM Bool × List Bool) :
    HaltProblem p ↔ Q (tapeOf B (Encodable.encode (progOf C p))) :=
  race_iff hB hC hQ pos neg (dataOf p) (halt_iff_test p)

/-- **The reduction.** The instance of the machine that writes the race program of `p` on its
tape and runs the interpreter. -/
def reduction (B : Base) (C : Code) (p : EncodableTM Bool × List Bool) : Inst :=
  rInst B.K (tapeOf B (Encodable.encode (progOf C p)))

/-- `C` is the race program for the instances of `reduction`. -/
def RaceProg (ka : Bool) (B : Base) (C : Code) : Prop := RaceOn ka B (instCode B.K) C

/-- A race program for the instances of `reduction` exists. -/
theorem exists_raceProg (ka : Bool) (B : Base) : ∃ C, RaceProg ka B C :=
  exists_raceOn ka B (instCode_prim B.K)

/-- `Rel ka e f` holds iff some `k` passes the proof test on the codes of `e` and `f`. -/
theorem rel_iff_checks {ka : Bool} {e f : RExp (ℕ ⊕ ℕ)} :
    Rel ka e f ↔ ∃ k, Checks ka k (rc e) (rc f) := by
  cases ka
  · simpa [Rel] using equiv_iff_checks
  · simpa [Rel] using kaEquiv_iff_checks

/-- If the interpreter outputs `true` on `l`, the two sides of `rInst K l` are related. -/
theorem rel_pos {ka : Bool} {K : UConst} {l : List Bool} (h : (NM K l).Outputs [] [true]) :
    Rel ka (rInst K l).1 (rInst K l).2 :=
  (closed_rel ka).ofEquiv (rInst_pos h)

/-- If the interpreter outputs `false` on `l`, the two sides of `rInst K l` are not related. -/
theorem rel_neg {ka : Bool} {K : UConst} {l : List Bool} (h : (NM K l).Outputs [] [false]) :
    ¬ Rel ka (rInst K l).1 (rInst K l).2 := by
  cases ka
  · simpa [Rel] using rInst_neg h
  · simpa [Rel] using rInst_neg_ka h

/-- **Smullyan's argument, for the race program.** -/
theorem halt_iff_rel {ka : Bool} {B : Base} {C : Code} (hB : B.Good) (hC : RaceProg ka B C)
    (p : EncodableTM Bool × List Bool) :
    HaltProblem p ↔ Rel ka (reduction B C p).1 (reduction B C p).2 :=
  halt_iff_of_family (Q := fun l => Rel ka (rInst B.K l).1 (rInst B.K l).2) hB hC
    (fun l => by
      rw [rel_iff_checks]
      have hi := instCode_eq B.K l
      rw [← hi])
    (fun _ h => rel_pos h) (fun _ h => rel_neg h) p

/-- The two-letter version of an instance. -/
def sbI (i : Inst) : InstB := (sbB i.1, sbB i.2)

/-- The codes of the two-letter instance of `NM K l`, over the letters `0` and `1` of `ℕ`. -/
def instCodeB (K : UConst) (l : List Bool) : ℕ × ℕ :=
  (subC (instCode K l).1, subC (instCode K l).2)

/-- `instCodeB K` is primitive recursive. -/
theorem instCodeB_prim (K : UConst) : Primrec (instCodeB K) :=
  prim_pair (subC_prim.comp (prim_fst (instCode_prim K)))
    (subC_prim.comp (prim_snd (instCode_prim K)))

/-- `instCodeB K l` is the pair of codes of the two-letter instance of `rInst K l`. -/
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

/-- If the interpreter outputs `true` on `l`, then `QB ka K l` holds. -/
theorem qb_pos {ka : Bool} {K : UConst} {l : List Bool} (h : (NM K l).Outputs [] [true]) :
    QB ka K l :=
  (closed_rel ka).ofEquiv (RExp.Equiv.map _ (dComm_dmap boolNat) (Equiv.sb wordOf (rInst_pos h)))

/-- If `x + y` and `y` are related by `Rel ka`, then `ModelLe (x, y)` holds. -/
theorem modelLe_of_rel {ka : Bool} {x y : RExp (ℕ ⊕ ℕ)} (h : Rel ka (plus x y) y) :
    ModelLe (x, y) := by
  cases ka
  · have h' : Equiv DComm (plus x y) y := by simpa [Rel] using h
    exact ((provable_iff_equiv (x, y)).2 h').modelLe
  · have h' : KAEquiv DComm (plus x y) y := by simpa [Rel] using h
    exact KAProvable.modelLe (i := (x, y)) h'

/-- If the interpreter outputs `false` on `l`, then `QB ka K l` fails. -/
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

/-- A race program for the instances of `reductionB` exists. -/
theorem exists_raceProgB (ka : Bool) (B : Base) : ∃ C, RaceProgB ka B C :=
  exists_raceOn ka B (instCodeB_prim B.K)

/-- `p` halts iff `QB` holds of the tape of the race program of `p`. -/
theorem halt_iff_qb {ka : Bool} {B : Base} {C : Code} (hB : B.Good) (hC : RaceProgB ka B C)
    (p : EncodableTM Bool × List Bool) :
    HaltProblem p ↔ QB ka B.K (tapeOf B (Encodable.encode (progOf C p))) :=
  halt_iff_of_family (Q := QB ka B.K) hB hC
    (fun l => by
      rw [QB, rel_iff_checks, instCodeB_eq])
    (fun _ h => qb_pos h) (fun _ h => qb_neg h) p

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
def encNat (i : Inst) : List Bool := bitsPair (rc i.1) (rc i.2)

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

end DiagonaLean.Foundations.KleeneAlgebra
