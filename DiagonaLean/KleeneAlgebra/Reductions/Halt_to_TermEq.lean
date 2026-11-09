/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.Foundations.Computability.HaltSearch
import DiagonaLean.Foundations.Computability.Interpreter
import DiagonaLean.KleeneAlgebra.Reductions.InstanceCode
import DiagonaLean.KleeneAlgebra.Reductions.ProofSearch

@[expose] public section

/-! # `HALT` many-one reduces to equality on `T Σ̈` and `K Σ̈`

For a `HALT` instance `p`, the program `curry C ⟨p⟩` runs a race on `p`: it searches for a halting
run of `p`, and for a proof that the instance of its own machine holds. If the halting run comes
first it returns `1`, and otherwise `0`. Its machine writes its own code on the tape and then runs
a fixed interpreter.

The reduction `reduction B C p` is an untagged function of the data of `p`. Its only classical
ingredients are finite constants: the interpreter's table and tape symbols (`Base`), and the code
`C` from Mathlib's recursion theorem. So it follows the convention on `ManyOneReduces`.

## Main statements

* `reduction`: the reduction.
* `halt_reducesto_termEq_spec`, `halt_reducesto_kaTermEq_spec`: `reduction B C` is correct, given
  correct constants, in the explicit form `HALT ⪯ₘ[reduction B C] _`.
* `haltReduces_termEq`, `haltReduces_kaTermEq`: the same reductions, packaged as `HALT ⪯ₘ _`.
* `undecidable_termEq`, `undecidable_kaTermEq`: **provable equality in pre-Kleene algebra and in
  Kleene algebra with commutativity is `Undecidable`.**
-/

namespace DiagonaLean.KAComm.Reduction

open Cslib.Turing Enc RExp Turing Nat.Partrec DiagonaLean.Foundations.Computability
open DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation Undec

/-! ### The race -/

/-- The data of a `HALT` instance. -/
abbrev HD := List (ℕ × ℕ) × SC

/-- At `k`, a halting run or a proof of the equation `i` has been found. -/
def Hit (ka : Bool) (d : HD) (i : ℕ × ℕ) (k : ℕ) : Prop := Test d k ∨ Checks ka k i.1 i.2

instance (d : HD) (k : ℕ) : Decidable (Test d k) := inferInstanceAs (Decidable (_ = _))
instance (ka : Bool) (k a b : ℕ) : Decidable (Checks ka k a b) :=
  inferInstanceAs (Decidable (_ = _))
instance (ka : Bool) (d : HD) (i : ℕ × ℕ) (k : ℕ) : Decidable (Hit ka d i k) :=
  inferInstanceAs (Decidable (_ ∨ _))

attribute [local irreducible] Test Checks

/-- The race: `1` if the first hit is a halting run, and `0` otherwise. -/
def race (ka : Bool) (d : HD) (i : ℕ × ℕ) : Part ℕ :=
  (Nat.rfind fun k => Part.some (decide (Hit ka d i k))).map fun k => if Test d k then 1 else 0

theorem mem_race {ka : Bool} {d : HD} {i : ℕ × ℕ} (h : ∃ k, Hit ka d i k) :
    ∃ k, Hit ka d i k ∧ (if Test d k then 1 else 0) ∈ race ka d i := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, (Part.mem_map_iff _).2 ⟨_, ?_, rfl⟩⟩
  refine Nat.mem_rfind.2 ⟨?_, fun {m} hm => ?_⟩
  · simpa using Nat.find_spec h
  · simpa using Nat.find_min h hm

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

theorem exists_raceOn (ka : Bool) (B : Base) {G : List Bool → ℕ × ℕ} (hG : Primrec G) :
    ∃ C, RaceOn ka B G C :=
  Code.fixed_point₂ (raceOn_part ka B hG)

/-! ### The reduction -/

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
    rw [ite_cond_eq_true _ _ (eq_true hT)] at hm
    exact hS (pos l (by simpa using hout 1 hm))
  · intro hS
    by_contra hH
    obtain ⟨k₀, hk₀⟩ := hrel.1 hS
    obtain ⟨k, _, hm⟩ := mem_race (ka := ka) (d := d) (i := i) ⟨k₀, Or.inr hk₀⟩
    have hT : ¬ Test d k := fun h => hH (hd.2 ⟨k, h⟩)
    rw [ite_cond_eq_false _ _ (eq_false hT)] at hm
    exact neg l (by simpa using hout 0 hm) hS

/-- **Smullyan's argument, for any instance family.** -/
theorem halt_iff_of_family {ka : Bool} {B : Base} {G : List Bool → ℕ × ℕ} {C : Code} (hB : B.Good)
    (hC : RaceOn ka B G C) {Q : List Bool → Prop}
    (hQ : ∀ l, Q l ↔ ∃ k, Checks ka k (G l).1 (G l).2)
    (pos : ∀ l, (NM B.K l).Outputs [] [true] → Q l)
    (neg : ∀ l, (NM B.K l).Outputs [] [false] → ¬ Q l)
    (p : EncodableTM Bool × List Bool) :
    HALT p ↔ Q (tapeOf B (Encodable.encode (progOf C p))) :=
  race_iff hB hC hQ pos neg (dataOf p) (halt_iff_test p)

/-- **The reduction.** The instance of the machine that writes the race program of `p` on its
tape and runs the interpreter. -/
def reduction (B : Base) (C : Code) (p : EncodableTM Bool × List Bool) : Inst :=
  rInst B.K (tapeOf B (Encodable.encode (progOf C p)))

/-- `C` is the race program for the instances of `reduction`. -/
def RaceProg (ka : Bool) (B : Base) (C : Code) : Prop := RaceOn ka B (instCode B.K) C

theorem exists_raceProg (ka : Bool) (B : Base) : ∃ C, RaceProg ka B C :=
  exists_raceOn ka B (instCode_prim B.K)

theorem rel_iff_checks {ka : Bool} {e f : RExp (ℕ ⊕ ℕ)} :
    Rel ka e f ↔ ∃ k, Checks ka k (rc e) (rc f) := by
  cases ka
  · simpa [Rel] using equiv_iff_checks
  · simpa [Rel] using kaEquiv_iff_checks

theorem rel_pos {ka : Bool} {K : UConst} {l : List Bool} (h : (NM K l).Outputs [] [true]) :
    Rel ka (rInst K l).1 (rInst K l).2 :=
  (closed_rel ka).ofEquiv (rInst_pos h)

theorem rel_neg {ka : Bool} {K : UConst} {l : List Bool} (h : (NM K l).Outputs [] [false]) :
    ¬ Rel ka (rInst K l).1 (rInst K l).2 := by
  cases ka
  · simpa [Rel] using rInst_neg h
  · simpa [Rel] using rInst_neg_ka h

/-- **Smullyan's argument, for the race program.** -/
theorem halt_iff_rel {ka : Bool} {B : Base} {C : Code} (hB : B.Good) (hC : RaceProg ka B C)
    (p : EncodableTM Bool × List Bool) :
    HALT p ↔ Rel ka (reduction B C p).1 (reduction B C p).2 :=
  halt_iff_of_family (Q := fun l => Rel ka (rInst B.K l).1 (rInst B.K l).2) hB hC
    (fun l => by
      rw [rel_iff_checks]
      have hi := instCode_eq B.K l
      rw [← hi])
    (fun _ h => rel_pos h) (fun _ h => rel_neg h) p

/-- `reduction B C` reduces `HALT` to provable equality in pre-Kleene algebra with commutativity. -/
theorem halt_reducesto_termEq_spec {B : Base} {C : Code} (hB : B.Good) (hC : RaceProg false B C) :
    HALT ⪯ₘ[reduction B C] fun i : Inst => Equiv DComm i.1 i.2 :=
  fun p => by simpa [Rel] using halt_iff_rel hB hC p

/-- `HALT` many-one reduces to provable equality in pre-Kleene algebra with commutativity. -/
def haltReduces_termEq (B : Base) (C : Code) (hB : B.Good) (hC : RaceProg false B C) :
    HALT ⪯ₘ fun i : Inst => Equiv DComm i.1 i.2 :=
  ⟨reduction B C, halt_reducesto_termEq_spec hB hC⟩

/-- `reduction B C` reduces `HALT` to provable equality in Kleene algebra with commutativity. -/
theorem halt_reducesto_kaTermEq_spec {B : Base} {C : Code} (hB : B.Good) (hC : RaceProg true B C) :
    HALT ⪯ₘ[reduction B C] fun i : Inst => KAEquiv DComm i.1 i.2 :=
  fun p => by simpa [Rel] using halt_iff_rel hB hC p

/-- `HALT` many-one reduces to provable equality in Kleene algebra with commutativity. -/
def haltReduces_kaTermEq (B : Base) (C : Code) (hB : B.Good) (hC : RaceProg true B C) :
    HALT ⪯ₘ fun i : Inst => KAEquiv DComm i.1 i.2 :=
  ⟨reduction B C, halt_reducesto_kaTermEq_spec hB hC⟩

/-- **Provable equality in pre-Kleene algebra with commutativity is `Undecidable`.** -/
theorem undecidable_termEq : Undecidable fun i : Inst => Equiv DComm i.1 i.2 := by
  obtain ⟨B, hB⟩ := exists_base
  obtain ⟨C, hC⟩ := exists_raceProg false B
  exact ⟨haltReduces_termEq B C hB hC⟩

/-- **Provable equality in Kleene algebra with commutativity is `Undecidable`.** -/
theorem undecidable_kaTermEq : Undecidable fun i : Inst => KAEquiv DComm i.1 i.2 := by
  obtain ⟨B, hB⟩ := exists_base
  obtain ⟨C, hC⟩ := exists_raceProg true B
  exact ⟨haltReduces_kaTermEq B C hB hC⟩

end DiagonaLean.KAComm.Reduction
