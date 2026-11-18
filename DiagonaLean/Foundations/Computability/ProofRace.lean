/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.Computability.CodeSim
import DiagonaLean.Foundations.Computability.Computer

@[expose] public section

/-! # A race between a halting search and a proof search

`chk k i` is a primitive recursive test that `k` codes a proof of the instance with codes `i`.
`race chk d i` searches for a halting run of the machine with data `d` and for a proof of `i`,
and returns `1` if the halting run comes first and `0` otherwise.

For an instance family `G`, the race program `C` (`RaceOn chk G C`, from Mathlib's recursion
theorem) runs the race on input `d` against its own instance `G C d`. Smullyan's argument
(`halt_iff`) gives `HaltProblem p ↔ Q d`, for `d` the code of the data of `p`, whenever `Q d`
holds iff some proof of `G C d` passes the test, output `1` makes `Q` hold, and output `0` makes
it fail. Run on the code of a machine, the same argument gives that no machine decides such a
predicate (`not_machineDecidable_of_race`). The race is shared by
`Foundations/CombinatoryLogic/Race.lean` and `Foundations/LambdaCalculus/Race.lean`; the race in
`Foundations/KleeneAlgebra/Race.lean` runs against the instance of a machine instead of a
program.

## References

* R. M. Smullyan, *Undecidability and recursive inseparability* (1958)
-/

namespace DiagonaLean.Foundations.Computability.ProofRace

open Cslib.Turing SingleTapeTM Nat.Partrec DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Undecidable DiagonaLean.Halt.Compositions DiagonaLean.Synthetic.Definitions

/-- The data of a `HaltProblem` instance. -/
abbrev HD := List (ℕ × ℕ) × SC

/-- At `k`, a halting run or a proof of the instance `i` has been found. -/
def Hit (chk : ℕ → ℕ × ℕ → Bool) (d : HD) (i : ℕ × ℕ) (k : ℕ) : Prop :=
  Test d k ∨ chk k i = true

/-- `Test d k` is decidable. -/
instance (d : HD) (k : ℕ) : Decidable (Test d k) := inferInstanceAs (Decidable (_ = _))
/-- `Hit chk d i k` is decidable. -/
instance (chk : ℕ → ℕ × ℕ → Bool) (d : HD) (i : ℕ × ℕ) (k : ℕ) : Decidable (Hit chk d i k) :=
  inferInstanceAs (Decidable (_ ∨ _))

attribute [local irreducible] Test

/-- The race: `1` if the first hit is a halting run, and `0` otherwise. -/
def race (chk : ℕ → ℕ × ℕ → Bool) (d : HD) (i : ℕ × ℕ) : Part ℕ :=
  (Nat.rfind fun k => Part.some (decide (Hit chk d i k))).map fun k => if Test d k then 1 else 0

/-- If some `k` is a hit, then the race returns the outcome of some hit `k`. -/
theorem mem_race {chk : ℕ → ℕ × ℕ → Bool} {d : HD} {i : ℕ × ℕ} (h : ∃ k, Hit chk d i k) :
    ∃ k, Hit chk d i k ∧ (if Test d k then 1 else 0) ∈ race chk d i := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, (Part.mem_map_iff _).2 ⟨_, ?_, rfl⟩⟩
  refine Nat.mem_rfind.2 ⟨?_, fun {m} hm => ?_⟩
  · simpa using Nat.find_spec h
  · simpa using Nat.find_min h hm

/-- `Hit chk` is a primitive recursive predicate when `chk` is primitive recursive. -/
theorem hit_prim {chk : ℕ → ℕ × ℕ → Bool} (hchk : Primrec₂ chk) :
    PrimrecPred fun x : (HD × (ℕ × ℕ)) × ℕ => Hit chk x.1.1 x.1.2 x.2 := by
  have h₁ : PrimrecPred fun x : (HD × (ℕ × ℕ)) × ℕ => Test x.1.1 x.2 :=
    test_prim.comp (f := fun x : (HD × (ℕ × ℕ)) × ℕ => (x.1.1, x.2))
      (prim_pair (prim_fst Primrec.fst) Primrec.snd)
  have h₂ : PrimrecPred fun x : (HD × (ℕ × ℕ)) × ℕ => chk x.2 x.1.2 = true :=
    Primrec.eq.comp (hchk.comp Primrec.snd (prim_snd Primrec.fst)) (Primrec.const true)
  exact h₁.or h₂

/-- `race chk` is partial recursive when `chk` is primitive recursive. -/
theorem race_part {chk : ℕ → ℕ × ℕ → Bool} (hchk : Primrec₂ chk) :
    Partrec fun x : HD × (ℕ × ℕ) => race chk x.1 x.2 := by
  unfold race
  refine Partrec.map (Partrec.rfind ?_) ?_
  · have h : Primrec fun y : (HD × (ℕ × ℕ)) × ℕ => decide (Hit chk y.1.1 y.1.2 y.2) :=
      (hit_prim hchk).decide
    exact (h.to_comp.partrec).of_eq fun y => rfl
  · have h : PrimrecPred fun y : (HD × (ℕ × ℕ)) × ℕ => Test y.1.1 y.2 :=
      test_prim.comp (f := fun x : (HD × (ℕ × ℕ)) × ℕ => (x.1.1, x.2))
        (prim_pair (prim_fst Primrec.fst) Primrec.snd)
    exact (Primrec.ite h (Primrec.const 1) (Primrec.const 0)).to_comp

attribute [local irreducible] race

/-- The function whose fixed point is the race program: the race on the data with code `n`,
against the instance `G c n` of the program `c` on `n`. -/
def raceOn (chk : ℕ → ℕ × ℕ → Bool) (G : Code → ℕ → ℕ × ℕ) (c : Code) (n : ℕ) : Part ℕ :=
  race chk (Denumerable.ofNat HD n) (G c n)

/-- `raceOn chk G` is partial recursive when `chk` and `G` are primitive recursive. -/
theorem raceOn_part {chk : ℕ → ℕ × ℕ → Bool} {G : Code → ℕ → ℕ × ℕ} (hchk : Primrec₂ chk)
    (hG : Primrec₂ G) : Partrec₂ (raceOn chk G) := by
  have hd : Primrec fun x : Code × ℕ => Denumerable.ofNat HD x.2 :=
    (Primrec.ofNat HD).comp Primrec.snd
  exact (race_part hchk).comp (g := fun x : Code × ℕ => (Denumerable.ofNat HD x.2, G x.1 x.2))
    (hd.pair hG).to_comp

/-- `C` is the race program for the test `chk` and the instance family `G`. -/
def RaceOn (chk : ℕ → ℕ × ℕ → Bool) (G : Code → ℕ → ℕ × ℕ) (C : Code) : Prop :=
  C.eval = raceOn chk G C

/-- A race program exists for every primitive recursive test and instance family. -/
theorem exists_raceOn {chk : ℕ → ℕ × ℕ → Bool} {G : Code → ℕ → ℕ × ℕ} (hchk : Primrec₂ chk)
    (hG : Primrec₂ G) : ∃ C, RaceOn chk G C :=
  Code.fixed_point₂ (raceOn_part hchk hG)

/-- **Smullyan's argument, for any search.** Suppose `Q n` holds iff some proof of the instance
`G C n` passes the test, that output `1` of `C` on `n` makes `Q n` hold, and that output `0` makes
it fail. If `H` holds iff the halting search on the data `d` succeeds, then `H` holds iff `Q` holds
of the code of `d`. -/
theorem race_iff {chk : ℕ → ℕ × ℕ → Bool} {G : Code → ℕ → ℕ × ℕ} {C : Code}
    (hC : RaceOn chk G C) {Q : ℕ → Prop} (hQ : ∀ n, Q n ↔ ∃ k, chk k (G C n) = true)
    (pos : ∀ n, 1 ∈ C.eval n → Q n) (neg : ∀ n, 0 ∈ C.eval n → ¬ Q n)
    (d : HD) {H : Prop} (hd : H ↔ ∃ k, Test d k) : H ↔ Q (Encodable.encode d) := by
  have heval : C.eval (Encodable.encode d) = race chk d (G C (Encodable.encode d)) := by
    rw [hC, raceOn, Denumerable.ofNat_encode]
  have hp := pos (Encodable.encode d)
  have hn := neg (Encodable.encode d)
  have hq := hQ (Encodable.encode d)
  rw [heval] at hp hn
  generalize Q (Encodable.encode d) = q at hp hn hq ⊢
  generalize G C (Encodable.encode d) = i at hp hn hq
  constructor
  · intro hH
    by_contra hS
    obtain ⟨k₀, hk₀⟩ := hd.1 hH
    obtain ⟨k, hk, hm⟩ := mem_race (chk := chk) (d := d) (i := i) ⟨k₀, Or.inl hk₀⟩
    have hT : Test d k := hk.resolve_right fun hch => hS (hq.2 ⟨k, hch⟩)
    rw [ite_eq_left hT] at hm
    exact hS (hp hm)
  · intro hS
    by_contra hH
    obtain ⟨k₀, hk₀⟩ := hq.1 hS
    obtain ⟨k, _, hm⟩ := mem_race (chk := chk) (d := d) (i := i) ⟨k₀, Or.inr hk₀⟩
    have hT : ¬ Test d k := fun h => hH (hd.2 ⟨k, h⟩)
    rw [ite_eq_right hT] at hm
    exact hn hm hS

/-- **Smullyan's argument.** Under the hypotheses of `race_iff`, a `HaltProblem` instance `p`
holds iff `Q` holds of the code of the data of `p`. -/
theorem halt_iff {chk : ℕ → ℕ × ℕ → Bool} {G : Code → ℕ → ℕ × ℕ} {C : Code}
    (hC : RaceOn chk G C) {Q : ℕ → Prop} (hQ : ∀ n, Q n ↔ ∃ k, chk k (G C n) = true)
    (pos : ∀ n, 1 ∈ C.eval n → Q n) (neg : ∀ n, 0 ∈ C.eval n → ¬ Q n)
    (p : EncodableTM Bool × List Bool) : HaltProblem p ↔ Q (Encodable.encode (dataOf p)) :=
  race_iff hC hQ pos neg (dataOf p) (halt_iff_test p)

/-- **No machine decides a predicate with a suitable family of race instances.** Let `inst c n`
be an instance whose encoding is the binary digits of the pair of codes `G c n`. If the predicate
holds of `inst c n` exactly when some proof of `G c n` passes the test, holds when `c` outputs `1`
on `n`, and fails when `c` outputs `0`, then no machine decides it: such a machine would decide
whether a machine halts on its own code. -/
theorem not_machineDecidable_of_race {Y : Type*} {enc : Y → List Bool} {P : Y → Prop}
    {chk : ℕ → ℕ × ℕ → Bool} {G : Code → ℕ → ℕ × ℕ} (hchk : Primrec₂ chk) (hG : Primrec₂ G)
    (inst : Code → ℕ → Y) (henc : ∀ c n, enc (inst c n) = bitsOf (Nat.pair (G c n).1 (G c n).2))
    (hQ : ∀ c n, P (inst c n) ↔ ∃ k, chk k (G c n) = true)
    (pos : ∀ c n, 1 ∈ c.eval n → P (inst c n)) (neg : ∀ c n, 0 ∈ c.eval n → ¬ P (inst c n)) :
    ¬ MachineDecidable enc P := by
  rintro ⟨D, hD⟩
  obtain ⟨C, hC⟩ := exists_raceOn hchk hG
  let F : List Bool → List Bool := fun w =>
    bitsOf (Nat.pair (G C (Encodable.encode (dataC w))).1 (G C (Encodable.encode (dataC w))).2)
  have hF : Primrec F := by
    have h : Primrec fun w => G C (Encodable.encode (dataC w)) :=
      hG.comp (Primrec.const C) (Primrec.encode.comp dataC_prim)
    exact bitsOf_prim.comp (prim_natPair (prim_fst h) (prim_snd h))
  obtain ⟨R, hR⟩ := exists_computer F hF.to_comp
  have hiff : ∀ M : EncodableTM Bool, Halts M.toSingleTapeTM (encodeBoolTM M) ↔
      P (inst C (Encodable.encode (dataC (encodeBoolTM M)))) := fun M =>
    race_iff (Q := fun n => P (inst C n)) hC (hQ C) (pos C) (neg C) (dataC (encodeBoolTM M))
      selfHalt_iff_test
  refine self_halt_undecidable ⟨compComputer R D, fun M => ⟨fun hM => ?_, fun hM => ?_⟩⟩
  · have h₁ := (hD (inst C (Encodable.encode (dataC (encodeBoolTM M))))).1 ((hiff M).1 hM)
    rw [henc] at h₁
    exact compComputer_seq_outputs (hR _) h₁
  · have h₁ := (hD (inst C (Encodable.encode (dataC (encodeBoolTM M))))).2
      (fun h => hM ((hiff M).2 h))
    rw [henc] at h₁
    exact compComputer_seq_outputs (hR _) h₁

end DiagonaLean.Foundations.Computability.ProofRace
