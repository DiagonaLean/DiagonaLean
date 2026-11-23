/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude
-/

import DiagonaLean.Foundations.Computability.MachineBridge
import DiagonaLean.Foundations.Computability.HaltCanon

@[expose] public section

/-! # A machine that computes a reduction gives a computable function

`readOut` (`OutputSearch.lean`) reads one output bit. `readTape` reads the whole output: the cells
from the head to the first blank. If `M` outputs `l'` on `w` then `readTape` on the data of the run
returns `l'` (`mem_readTape`), and `readTape` is partial recursive (`readTape_part`).

This is the machine to function direction for outputs of any length. With a computable encoding of
the instances and a computable decoder of the outputs it gives
`computable_of_computesReduction`: a machine that computes `f` on the encodings shows that `f` is
`Computable`. The other direction is `exists_computes` (`Computer.lean`).

`HaltReduction.ofMachine` is the consequence for halting: a synthetic reduction from the halting
problem, together with a machine that computes it on a computable encoding of the canonical
instances, is a proved halting reduction. Before this, the same data gave only
`¬ MachineDecidable` (`not_machineDecidable_of_halt_reduces`).
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Halt.Undecidable
  DiagonaLean.Synthetic.Definitions
  DiagonaLean.Halt.Helpers Nat.Partrec

/-- The output of a halted numeric configuration: the cells from the head to the first blank. -/
def outList (c : SC) : List ℕ := (c.2.2.1 :: c.2.2.2).takeWhile fun n => decide (0 < n)

/-- Search for the first halting step and read the output there. -/
def readTape (d : List (ℕ × ℕ) × SC) : Part (List ℕ) :=
  (Nat.rfind fun k => Part.some (decide (Test d k))).map fun k => outList ((sstep d.1)^[k] d.2)

/-- `readTape` is partial recursive. -/
theorem readTape_part : Partrec readTape := by
  unfold readTape
  refine Partrec.map (Partrec.rfind ?_) ?_
  · have h : Primrec fun y : (List (ℕ × ℕ) × SC) × ℕ => decide (Test y.1 y.2) :=
      test_prim.decide
    exact (h.to_comp.partrec).of_eq fun y => rfl
  · have h : Primrec fun y : (List (ℕ × ℕ) × SC) × ℕ => outList ((sstep y.1.1)^[y.2] y.1.2) := by
      unfold outList; fun_prop
    exact h.to_comp

/-- Decoding a cell list to a `StackTape` drops only trailing blanks, so the cells up to the first
blank are the same. -/
theorem stk_takeWhile (a : List (Option Bool)) :
    ((stk a).toList).takeWhile Option.isSome = a.takeWhile Option.isSome := by
  induction a with
  | nil => rfl
  | cons o a ih =>
    cases o with
    | none =>
      rw [stk_cons]
      generalize stk a = t
      rcases t with ⟨_ | ⟨hd, tl⟩, hl⟩ <;> simp [StackTape.cons]
    | some x =>
      rw [stk_cons, StackTape.cons_some_toList]
      simp [ih]

theorem takeWhile_isSome_map_some (t : List Bool) :
    (t.map some).takeWhile Option.isSome = t.map some := by
  induction t with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- A symbol's code is positive unless it is blank. -/
theorem hc_pos_iff (o : Option Bool) : (0 < hc o) = (o.isSome = true) := by
  cases o with
  | none => simp [hc]
  | some b => cases b <;> simp [hc]

/-- Reading the codes up to the first blank, or taking the cells up to it and coding them. -/
theorem map_hc_takeWhile (r : List (Option Bool)) :
    (r.map hc).takeWhile (fun n => decide (0 < n)) = (r.takeWhile Option.isSome).map hc := by
  induction r with
  | nil => rfl
  | cons o r ih =>
    cases o with
    | none => simp [hc]
    | some b => cases b <;> simp [hc, ih]

/-- **The reader returns the whole output.** If `M` outputs `l'` on `w`, `readTape` on the data of
`M` on `w` returns the codes `b.toNat + 1` of the letters of `l'`. -/
theorem mem_readTape {M : EncodableTM Bool} {w l' : List Bool}
    (h : M.toSingleTapeTM.Outputs w l') :
    l'.map (fun b => b.toNat + 1) ∈ readTape (dataOf (M, w)) := by
  classical
  have hH : ∃ k, Test (dataOf (M, w)) k := (halt_iff_test (M, w)).1 (halts_of_outputs h)
  refine (Part.mem_map_iff _).2 ⟨Nat.find hH, ?_, ?_⟩
  · refine Nat.mem_rfind.2 ⟨?_, fun {m} hm => ?_⟩
    · simpa using Nat.find_spec hH
    · simpa using Nat.find_min hH hm
  · have hk : Test (dataOf (M, w)) (Nat.find hH) := Nat.find_spec hH
    generalize Nat.find hH = k at hk ⊢
    have hit : (sstep (rowsE M))^[k] (absD (initData w)) =
        absD ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM)) :=
      iterate_absD _ k
    have hk' : ((sstep (rowsE M))^[k] (absD (initData w))).1 = 0 := hk
    rw [hit] at hk'
    show outList ((sstep (rowsE M))^[k] (absD (initData w))) = _
    rw [hit]
    generalize hD : (dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM) = D at hk' ⊢
    have hs : D.state = Option.none := by
      rcases hx : D.state with _ | q
      · rfl
      · simp [absD, hx, qc] at hk'
    have hr := reaches_iterate (initData w : Data M.toSingleTapeTM) k
    rw [cfgOf_initData, hD] at hr
    have he : cfgOf D = ⟨Option.none, (cfgOf D).BiTape⟩ := by simp only [cfgOf, hs]
    rw [he] at hr
    have ht : (cfgOf D).BiTape = BiTape.mk₁ l' := halt_tape_unique hr h
    cases l' with
    | nil =>
      have hh : D.h = Option.none := by
        simpa [cfgOf, BiTape.mk₁, BiTape.nil] using congrArg BiTape.head ht
      simp [outList, absD, hh, hc]
    | cons a t =>
      have hh : D.h = some a := by
        simpa [cfgOf, BiTape.mk₁] using congrArg BiTape.head ht
      have hrt : stk D.r = StackTape.mapSome t := by
        simpa [cfgOf, BiTape.mk₁] using congrArg BiTape.right ht
      have hcut : D.r.takeWhile Option.isSome = t.map some := by
        have h1 := stk_takeWhile D.r
        rw [hrt] at h1
        rw [← h1]
        simp [StackTape.mapSome, takeWhile_isSome_map_some]
      have ha : 0 < hc (some a) := by cases a <;> simp [hc]
      simp only [outList, absD, hh]
      rw [List.takeWhile_cons_of_pos (by simpa using ha), map_hc_takeWhile, hcut]
      cases a <;> simp [hc, List.map_map, Function.comp_def]

/-- **A machine that computes a reduction on computable encodings makes it computable.** If `R`
takes `enc₁ x` to `enc₂ (f x)`, `enc₁` is computable and `enc₂` has a computable left inverse
`dec`, then `f` is computable. The machine's answer is `readTape` of the run, which is partial
recursive (`readTape_part`) and correct (`mem_readTape`). The other direction is `exists_computes`
(`Computer.lean`). -/
theorem computable_of_computesReduction {X Y : Type*} [Primcodable X] [Primcodable Y]
    {enc₁ : X → List Bool} {enc₂ : Y → List Bool} {f : X → Y} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R enc₁ enc₂ f) (h₁ : Computable enc₁)
    {dec : List Bool → Y} (hdec : Computable dec) (hd : ∀ y, dec (enc₂ y) = y) :
    Computable f := by
  have hm : Primrec fun l : List ℕ => l.map fun n => decide (n = 2) := by fun_prop
  have hg : Computable₂ fun (_ : X) (l : List ℕ) => dec (l.map fun n => decide (n = 2)) :=
    hdec.comp (hm.to_comp.comp Computable.snd)
  have hp : Partrec fun x => (readTape (dataOf (toEncodableTM R, enc₁ x))).map
      fun l => dec (l.map fun n => decide (n = 2)) :=
    Partrec.map (readTape_part.comp ((dataOf_prim _).to_comp.comp h₁)) hg
  refine Partrec.of_eq_tot hp fun x => ?_
  refine (Part.mem_map_iff _).2 ⟨(enc₂ (f x)).map fun b => b.toNat + 1, mem_readTape (hR x), ?_⟩
  have hmap : ((enc₂ (f x)).map fun b => b.toNat + 1).map (fun n => decide (n = 2)) =
      enc₂ (f x) := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (enc₂ (f x))]
    exact List.map_congr_left fun b _ => by cases b <;> simp
  rw [hmap, hd]

/-- **From a synthetic halting reduction and a machine to a proved one.** `r` is a synthetic
reduction from the halting problem to `Q`. If a machine `R` computes `r` on canonical machines
(`synthCanonToHalt`), taking the instance `encC (c, w)` to `enc (r.f (c.toTM, w))`, with `encC`
computable and `enc` having a computable left inverse, then `HaltCanon` reduces to `Q` with a proved
computable function. -/
def HaltReduction.ofMachine {β : Type*} [Primcodable β] {Q : β → Prop}
    (r : SynthHaltReduction Q) {encC : CanonTM × List Bool → List Bool} {enc : β → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encC enc (synthCanonToHalt.trans r).f)
    (hC : Computable encC) {dec : List Bool → β} (hdec : Computable dec)
    (hd : ∀ y, dec (enc y) = y) : HaltReduction Q :=
  ComputableReduction.ofSynth (synthCanonToHalt.trans r)
    (computable_of_computesReduction hR hC hdec hd)

end DiagonaLean.Foundations.Computability
