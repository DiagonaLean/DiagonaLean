/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.CodeSim
import DiagonaLean.Halt.Inseparable

@[expose] public section

/-! # Reading a machine's output bit by a partial recursive function

`outBit d` runs the numeric simulation `sstep` on the data `d` to its first halt and returns `1` if
the head then reads `1`, and `0` otherwise. On the data `dataC w` of a machine code `w` run on `w`
itself, it returns the bit that the machine outputs (`selfOut_mem`).

## Main statements

* `outBit_part`: `outBit` is partial recursive.
* `selfOut_mem`: if `M` outputs `[b]` on its own code, then `outBit` returns `b` on its data.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Halt.Inseparable

/-- The numeric configuration after `k` steps. -/
def runC (d : List (ℕ × ℕ) × SC) (k : ℕ) : SC := (sstep d.1)^[k] d.2

/-- A halted numeric configuration does not change. -/
theorem sstep_halt (rows : List (ℕ × ℕ)) {c : SC} (h : c.1 = 0) : sstep rows c = c := by
  simp [sstep, h]

/-- After the machine halts, the numeric configuration stays the same. -/
theorem runC_of_le {d : List (ℕ × ℕ) × SC} {k₀ k : ℕ} (h₀ : (runC d k₀).1 = 0) (hk : k₀ ≤ k) :
    runC d k = runC d k₀ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction j with
  | zero => rfl
  | succ j ih =>
    have h : runC d (k₀ + (j + 1)) = sstep d.1 (runC d (k₀ + j)) :=
      Function.iterate_succ_apply' (sstep d.1) (k₀ + j) d.2
    rw [h, ih, sstep_halt _ h₀]

/-- Run to the first halt; `1` if the head then reads `1` (code `2`), and `0` otherwise. -/
def outBit (d : List (ℕ × ℕ) × SC) : Part ℕ :=
  (Nat.rfind fun k => Part.some (decide ((runC d k).1 = 0))).map fun k =>
    if (runC d k).2.2.1 = 2 then 1 else 0

/-- If the machine has halted after `k` steps, `outBit` reads the head at step `k`. -/
theorem mem_outBit {d : List (ℕ × ℕ) × SC} {k : ℕ} (hk : (runC d k).1 = 0) :
    (if (runC d k).2.2.1 = 2 then 1 else 0) ∈ outBit d := by
  classical
  have hex : ∃ k, (runC d k).1 = 0 := ⟨k, hk⟩
  rw [runC_of_le (Nat.find_spec hex) (Nat.find_min' hex hk)]
  refine (Part.mem_map_iff _).2 ⟨_, Nat.mem_rfind.2 ⟨?_, fun {m} hm => ?_⟩, rfl⟩
  · simpa using Nat.find_spec hex
  · simpa using Nat.find_min hex hm

/-- `runC` is primitive recursive. -/
theorem runC_prim : Primrec fun x : (List (ℕ × ℕ) × SC) × ℕ => runC x.1 x.2 :=
  Primrec.nat_iterate Primrec.snd (prim_snd Primrec.fst)
    (Primrec₂.mk (sstep_prim.comp (prim_pair (prim_fst (prim_fst Primrec.fst)) Primrec.snd)))

/-- `outBit` is partial recursive. -/
theorem outBit_part : Partrec outBit := by
  unfold outBit
  refine Partrec.map (Partrec.rfind ?_) ?_
  · have h : Primrec fun y : (List (ℕ × ℕ) × SC) × ℕ => decide ((runC y.1 y.2).1 = 0) :=
      (pred_eq (prim_fst runC_prim) (Primrec.const 0)).decide
    exact (h.to_comp.partrec).of_eq fun y => rfl
  · exact (Primrec.ite (pred_eq (prim_fst (prim_snd (prim_snd runC_prim))) (Primrec.const 2))
      (Primrec.const 1) (Primrec.const 0)).to_comp

attribute [local instance] EncodableTM.stateEncodable

/-- **`outBit` reads the output of a machine run on its own code.** -/
theorem selfOut_mem {b : Bool} {M : EncodableTM Bool} (h : SelfOut b M) :
    (if b then 1 else 0) ∈ outBit (dataC (encodeBoolTM M)) := by
  obtain ⟨k, hk⟩ := (outputs_iff_dstep _ _).1 h
  obtain ⟨h₀, ht⟩ := (cfgOf_eq_haltCfg_iff _ _).1 hk
  have hrun : runC (dataC (encodeBoolTM M)) k =
      absD ((dstep M.toSingleTapeTM)^[k] (initData (encodeBoolTM M) : Data M.toSingleTapeTM)) := by
    simp only [runC, dataC_code]
    rw [rowsC_eq_rowsE, iterate_absD]
  have hh : ((dstep M.toSingleTapeTM)^[k] (initData (encodeBoolTM M) : Data M.toSingleTapeTM)).h =
      some b := by simpa [BiTape.mk₁] using congrArg BiTape.head ht
  have hm := mem_outBit (d := dataC (encodeBoolTM M)) (k := k) (by rw [hrun]; exact h₀)
  rw [hrun] at hm
  cases b <;> simpa [absD, hc, hh] using hm

end DiagonaLean.Foundations.Computability
