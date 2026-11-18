/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.Computability.HaltSearch
import DiagonaLean.Halt.Helpers

@[expose] public section

/-! # Reading a machine's output bit

`readOut d` searches for the first step at which the machine with data `d` has halted, and reads
the cell under the head: `1` if it holds `true`, and `0` otherwise. On the data of a machine on
an input (`dataOf`), the table records what the machine writes on its halting step, so if the
machine outputs `[b]` then `readOut` returns `1` for `true` and `0` for `false`
(`mem_readOut`). A program computing `readOut` exists (`exists_isReader`).

The code of a machine (`dataC`) does not record what the machine writes on its halting step, so
the reader runs on `dataOf`, which uses the machine's transition table.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing Nat.Partrec DiagonaLean.Halt.Encoding DiagonaLean.Halt.Helpers

/-- The output bit of a halted numeric configuration: `1` if the head holds `true`. -/
def outBit (c : SC) : ℕ := if c.2.2.1 = hc (some true) then 1 else 0

/-- `Test d k` is decidable. -/
instance (d : List (ℕ × ℕ) × SC) (k : ℕ) : Decidable (Test d k) :=
  inferInstanceAs (Decidable (_ = _))

/-- Search for the first halting step and read the output bit there. -/
def readOut (d : List (ℕ × ℕ) × SC) : Part ℕ :=
  (Nat.rfind fun k => Part.some (decide (Test d k))).map fun k => outBit ((sstep d.1)^[k] d.2)

/-- `readOut` is partial recursive. -/
theorem readOut_part : Partrec readOut := by
  unfold readOut
  refine Partrec.map (Partrec.rfind ?_) ?_
  · have h : Primrec fun y : (List (ℕ × ℕ) × SC) × ℕ => decide (Test y.1 y.2) :=
      test_prim.decide
    exact (h.to_comp.partrec).of_eq fun y => rfl
  · have hit : Primrec fun y : (List (ℕ × ℕ) × SC) × ℕ => (sstep y.1.1)^[y.2] y.1.2 :=
      Primrec.nat_iterate Primrec.snd (prim_snd Primrec.fst)
        (sstep_prim.comp (prim_pair (prim_fst (prim_fst Primrec.fst)) Primrec.snd)).to₂
    have h : Primrec fun y : (List (ℕ × ℕ) × SC) × ℕ => outBit ((sstep y.1.1)^[y.2] y.1.2) := by
      unfold outBit
      exact Primrec.ite (pred_eq (prim_fst (prim_snd (prim_snd hit))) (Primrec.const _))
        (Primrec.const 1) (Primrec.const 0)
    exact h.to_comp

/-- **The reader returns the output bit.** If `M` outputs `[b]` on `w`, then `readOut` on the
data of `M` on `w` returns `1` when `b` is `true` and `0` when it is `false`. -/
theorem mem_readOut {M : EncodableTM Bool} {w : List Bool} {b : Bool}
    (h : M.toSingleTapeTM.Outputs w [b]) : (if b then 1 else 0) ∈ readOut (dataOf (M, w)) := by
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
    show outBit ((sstep (rowsE M))^[k] (absD (initData w))) = if b then 1 else 0
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
    have ht : (cfgOf D).BiTape = BiTape.mk₁ [b] := halt_tape_unique hr h
    have hh : D.h = some b := by
      simpa [cfgOf, BiTape.mk₁] using congrArg BiTape.head ht
    cases b <;> simp [outBit, absD, hh, hc]

/-- `c` is a program that reads the output bit of the machine whose data has code `n`. -/
def IsReader (c : Code) : Prop :=
  ∀ n, c.eval n = readOut (Denumerable.ofNat (List (ℕ × ℕ) × SC) n)

/-- A reader program exists. -/
theorem exists_isReader : ∃ c, IsReader c := by
  have h : Partrec fun n => readOut (Denumerable.ofNat (List (ℕ × ℕ) × SC) n) :=
    readOut_part.comp (Computable.ofNat _)
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 h)
  exact ⟨c, fun n => by rw [hc]⟩

/-- If `M` outputs `[b]` on `w`, a reader program returns `1` for `true` and `0` for `false` on
the code of the data of `M` on `w`. -/
theorem mem_eval_of_outputs {c : Code} (hc : IsReader c) {M : EncodableTM Bool} {w : List Bool}
    {b : Bool} (h : M.toSingleTapeTM.Outputs w [b]) :
    (if b then 1 else 0) ∈ c.eval (Encodable.encode (dataOf (M, w))) := by
  rw [hc, Denumerable.ofNat_encode]
  exact mem_readOut h

end DiagonaLean.Foundations.Computability
