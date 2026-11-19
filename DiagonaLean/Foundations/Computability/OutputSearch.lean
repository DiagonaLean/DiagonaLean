/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.Computability.CodeSim
import DiagonaLean.Halt.Helpers
import DiagonaLean.Halt.Inseparable

@[expose] public section

/-! # Reading a machine's output bit

`readOut d` searches for the first step at which the machine with data `d` has halted, and reads
the cell under the head: `1` if it holds `true`, and `0` otherwise. On the data of a machine on
an input (`dataOf`), the table records what the machine writes on its halting step, so if the
machine outputs `[b]` then `readOut` returns `1` for `true` and `0` for `false`
(`mem_readOut`). A program computing `readOut` exists (`exists_isReader`).

The same holds on the data `dataC w` computed from a machine code `w`, which records every
transition, halting ones included: if `M` outputs `[b]` on its own code, `readOut` returns `b` on
`dataC (encodeBoolTM M)` (`selfOut_mem`). Unlike `dataOf`, `dataC` is primitive recursive in the
code, so this form composes with primitive recursive maps on codes.
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
  · have h : Primrec fun y : (List (ℕ × ℕ) × SC) × ℕ => outBit ((sstep y.1.1)^[y.2] y.1.2) := by
      unfold outBit; fun_prop
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

/-- A halted numeric configuration does not change. -/
theorem sstep_halt (rows : List (ℕ × ℕ)) {c : SC} (h : c.1 = 0) : sstep rows c = c := by
  simp [sstep, h]

/-- After the machine halts, the numeric configuration stays the same. -/
theorem iterate_sstep_of_le {d : List (ℕ × ℕ) × SC} {k₀ k : ℕ} (h₀ : Test d k₀) (hk : k₀ ≤ k) :
    (sstep d.1)^[k] d.2 = (sstep d.1)^[k₀] d.2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply', ih, sstep_halt _ h₀]

/-- If the machine has halted after `k` steps, `readOut` reads the head at step `k`. -/
theorem mem_readOut_of_test {d : List (ℕ × ℕ) × SC} {k : ℕ} (hk : Test d k) :
    outBit ((sstep d.1)^[k] d.2) ∈ readOut d := by
  classical
  have hex : ∃ k, Test d k := ⟨k, hk⟩
  rw [iterate_sstep_of_le (Nat.find_spec hex) (Nat.find_min' hex hk)]
  refine (Part.mem_map_iff _).2 ⟨_, Nat.mem_rfind.2 ⟨?_, fun {m} hm => ?_⟩, rfl⟩
  · simpa using Nat.find_spec hex
  · simpa using Nat.find_min hex hm

attribute [local instance] EncodableTM.stateEncodable

open DiagonaLean.Halt.Inseparable in
/-- **`readOut` reads the output of a machine run on its own code**, from the data `dataC` of the
code. -/
theorem selfOut_mem {b : Bool} {M : EncodableTM Bool} (h : SelfOut b M) :
    (if b then 1 else 0) ∈ readOut (dataC (encodeBoolTM M)) := by
  obtain ⟨k, hk⟩ := (outputs_iff_dstep _ _).1 h
  obtain ⟨h₀, ht⟩ := (cfgOf_eq_haltCfg_iff _ _).1 hk
  have hrun : (sstep (dataC (encodeBoolTM M)).1)^[k] (dataC (encodeBoolTM M)).2 =
      absD ((dstep M.toSingleTapeTM)^[k] (initData (encodeBoolTM M) : Data M.toSingleTapeTM)) := by
    simp only [dataC_code]
    rw [rowsC_eq_rowsE, iterate_absD]
  have hh : ((dstep M.toSingleTapeTM)^[k] (initData (encodeBoolTM M) : Data M.toSingleTapeTM)).h =
      some b := by simpa [BiTape.mk₁] using congrArg BiTape.head ht
  have hm := mem_readOut_of_test (d := dataC (encodeBoolTM M)) (k := k)
    (show (_ : SC).1 = 0 by rw [hrun]; exact h₀)
  rw [hrun] at hm
  cases b <;> simpa [outBit, absD, hc, hh] using hm

end DiagonaLean.Foundations.Computability
