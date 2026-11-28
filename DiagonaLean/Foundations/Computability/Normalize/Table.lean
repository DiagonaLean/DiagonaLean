/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.Normalize.Normalize
import DiagonaLean.Foundations.Computability.CodeSim
import DiagonaLean.Foundations.Computability.MachineBridge
import DiagonaLean.Foundations.Computability.HaltCanon

@[expose] public section

/-! # The normalised machine of a transition table

The normalised machine of `tm` (`Normalize/Machine.lean`) has states `tm.State × Ctrl`. Here its
transition is computed from the transition table of `tm` in the format of `rowsE`, on the state
numbers `Nat.pair i c` (`stIdx`): `normTrN rows i c a` is the symbol written, the movement code
and the next-state code. The reductions from the halting problem on canonical machines read their
instances off a table through it.

## Main statements

* `normTrN_eq`: `normTrN` on `rowsE M` is `normTr` of `M`, in numbers.
* `normTrN_congr`: `normTrN` reads a table only through `lookup`.
* `CanonTM.sameTable`: the table of a canonical machine and the table of its machine have the same
  lookup and the same state numbers (`SameTable`).
-/

namespace DiagonaLean.Foundations.Computability.Normalize

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Foundations.Computability

/-- The transition of the normalised machine in a simulating control state (`simR` if `right`,
`simL` otherwise), from the transition table `rows` of the simulated machine, in state number `i` on
cell `a`. The result is the symbol written, the movement code `mvc` and the next-state code: `0`
halts, `Nat.pair j c + 1` is state number `j` with control state number `c`. -/
def simN (rows : List (ℕ × ℕ)) (i : ℕ) (right : Bool) (a : Option Normalize.Sym2) :
    Option Normalize.Sym2 × ℕ × ℕ :=
  if rowX (lookup rows (Nat.pair i (hc (decSym a)))) = 0 then
    (encSym (optOf (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), 0, 0)
  else if rowM (lookup rows (Nat.pair i (hc (decSym a)))) = 0 then
    (encSym (optOf (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), 0,
      Nat.pair (rowX (lookup rows (Nat.pair i (hc (decSym a)))) - 1) (if right then 1 else 2) + 1)
  else if rowM (lookup rows (Nat.pair i (hc (decSym a)))) = 2 then
    (encSym (optOf (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), (if right then 2 else 1),
      Nat.pair (rowX (lookup rows (Nat.pair i (hc (decSym a)))) - 1) (if right then 3 else 6) + 1)
  else
    (encSym (optOf (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), (if right then 1 else 2),
      Nat.pair (rowX (lookup rows (Nat.pair i (hc (decSym a)))) - 1) (if right then 5 else 4) + 1)

derive_primrec simN

/-- The transition `normTr` of the normalised machine, numerically, in state number `i` with control
state number `c` (the `Encodable` code of `Ctrl`), in the format of `simN`. -/
def normTrN (rows : List (ℕ × ℕ)) (i c : ℕ) (a : Option Normalize.Sym2) :
    Option Normalize.Sym2 × ℕ × ℕ :=
  if c = 0 then (some Mk, 2, Nat.pair i 1 + 1)
  else if c = 1 then simN rows i true a
  else if c = 2 then simN rows i false a
  else if c = 3 then (preserve a, 2, Nat.pair i 1 + 1)
  else if c = 4 then (preserve a, 2, Nat.pair i 2 + 1)
  else if c = 5 then
    (if a = some Mk then (some Mk, 2, Nat.pair i 4 + 1) else (preserve a, 1, Nat.pair i 1 + 1))
  else if c = 6 then (preserve a, 1, Nat.pair i 7 + 1)
  else (if a = some Mk then (some Mk, 2, Nat.pair i 1 + 1) else (preserve a, 0, Nat.pair i 2 + 1))

derive_primrec normTrN

section

variable (M : EncodableTM Bool)

attribute [local instance] EncodableTM.stateEncodable

/-- The number of a state of the normalised machine: the pair of the codes of its components. -/
def stIdx (s : M.State × Ctrl) : ℕ := Nat.pair (Encodable.encode s.1) (Encodable.encode s.2)

/-- `stIdx` is injective. -/
theorem stIdx_injective : Function.Injective (stIdx M) := fun s t h => by
  obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.1 h
  exact Prod.ext (Encodable.encode_injective h₁) (Encodable.encode_injective h₂)

/-- The numeric form of a transition of the normalised machine, in the format of `simN`. -/
def codeOf (r : Stmt Normalize.Sym2 × Option (M.State × Ctrl)) :
    Option Normalize.Sym2 × ℕ × ℕ :=
  (r.1.symbol, mvc r.1.movement, match r.2 with | none => 0 | some s => stIdx M s + 1)

/-- `simN` computes `simStep` from the transition table `rowsE M`. -/
theorem simN_eq (q : M.State) (right : Bool) (a : Option Normalize.Sym2) :
    simN (rowsE M) (Encodable.encode q) right a =
      codeOf M (simStep M.toSingleTapeTM q right a) := by
  unfold simN simStep
  rw [lookup_rowsE]
  obtain ⟨⟨wr, mv⟩, nx⟩ := M.tr q (decSym a)
  rcases nx with _ | q₂
  · simp [rowT, codeOf, qc, mvc, optOf_hc]
  · rcases mv with _ | _ | _ <;> cases right <;>
      simp [rowT, codeOf, qc, mvc, optOf_hc, stIdx, Ctrl.sim, Encodable.encode]

/-- `normTrN` computes `normTr` from the transition table `rowsE M`. -/
theorem normTrN_eq (q : M.State) (c : Ctrl) (a : Option Normalize.Sym2) :
    normTrN (rowsE M) (Encodable.encode q) (Encodable.encode c) a =
      codeOf M (normTr M.toSingleTapeTM q c a) := by
  cases c <;> simp [normTrN, normTr, simN_eq, codeOf, stIdx, mvc, Encodable.encode] <;>
    split_ifs <;> simp

/-- The state numbers read off `rowsE M` are the codes of the states of `M`. -/
theorem mem_idx (i : ℕ) :
    i ∈ (rowsE M).map (fun r => r.1.unpair.1) ↔ ∃ q : M.State, Encodable.encode q = i := by
  simp only [rowsE, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_map,
    Function.comp_def, Nat.unpair_pair]
  constructor
  · rintro ⟨q, -, -, -, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, mem_statesList q, none, mem_syms none, rfl⟩

/-- The numbers below `8` are the codes of the control states. -/
theorem mem_range_eight (c : ℕ) : c ∈ List.range 8 ↔ ∃ k : Ctrl, Encodable.encode k = c := by
  rw [List.mem_range]
  constructor
  · intro h
    have : ∀ c : Fin 8, ∃ k : Ctrl, Encodable.encode k = c.val := by decide
    exact this ⟨c, h⟩
  · rintro ⟨k, rfl⟩
    cases k <;> decide

end

/-- `normTrN` reads a table only through `lookup`. -/
theorem normTrN_congr {r₁ r₂ : List (ℕ × ℕ)} (h : ∀ k, lookup r₁ k = lookup r₂ k) (i c : ℕ)
    (a : Option Normalize.Sym2) : normTrN r₁ i c a = normTrN r₂ i c a := by
  unfold normTrN simN
  simp only [h]

/-- Two transition tables are **the same table** when they have the same lookup and the same set of
state numbers: the constructions on tables (`transN`, `stackN`, and the rewriting systems of
`SemiThue.Reduction.codeRules`) read a table only through these. -/
def SameTable (r₁ r₂ : List (ℕ × ℕ)) : Prop :=
  (∀ k, lookup r₁ k = lookup r₂ k) ∧
    ∀ i, i ∈ r₁.map (fun r => r.1.unpair.1) ↔ i ∈ r₂.map (fun r => r.1.unpair.1)

/-- **The table of a canonical machine is the table of its machine.** -/
theorem _root_.DiagonaLean.Foundations.Computability.CanonTM.sameTable (c : CanonTM) :
    SameTable (rowsE c.toTM) c.table := by
  refine ⟨fun k => by rw [CanonTM.lookup_rowsE_toTM, CanonTM.lookup_table], fun i => ?_⟩
  rw [mem_idx, CanonTM.mem_idx_table]
  exact ⟨fun ⟨q, hq⟩ => hq ▸ q.isLt, fun h => ⟨⟨i, h⟩, rfl⟩⟩

end DiagonaLean.Foundations.Computability.Normalize
