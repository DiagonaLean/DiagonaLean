/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.MachineLevel
import DiagonaLean.Foundations.Computability.HaltCanon

@[expose] public section

/-! # MPCP is halting-hard

The machine-level construction of `MachineLevel.lean` builds an MPCP instance from a transition
table (`startN`, `stackN`). Its correctness proof does not use that the input is the machine's own
code, so it holds for every machine and input (`halts_iff_mpcpN`). On canonical machines the table
is primitive recursive (`CanonTM.table`), and `stackN` depends on a table only through its lookup
and its set of state numbers (`mem_stackN_congr`), which `c.table` shares with the table of
`c.toTM`. So `(c, w) ↦ (startN c.start w, stackN c.table)` is a reduction from `HaltCanon` to MPCP,
proved computable: `MPCP.fromHalt`, a kernel-checked halting reduction.
-/

namespace DiagonaLean.MPCP.MachineLevel

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Computability.Normalize

section

attribute [local instance] EncodableTM.stateEncodable

/-- **A machine halts on an input iff the MPCP instance of its table on that input is solvable**:
the proof of `selfHalt_iff_instC`, for any input. -/
theorem halts_iff_mpcpN (M : EncodableTM Bool) (w : List Bool) :
    Halts M.toSingleTapeTM w ↔
      MPCP.Solvable (startN (Encodable.encode M.q₀) w) (stackN (rowsE M)) := by
  rw [halts_normTM_iff,
    halt_iff_mpcp (normEnc M) (normTM_noBlankWrites _) _ (normTM_noLeftBoundary _ _),
    mpcp_map_iff _ (Alpha.map_injective (stIdx_injective M)), ← startTile_ren]
  exact mpcp_congr _ (mem_stackN M)

end

/-- `normTrN` reads a table only through `lookup`. -/
theorem normTrN_congr {r₁ r₂ : List (ℕ × ℕ)} (h : ∀ k, lookup r₁ k = lookup r₂ k) (i c : ℕ)
    (a : Option Normalize.Sym2) : normTrN r₁ i c a = normTrN r₂ i c a := by
  unfold normTrN simN
  simp only [h]

/-- `stackN` depends on a table only through its lookup and its set of state numbers. -/
theorem mem_stackN_congr {r₁ r₂ : List (ℕ × ℕ)} (hl : ∀ k, lookup r₁ k = lookup r₂ k)
    (hi : ∀ i, i ∈ r₁.map (fun r => r.1.unpair.1) ↔ i ∈ r₂.map (fun r => r.1.unpair.1))
    (t : Tile (Alpha ℕ Normalize.Sym2)) : t ∈ stackN r₁ ↔ t ∈ stackN r₂ := by
  simp only [stackN, transN, List.mem_append, List.mem_flatMap, normTrN_congr hl]
  constructor <;> rintro ((((h | h) | h) | h) | h)
  all_goals first
    | exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    | exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    | exact Or.inl (Or.inr h)
    | exact Or.inr h
    | (obtain ⟨i, hi', rest⟩ := h
       exact Or.inl (Or.inl (Or.inr ⟨i, by first | exact (hi i).1 hi' | exact (hi i).2 hi', rest⟩)))

/-- The MPCP instance of a canonical machine on an input. -/
def canonInst (x : CanonTM × List Bool) :
    Tile (Alpha ℕ Normalize.Sym2) × Stack (Alpha ℕ Normalize.Sym2) :=
  (startN x.1.start x.2, stackN x.1.table)

theorem canonInst_prim : Primrec canonInst := by
  unfold canonInst
  fun_prop

/-- **A canonical machine halts on an input iff its MPCP instance is solvable.** -/
theorem haltCanon_iff_mpcp (x : CanonTM × List Bool) :
    HaltCanon x ↔ MPCP.DecisionProblem (canonInst x) := by
  obtain ⟨c, w⟩ := x
  refine (halts_iff_mpcpN c.toTM w).trans (mpcp_congr _ fun t => mem_stackN_congr ?_ ?_ t)
  · intro k
    rw [CanonTM.lookup_rowsE_toTM, CanonTM.lookup_table]
  · intro i
    rw [mem_idx, CanonTM.mem_idx_table]
    exact ⟨fun ⟨q, hq⟩ => hq ▸ q.isLt, fun h => ⟨⟨i, h⟩, rfl⟩⟩

end DiagonaLean.MPCP.MachineLevel

namespace DiagonaLean.MPCP

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.MPCP.MachineLevel

/-- **MPCP is halting-hard**, over the alphabet `Alpha ℕ Sym2`: a reduction from the halting problem
on canonical machines, proved computable. -/
def fromHalt : HaltReduction (@MPCP.DecisionProblem (Alpha ℕ Normalize.Sym2)) :=
  ⟨canonInst, canonInst_prim.to_comp, haltCanon_iff_mpcp⟩

theorem haltHard : HaltHard (@MPCP.DecisionProblem (Alpha ℕ Normalize.Sym2)) :=
  ⟨fromHalt⟩

end DiagonaLean.MPCP
