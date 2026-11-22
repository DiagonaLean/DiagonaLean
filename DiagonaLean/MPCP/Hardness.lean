/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.MachineLevel
import DiagonaLean.Foundations.Computability.HaltCanon

@[expose] public section

/-! # MPCP is halting-hard

The machine-level construction of `MachineLevel.lean` builds an MPCP instance from a transition
table (`instOf`), and is correct for every machine and input (`halts_iff_mpcpN`). On canonical
machines the table is primitive recursive (`CanonTM.table`), and `stackN` depends on a table only
through its lookup and its set of state numbers (`mem_stackN_congr`), which `c.table` shares with
the table of `c.toTM`. So `canonInst (c, w) = instOf c.start c.table w` is a reduction from
`HaltCanon` to MPCP, proved computable: `MPCP.fromHalt`, a kernel-checked halting reduction.

## Main statements

* `MPCP.fromHalt`, `MPCP.haltHard`: MPCP over `Alpha ℕ Sym2` is halting-hard.
* `not_computablePred_mpcp`, `not_machineDecidable_mpcp`: so it is not a computable predicate, and
  no Turing machine decides it under any computable encoding.
* `not_computablePred_mpcpOf`, `not_machineDecidable_mpcpOf`: the same over any nontrivial
  alphabet; `mpcp_manyOneEquiv`: MPCP is many-one equivalent over all of them.
-/

namespace DiagonaLean.MPCP.MachineLevel

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Computability.Normalize

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
  instOf x.1.start x.1.table x.2

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

namespace DiagonaLean.MPCP.MachineLevel

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

/-- **MPCP is not a computable predicate**, over the alphabet `Alpha ℕ Sym2`: it is halting-hard
(`MPCP.haltHard`). -/
theorem not_computablePred_mpcp :
    ¬ ComputablePred (@MPCP.DecisionProblem (Alpha ℕ Normalize.Sym2)) :=
  MPCP.haltHard.not_computablePred

/-- **No Turing machine decides MPCP**, over the alphabet `Alpha ℕ Sym2`, under any computable
encoding of instances as bit strings. -/
theorem not_machineDecidable_mpcp
    {enc : Tile (Alpha ℕ Normalize.Sym2) × Stack (Alpha ℕ Normalize.Sym2) →
      List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc MPCP.DecisionProblem :=
  MPCP.haltHard.not_machineDecidable henc

open Foundations.Codes in
/-- **MPCP is not a computable predicate over any nontrivial alphabet**: the lifting of
`not_computablePred_mpcp` (`Foundations.Codes.CodeFunctor.not_computablePred_lift`).
-/
theorem not_computablePred_mpcpOf {α : Type} [Primcodable α] [Nontrivial α] :
    ¬ ComputablePred (@MPCP.DecisionProblem α) := by
  code_lift mpcpFunctor from not_computablePred_mpcp

/-- **No Turing machine decides MPCP over any nontrivial alphabet**, under any computable
encoding. -/
theorem not_machineDecidable_mpcpOf {α : Type} [Primcodable α] [Nontrivial α]
    {enc : Tile α × Stack α → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc MPCP.DecisionProblem := by
  code_lift Reduction.mpcpFunctor from not_computablePred_mpcp

open Foundations.Codes in
/-- **Alphabet invariance of MPCP**: over any two nontrivial `Primcodable` alphabets, MPCP is
many-one equivalent, so every property closed under computable many-one reductions holds over all
of them or none (`ComputablePred.computable_of_manyOneReducible`,
`REPred.of_manyOneReducible`). -/
theorem mpcp_manyOneEquiv {α β : Type} [Primcodable α] [Primcodable β] [Nontrivial α]
    [Nontrivial β] :
    ManyOneEquiv (@MPCP.DecisionProblem α)
      (@MPCP.DecisionProblem β) := by
  code_lift mpcpFunctor

end DiagonaLean.MPCP.MachineLevel
