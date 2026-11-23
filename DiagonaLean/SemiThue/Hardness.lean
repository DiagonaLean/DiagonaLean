/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.SemiThue.AlphabetLift
import DiagonaLean.MPCP.Hardness

@[expose] public section

/-! # The word problem for string rewriting systems is halting-hard

The construction of `MachineLevel.lean` builds a rewriting system and a start string from a
transition table (`toEmptyOf`), and is correct for every machine and input (`halts_iff_toEmptyN`).
Its rules depend on the table only through its lookup and its state numbers
(`mem_codeRules_congr`), which the table `c.table` of a canonical machine shares with the table of
`c.toTM` (`CanonTM.sameTable`), as for MPCP. So `canonToEmpty (c, w) = toEmptyOf c.start c.table w`
is a reduction from `HaltCanon`, proved computable.

## Main statements

* `SemiThue.toEmptyFromHalt`: rewriting to the empty string is halting-hard.
* `SemiThue.fromHalt`, `SemiThue.posFromHalt`: the word problem, and the word problem for systems
  with non-empty left sides, are halting-hard, over `Alpha ℕ Sym2`.
* `SemiThue.posFromHaltOver`, `SemiThue.fromHaltOver b0 b1 hne`, `SemiThue.fromHaltBool`: over any
  alphabet with two distinct letters.
* `not_computablePred_semiThue`, `not_machineDecidable_semiThue`, `not_computablePred_toEmpty`,
  `not_computablePred_semiThuePos`, and over every nontrivial alphabet
  `not_computablePred_semiThueOf`, `not_machineDecidable_semiThueOf`,
  `not_computablePred_semiThuePosOf`: the word problem (Post, Markov 1947) and its variants are not
  computable predicates, and no Turing machine decides them under any computable encoding.
-/

namespace DiagonaLean.SemiThue.MachineLevel

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.MPCP.MachineLevel
  DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Grammar

/-- `codeRules` depends on a table only through its lookup and its set of state numbers. -/
theorem mem_codeRules_congr {r₁ r₂ : List (ℕ × ℕ)} (h : SameTable r₁ r₂)
    (lr : List (Alpha ℕ Normalize.Sym2) × List (Alpha ℕ Normalize.Sym2)) :
    lr ∈ codeRules r₁ ↔ lr ∈ codeRules r₂ := by
  simp only [codeRules, List.mem_append, List.mem_map, mem_transN_congr h]

/-- The rewriting instance of a canonical machine on an input. -/
def canonToEmpty (x : CanonTM × List Bool) :
    SRS (Alpha ℕ Normalize.Sym2) × List (Alpha ℕ Normalize.Sym2) :=
  toEmptyOf x.1.start x.1.table x.2

theorem canonToEmpty_prim : Primrec canonToEmpty := by
  unfold canonToEmpty
  fun_prop

/-- **A canonical machine halts on an input iff the start string of its instance rewrites to the
empty string.** -/
theorem haltCanon_iff_toEmpty (x : CanonTM × List Bool) :
    HaltCanon x ↔ ToEmptyProblem (canonToEmpty x) := by
  obtain ⟨c, w⟩ := x
  exact (halts_iff_toEmptyN c.toTM w).trans
    (SRS.derives_congr (mem_codeRules_congr (CanonTM.sameTable c)) _ _)

/-- The word problem of the instance with target `[]`. -/
def canonWord (x : CanonTM × List Bool) :
    SRS (Alpha ℕ Normalize.Sym2) × List (Alpha ℕ Normalize.Sym2) × List (Alpha ℕ Normalize.Sym2) :=
  ((canonToEmpty x).1, (canonToEmpty x).2, [])

theorem canonWord_prim : Primrec canonWord := by
  have := canonToEmpty_prim
  unfold canonWord
  fun_prop

end DiagonaLean.SemiThue.MachineLevel

namespace DiagonaLean.SemiThue

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.SemiThue.MachineLevel

/-- **Whether a string rewrites to the empty string is halting-hard**, over `Alpha ℕ Sym2`: a
reduction from the halting problem on canonical machines, proved computable. -/
def toEmptyFromHalt : HaltReduction (@ToEmptyProblem (Alpha ℕ Normalize.Sym2)) :=
  ⟨canonToEmpty, canonToEmpty_prim.to_comp, haltCanon_iff_toEmpty⟩

/-- **The word problem for string rewriting systems is halting-hard** (Post, Markov 1947), over
`Alpha ℕ Sym2`. -/
def fromHalt : HaltReduction (@DecisionProblem (Alpha ℕ Normalize.Sym2)) :=
  ⟨canonWord, canonWord_prim.to_comp, haltCanon_iff_toEmpty⟩

theorem haltHard : HaltHard (@DecisionProblem (Alpha ℕ Normalize.Sym2)) :=
  ⟨fromHalt⟩

/-- **The word problem for systems with non-empty left sides is halting-hard**, over
`Alpha ℕ Sym2`: the systems of `canonWord` have non-empty left sides (`codeRules_lhs_ne`). -/
def posFromHalt : HaltReduction (@DecisionProblemPos (Alpha ℕ Normalize.Sym2)) :=
  ⟨canonWord, canonWord_prim.to_comp,
    fun x => (haltCanon_iff_toEmpty x).trans (and_iff_right (codeRules_lhs_ne _)).symm⟩

/-- **The word problem for systems with non-empty left sides is halting-hard over any alphabet with
two distinct letters**: `posFromHalt`, then the change of alphabet along `semiThueFunctor`. -/
def posFromHaltOver {α : Type} [Primcodable α] (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction (@DecisionProblemPos α) := by
  code_lift semiThueFunctor from posFromHalt

/-- **The word problem for string rewriting systems is halting-hard over any alphabet with two
distinct letters**: `posFromHaltOver`, then `synthFromPos`, proved computable (`posToWord_prim`). -/
def fromHaltOver {α : Type} [Primcodable α] (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction (@DecisionProblem α) := by
  reduce_from (posFromHaltOver b0 b1 hne) via (SemiThue.synthFromPos b0)

/-- **The word problem for string rewriting systems over `Bool` is halting-hard.** -/
def fromHaltBool : HaltReduction (@DecisionProblem Bool) :=
  fromHaltOver false true Bool.false_ne_true

end DiagonaLean.SemiThue

namespace DiagonaLean.SemiThue.MachineLevel

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Grammar DiagonaLean.Synthetic.Definitions

variable {α : Type}

/-- **Whether a string rewrites to the empty string is not a computable predicate**, for string
rewriting systems over `Alpha ℕ Sym2`: it is halting-hard (`SemiThue.toEmptyFromHalt`). -/
theorem not_computablePred_toEmpty :
    ¬ ComputablePred fun x :
      SRS (Alpha ℕ Normalize.Sym2) × List (Alpha ℕ Normalize.Sym2) =>
        ToEmptyProblem x :=
  SemiThue.toEmptyFromHalt.not_computablePred

/-- **No Turing machine decides whether a string rewrites to the empty string**, under any
computable encoding. -/
theorem not_machineDecidable_toEmpty
    {enc : SRS (Alpha ℕ Normalize.Sym2) × List (Alpha ℕ Normalize.Sym2) →
      List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc ToEmptyProblem :=
  SemiThue.toEmptyFromHalt.not_machineDecidable henc

/-- **The word problem for string rewriting systems is not a computable predicate** (Post, Markov
1947), over `Alpha ℕ Sym2`: it is halting-hard (`SemiThue.fromHalt`). -/
theorem not_computablePred_semiThue :
    ¬ ComputablePred (@DecisionProblem (Alpha ℕ Normalize.Sym2)) :=
  SemiThue.fromHalt.not_computablePred

/-- **No Turing machine decides the word problem for string rewriting systems**, under any
computable encoding. -/
theorem not_machineDecidable_semiThue
    {enc : SRS (Alpha ℕ Normalize.Sym2) × List (Alpha ℕ Normalize.Sym2) ×
      List (Alpha ℕ Normalize.Sym2) → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc DecisionProblem :=
  SemiThue.fromHalt.not_machineDecidable henc

/-- **The restricted word problem is not a computable predicate** over `Alpha ℕ Sym2`: it is
halting-hard (`SemiThue.posFromHalt`). -/
theorem not_computablePred_semiThuePos :
    ¬ ComputablePred (@DecisionProblemPos (Alpha ℕ Normalize.Sym2)) :=
  SemiThue.posFromHalt.not_computablePred

/-- **The restricted word problem is not a computable predicate over any nontrivial alphabet**: it
is halting-hard there (`SemiThue.posFromHaltOver`). -/
theorem not_computablePred_semiThuePosOf [Primcodable α] [Nontrivial α] :
    ¬ ComputablePred (@DecisionProblemPos α) := by
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne α
  exact (SemiThue.posFromHaltOver b0 b1 hne).not_computablePred

/-- **The word problem for string rewriting systems is not a computable predicate over any
nontrivial alphabet**: it is halting-hard there (`SemiThue.fromHaltOver`). -/
theorem not_computablePred_semiThueOf [Primcodable α] [Nontrivial α] :
    ¬ ComputablePred (@DecisionProblem α) := by
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne α
  exact (SemiThue.fromHaltOver b0 b1 hne).not_computablePred

/-- **No Turing machine decides the word problem for string rewriting systems over any nontrivial
alphabet**, under any computable encoding. -/
theorem not_machineDecidable_semiThueOf [Primcodable α] [Nontrivial α]
    {enc : SRS α × List α × List α → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc (@DecisionProblem α) :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_semiThueOf

end DiagonaLean.SemiThue.MachineLevel
