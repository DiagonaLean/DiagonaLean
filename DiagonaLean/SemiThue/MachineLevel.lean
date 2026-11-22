/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.SemiThue.Basic
import DiagonaLean.SemiThue.Reductions.Halt_to_SemiThue

@[expose] public section

/-! # No machine decides the word problem for string rewriting systems

`Reductions/Halt_to_SemiThue.lean` shows that a machine halts iff its configuration string
rewrites to the empty string under `tmRules`. Here the system is read off the machine's code, as
`MPCP.MachineLevel.instC` reads the MPCP tiles: the transition tiles `transN`, the absorb rules and
the final rule, over the alphabet `Alpha ℕ Sym2` (`codeRules`). The rules of the code are the rules
of the normalised machine with its states renamed to numbers (`mem_codeRules`), and renaming letters
injectively keeps derivability (`SRS.derives_map_iff`), so a machine halts on its own code iff the
start string of its code rewrites to the empty string (`selfHalt_iff_toEmpty`). The instance is
primitive recursive in the code (`toEmptyCode_prim`), and self-halting is undecidable.

## Main statements

* `not_computablePred_toEmpty`, `not_machineDecidable_toEmpty`: whether a string rewrites to the
  empty string in a string rewriting system is not computable.
* `not_computablePred_semiThue`, `not_machineDecidable_semiThue`: the word problem for string
  rewriting systems is not computable (Post, Markov 1947).
-/

namespace DiagonaLean.SemiThue.MachineLevel

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Computability
  DiagonaLean.MPCP.Normalize DiagonaLean.MPCP.MachineLevel DiagonaLean.SemiThue.Reduction
  DiagonaLean.Foundations.Grammar DiagonaLean.Synthetic.Definitions

/-- The absorb rules and the final rule, over `Alpha ℕ Sym2`. -/
def haltRules : SRS (Alpha ℕ MPCP.Normalize.Sym2) :=
  syms2.flatMap (fun a => [([↟ₜa, h⊥], [h⊥]), ([h⊥, ↟ₜa], [h⊥])]) ++ [([#, h⊥, #], [])]

/-- The rewriting system of a machine code: the transition tiles of `transN` as rules, the absorb
rules and the final rule. -/
def codeRules (rows : List (ℕ × ℕ)) : SRS (Alpha ℕ MPCP.Normalize.Sym2) :=
  (transN rows).map tileRule ++ haltRules

/-- **The instance of a machine code** `w`: its rewriting system, and the start string of the
normalised machine on input `w` itself. -/
def toEmptyCode (w : List Bool) :
    SRS (Alpha ℕ MPCP.Normalize.Sym2) × List (Alpha ℕ MPCP.Normalize.Sym2) :=
  (codeRules (rowsC w), (startN ((tokens w).headI - 1) w).bot)

derive_primrec tileRule [Primcodable α]

derive_primrec codeRules

derive_primrec toEmptyCode

section

variable (M : EncodableTM Bool)

attribute [local instance] EncodableTM.stateEncodable

/-- **The rules of the code are the renamed rules of the normalised machine.** -/
theorem mem_codeRules
    (lr : List (Alpha ℕ MPCP.Normalize.Sym2) × List (Alpha ℕ MPCP.Normalize.Sym2)) :
    lr ∈ (tmRules (normEnc M)).mapRules (Alpha.map (stIdx M)) ↔ lr ∈ codeRules (rowsE M) := by
  have hlist : (tmRules (normEnc M)).mapRules (Alpha.map (stIdx M)) =
      ((transitionTiles (normEnc M)).map (ren M)).map tileRule ++ haltRules := by
    simp only [SRS.mapRules, tmRules, List.map_append, List.map_map, haltRules, List.append_assoc]
    congr 1
    congr 1
    rw [absorbTiles, List.map_flatMap]; rfl
  rw [hlist, codeRules, List.mem_append, List.mem_append]
  refine or_congr ⟨fun h => ?_, fun h => ?_⟩ Iff.rfl
  · obtain ⟨T, hT, rfl⟩ := List.mem_map.1 h
    exact List.mem_map_of_mem ((mem_transN M T).1 hT)
  · obtain ⟨T, hT, rfl⟩ := List.mem_map.1 h
    exact List.mem_map_of_mem ((mem_transN M T).2 hT)

end

/-- **A machine halts on its own code iff the start string of its code rewrites to the empty
string.** -/
theorem selfHalt_iff_toEmpty (M : EncodableTM Bool) :
    Halts M.toSingleTapeTM (encodeBoolTM M) ↔ ToEmptyProblem (toEmptyCode (encodeBoolTM M)) := by
  let := M.stateEncodable
  have hq : (tokens (encodeBoolTM M)).headI - 1 = Encodable.encode M.q₀ := by
    rw [headI_tokens_code]; rfl
  have hstart : (startN (Encodable.encode M.q₀) (encodeBoolTM M)).bot =
      (block (normTM M.toSingleTapeTM)
        (initCfg (normTM M.toSingleTapeTM) (encInput (encodeBoolTM M)))).map
        (Alpha.map (stIdx M)) := by
    rw [← startTile_ren]; rfl
  rw [ToEmptyProblem, toEmptyCode, hq, rowsC_eq_rowsE, halts_normTM_iff,
    halt_iff_derives (tm := normEnc M) (normTM_noBlankWrites _) _ (normTM_noLeftBoundary _ _),
    ← SRS.derives_map_iff (f := Alpha.map (stIdx M)) (Alpha.map_injective (stIdx_injective M)),
    SRS.derives_congr (mem_codeRules M), hstart]
  rfl

/-- **Whether a string rewrites to the empty string is not a computable predicate**, for string
rewriting systems over `Alpha ℕ Sym2`. -/
theorem not_computablePred_toEmpty :
    ¬ ComputablePred fun x :
      SRS (Alpha ℕ MPCP.Normalize.Sym2) × List (Alpha ℕ MPCP.Normalize.Sym2) =>
        ToEmptyProblem x := by
  intro h
  have h' : ComputablePred fun w : List Bool => ToEmptyProblem (toEmptyCode w) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun x => ToEmptyProblem x) toEmptyCode_prim.to_comp) h
  obtain ⟨D, hD⟩ := machineDecidable_of_computablePred (enc := id) (dec := some)
    Computable.option_some (fun _ => rfl) h'
  refine Halt.Undecidable.self_halt_undecidable ⟨D, fun M => ?_⟩
  simpa only [id, ← selfHalt_iff_toEmpty] using hD (encodeBoolTM M)

/-- **No Turing machine decides whether a string rewrites to the empty string**, under any
computable encoding. -/
theorem not_machineDecidable_toEmpty
    {enc : SRS (Alpha ℕ MPCP.Normalize.Sym2) × List (Alpha ℕ MPCP.Normalize.Sym2) → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc ToEmptyProblem :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_toEmpty

/-- Rewriting to the empty string is the word problem with target `[]`. -/
def toEmptyReducesSemiThue {T : Type} : @ToEmptyProblem T ⪯ₘ @DecisionProblem T :=
  ⟨fun x => (x.1, x.2, []), fun _ => Iff.rfl⟩

/-- **The word problem for string rewriting systems is not a computable predicate** (Post, Markov
1947), over `Alpha ℕ Sym2`. -/
theorem not_computablePred_semiThue :
    ¬ ComputablePred (@DecisionProblem (Alpha ℕ MPCP.Normalize.Sym2)) :=
  not_computablePred_of_reduces toEmptyReducesSemiThue
    (Primrec.to_comp (by unfold toEmptyReducesSemiThue; fun_prop)) not_computablePred_toEmpty

/-- **No Turing machine decides the word problem for string rewriting systems**, under any
computable encoding. -/
theorem not_machineDecidable_semiThue
    {enc : SRS (Alpha ℕ MPCP.Normalize.Sym2) × List (Alpha ℕ MPCP.Normalize.Sym2) ×
      List (Alpha ℕ MPCP.Normalize.Sym2) → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc DecisionProblem :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_semiThue

end DiagonaLean.SemiThue.MachineLevel
