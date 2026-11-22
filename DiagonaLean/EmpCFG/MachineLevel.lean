/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.EmpCFG.Reductions.PCP_to_EmpCFG
import DiagonaLean.PCP.MachineLevel
import DiagonaLean.Foundations.Grammar.Code

@[expose] public section

/-! # No machine decides whether two grammar codes share a word

`pcpToEmpCFG` sends a PCP instance to two grammars of Mathlib's `ContextFreeGrammar`, which is not
`Primcodable`, so it says nothing about machines. Here the construction `genCFG` is written once as
a presentation, polymorphic in the name of its one nonterminal (`genPres`). With the name `()` it
presents `genCFG` itself (`toCFG_genPres_unit`); with the name `0` it is a grammar code, the
renaming of the first (`genPres_zero`), so it has the same language
(`language_toCFG_genPres_zero`). The codes of a PCP instance are primitive recursive in it
(`empCode_prim`), so the many-one reduction `pcpReducesEmpCFGCode` from PCP to the problem on
codes (`pcp_reducesto_empCFGCode_spec`) transfers `PCP.MachineLevel.not_computablePred_pcp`.

The statements are about grammar codes (`Foundations.Grammar.CFGCode`): a machine reads a finite
description, and `CFGCode.toCFG` is the grammar a code describes.

## Main statements

* `not_computablePred_empCFGCode`, `not_machineDecidable_empCFGCode`: whether the languages of two
  grammar codes intersect is not a computable predicate, and no Turing machine decides it under any
  computable encoding.
* `not_computablePred_empCFGCode_empty`, `not_machineDecidable_empCFGCode_empty`: the same for
  whether they are disjoint.
-/

namespace DiagonaLean.EmpCFG.MachineLevel

open DiagonaLean.PCP DiagonaLean.EmpCFG DiagonaLean.EmpCFG.Reduction
  DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

variable {α : Type} [DecidableEq α] {N : Type}

/-- The construction `genCFG proj P` as a presentation, with nonterminal `s`: for each tile `t`,
the rules `s → (proj t) · s · t` and `s → (proj t) · t`. -/
def genPres (s : N) (proj : Tile α → List α) (P : Stack α) : GrammarPres N (Term α) :=
  (s, P.flatMap fun t =>
    [(s, (proj t).map (fun a => .inl (.inl a)) ++ [.inr s] ++ [.inl (.inr t)]),
      (s, (proj t).map (fun a => .inl (.inl a)) ++ [.inl (.inr t)])])

/-- With the nonterminal `()`, the presentation is `genCFG` itself. -/
theorem toCFG_genPres_unit (proj : Tile α → List α) (P : Stack α) :
    (genPres () proj P).toCFG = genCFG proj P := by
  simp only [GrammarPres.toCFG, genCFG, genPres]
  congr 1
  ext r
  simp only [List.mem_toFinset, List.mem_map, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl | rfl⟩, rfl⟩
    · exact Or.inl ⟨t, ht, by simp [recRule, ruleOf, symOf]⟩
    · exact Or.inr ⟨t, ht, by simp [baseRule, ruleOf, symOf]⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨_, ⟨t, ht, Or.inl rfl⟩, by simp [recRule, ruleOf, symOf]⟩
    · exact ⟨_, ⟨t, ht, Or.inr rfl⟩, by simp [baseRule, ruleOf, symOf]⟩

omit [DecidableEq α] in
/-- With the nonterminal `0`, the presentation is the renaming of the one with `()`. -/
theorem genPres_zero (proj : Tile α → List α) (P : Stack α) :
    genPres 0 proj P = (genPres () proj P).map id (fun _ => 0) := by
  simp [genPres, GrammarPres.map, List.map_flatMap, Function.comp_def]

/-- The code with the nonterminal `0` has the language of `genCFG`. -/
theorem language_toCFG_genPres_zero (proj : Tile α → List α) (P : Stack α) :
    (genPres 0 proj P).toCFG.language = (genCFG proj P).language := by
  rw [genPres_zero, language_map_toCFG (fun _ _ _ => rfl), toCFG_genPres_unit]

/-- **The reduction on codes.** The two grammar codes of a PCP instance. -/
def empCode (P : Stack α) : CFGCode (Term α) × CFGCode (Term α) :=
  (genPres 0 Tile.top P, genPres 0 Tile.bot P)

/-- `empCode` witnesses the reduction from PCP to the non-emptiness of the intersection of the
languages of two grammar codes. -/
theorem pcp_reducesto_empCFGCode_spec :
    @PCP.DecisionProblem α ⪯ₘ[empCode]
      fun c : CFGCode (Term α) × CFGCode (Term α) => IntersectionNonempty c.1.toCFG c.2.toCFG := by
  intro P
  rw [pcp_reducesto_empCFG_spec P]
  simp only [EmpCFG.DecisionProblem, IntersectionNonempty, pcpToEmpCFG, empCode,
    language_toCFG_genPres_zero]

/-- PCP many-one reduces to the non-emptiness of the intersection of the languages of two grammar
codes, through `empCode`. -/
def pcpReducesEmpCFGCode :
    @PCP.DecisionProblem α ⪯ₘ
      fun c : CFGCode (Term α) × CFGCode (Term α) => IntersectionNonempty c.1.toCFG c.2.toCFG :=
  ⟨empCode, pcp_reducesto_empCFGCode_spec⟩

variable [Primcodable α]

omit [DecidableEq α] in
/-- **The codes of a PCP instance are primitive recursive in it.** -/
theorem empCode_prim : Primrec (empCode (α := α)) := by
  unfold empCode genPres
  fun_prop

/-- **Whether the languages of two grammar codes intersect is not a computable predicate**, over
the terminals `Term α`, for any alphabet `α` with two distinct letters. -/
theorem not_computablePred_empCFGCode [Nontrivial α] :
    ¬ ComputablePred fun c : CFGCode (Term α) × CFGCode (Term α) =>
      IntersectionNonempty c.1.toCFG c.2.toCFG :=
  not_computablePred_of_reduces pcpReducesEmpCFGCode empCode_prim.to_comp
    PCP.MachineLevel.not_computablePred_pcp

/-- **Whether the languages of two grammar codes are disjoint is not a computable predicate.** -/
theorem not_computablePred_empCFGCode_empty [Nontrivial α] :
    ¬ ComputablePred fun c : CFGCode (Term α) × CFGCode (Term α) =>
      IntersectionEmpty c.1.toCFG c.2.toCFG := fun h => by
  refine not_computablePred_empCFGCode (α := α) ?_
  have := h.not
  simpa [not_intersectionEmpty_iff_nonempty] using this

/-- **No Turing machine decides whether the languages of two grammar codes intersect**, under any
computable encoding of pairs of codes as bit strings. -/
theorem not_machineDecidable_empCFGCode [Nontrivial α]
    {enc : CFGCode (Term α) × CFGCode (Term α) → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc fun c => IntersectionNonempty c.1.toCFG c.2.toCFG :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_empCFGCode

/-- **No Turing machine decides whether the languages of two grammar codes are disjoint**, under
any computable encoding of pairs of codes as bit strings. -/
theorem not_machineDecidable_empCFGCode_empty [Nontrivial α]
    {enc : CFGCode (Term α) × CFGCode (Term α) → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc fun c => IntersectionEmpty c.1.toCFG c.2.toCFG :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_empCFGCode_empty

end DiagonaLean.EmpCFG.MachineLevel
