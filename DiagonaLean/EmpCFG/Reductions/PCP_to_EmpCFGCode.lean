/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.EmpCFG.Reductions.PCP_to_EmpCFG
import DiagonaLean.PCP.Primrec
import DiagonaLean.Foundations.Grammar.Code

@[expose] public section

/-! # From PCP to the intersection of grammar codes

`pcpToEmpCFG` sends a PCP instance to two grammars of Mathlib's `ContextFreeGrammar`, which is not
`Primcodable`, so it says nothing about machines. Here the construction `genCFG` is written once as
a presentation, polymorphic in the name of its one nonterminal (`genPres`). With the name `()` it
presents `genCFG` itself (`toCFG_genPres_unit`); with the name `0` it is a grammar code, the
renaming of the first (`genPres_zero`), so it has the same language
(`language_toCFG_genPres_zero`). The codes of a PCP instance are primitive recursive in it
(`empCode_prim`), and correct (`pcp_reducesto_empCFGCode_spec`). The halting reduction
`EmpCFG.codeFromHaltTerm` built from it is in `Undecidable.lean`.

The statements are about grammar codes (`Foundations.Grammar.CFGCode`): a machine reads a finite
description, and `CFGCode.toCFG` is the grammar a code describes.

## Main statements

* `empCode`, `pcp_reducesto_empCFGCode_spec`, `empCode_prim`: the reduction from PCP to grammar
  codes, its correctness and its computability.
-/

namespace DiagonaLean.EmpCFG.Reduction

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
    @PCP.DecisionProblem α ⪯_s[empCode]
      fun c : CFGCode (Term α) × CFGCode (Term α) => IntersectionNonempty c.1.toCFG c.2.toCFG := by
  intro P
  rw [pcp_reducesto_empCFG_spec P]
  simp only [EmpCFG.DecisionProblem, IntersectionNonempty, pcpToEmpCFG, empCode,
    language_toCFG_genPres_zero]

variable [Primcodable α]

omit [DecidableEq α] in
/-- **The codes of a PCP instance are primitive recursive in it.** -/
@[fun_prop] theorem empCode_prim : Primrec (empCode (α := α)) := by
  unfold empCode genPres
  fun_prop

end DiagonaLean.EmpCFG.Reduction
