/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.AmbigCFG.Reductions.PCP_to_AmbigCFG
import DiagonaLean.AmbigCFG.Rename
import DiagonaLean.PCP.MachineLevel

@[expose] public section

/-! # No machine decides whether a grammar code is ambiguous

`pcpToAmbigCFG` sends a PCP instance `P` to a grammar of Mathlib's `ContextFreeGrammar` over the
terminals `α ⊕ Fin P.length`, which is not `Primcodable`, so it says nothing about machines. Here
the construction is written once as a presentation, polymorphic in the names of its three
nonterminals and in the terminals that index the tiles (`ambPres`). With `PCPNonterm` and `Fin n`
it presents `Stack.toGrammar` (`toCFG_ambPres_abs`); with `0, 1, 2` and natural numbers it is a
grammar code over `α ⊕ ℕ` (`ambCode`), the renaming of the first (`ambCode_eq_map`). Injective
renamings keep and reflect ambiguity (`AmbigCFG.decisionProblem_map_iff`), so PCP many-one reduces
to the ambiguity of grammar codes (`pcp_reducesto_ambigCFGCode_spec`, `AmbigCFG.synthCodeFromPCP`),
through a primitive recursive function (`ambCode_prim`), and
`PCP.MachineLevel.not_computablePred_pcp` transfers.

The statements are about grammar codes (`Foundations.Grammar.CFGCode`): a machine reads a finite
description, and `CFGCode.toCFG` is the grammar a code describes.

The reductions are also proved computable: `AmbigCFG.codeFromPCP`, and the halting reduction
`AmbigCFG.codeFromHaltOver b0 b1 hne` (from `PCP.fromHaltOver`).


## Main statements

* `not_computablePred_ambigCFGCode`, `not_machineDecidable_ambigCFGCode`: whether a grammar code is
  ambiguous is not a computable predicate, and no Turing machine decides it under any computable
  encoding.
-/

namespace DiagonaLean.AmbigCFG.MachineLevel

open DiagonaLean.PCP DiagonaLean.AmbigCFG DiagonaLean.AmbigCFG.Reduction
  DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

variable {α : Type} {N I : Type}

/-- The grammar of a PCP instance as a presentation, with start symbol `S`, nonterminals `A` and
`B` for the top and bottom words, and the list `ts` of tiles with the terminals that index them:
`S → A`, `S → B`, and for each `(i, t)` the rules `A → t.top · A · i`, `A → t.top · i`,
`B → t.bot · B · i`, `B → t.bot · i`. -/
def ambPres (S A B : N) (ts : List (I × Tile α)) : GrammarPres N (α ⊕ I) :=
  (S, [(S, [.inr A]), (S, [.inr B])] ++ ts.flatMap fun it =>
    [(A, it.2.top.map (fun a => .inl (.inl a)) ++ [.inr A, .inl (.inr it.1)]),
      (A, it.2.top.map (fun a => .inl (.inl a)) ++ [.inl (.inr it.1)]),
      (B, it.2.bot.map (fun a => .inl (.inl a)) ++ [.inr B, .inl (.inr it.1)]),
      (B, it.2.bot.map (fun a => .inl (.inl a)) ++ [.inl (.inr it.1)])])

/-- Renaming the index terminals by `g` and the nonterminals by `e` renames the parameters. -/
theorem ambPres_map {I' N' : Type} (g : I → I') (e : N → N') (S A B : N)
    (ts : List (I × Tile α)) :
    (ambPres S A B ts).map (Sum.map id g) e =
      ambPres (e S) (e A) (e B) (ts.map (Prod.map g id)) := by
  simp [ambPres, GrammarPres.map, List.map_flatMap, List.flatMap_map, Function.comp_def]

/-- The tiles of `P` with their indices in `Fin P.length`. -/
def absTs (P : Stack α) : List (Fin P.length × Tile α) :=
  (List.finRange P.length).map fun i => (i, P[i])

/-- The tiles of `P` with their indices as numbers. -/
def codeTs (P : Stack α) : List (ℕ × Tile α) :=
  (List.range P.length).map fun i => (i, P.getD i ⟨[], []⟩)

/-- Forgetting the bounds of the indices of `absTs P` gives `codeTs P`. -/
theorem absTs_map_val (P : Stack α) : (absTs P).map (Prod.map Fin.val id) = codeTs P := by
  apply List.ext_getElem
  · simp [absTs, codeTs]
  · intro i h₁ h₂
    simp only [absTs, List.length_map, List.length_finRange] at h₁
    simp [absTs, codeTs, List.getElem?_eq_getElem h₁]

/-- **The reduction on codes.** The grammar code of a PCP instance. -/
def ambCode (P : Stack α) : CFGCode (α ⊕ ℕ) := ambPres 0 1 2 (codeTs P)

/-- The names of `PCPNonterm` as numbers. -/
def ntIdx : PCPNonterm → ℕ
  | .S => 0
  | .A => 1
  | .B => 2

/-- `ntIdx` is injective. -/
theorem ntIdx_injective : Function.Injective ntIdx := by
  intro a b h; cases a <;> cases b <;> first | rfl | (simp [ntIdx] at h)

/-- The code of `P` is the renaming of the presentation with `PCPNonterm` and `Fin P.length`. -/
theorem ambCode_eq_map (P : Stack α) :
    ambCode P = (ambPres PCPNonterm.S PCPNonterm.A PCPNonterm.B (absTs P)).map
      (Sum.map id Fin.val) ntIdx := by
  rw [ambPres_map, absTs_map_val]; rfl

variable [DecidableEq α]

/-- With `PCPNonterm` and `Fin P.length`, the presentation is `Stack.toGrammar P`. -/
theorem toCFG_ambPres_abs (P : Stack α) :
    (ambPres PCPNonterm.S PCPNonterm.A PCPNonterm.B (absTs P)).toCFG = P.toGrammar := by
  simp only [GrammarPres.toCFG, Stack.toGrammar, ambPres]
  congr 1
  ext r
  simp only [List.mem_toFinset, List.mem_map, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, absTs, List.mem_finRange, true_and, Finset.mem_union, rulesS,
    rulesA, rulesB, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨s, (rfl | rfl) | ⟨_, ⟨i, rfl⟩, rfl | rfl | rfl | rfl⟩, rfl⟩ <;>
      (simp only [ruleOf, symOf, Fin.getElem_fin, List.map_append, List.map_map, Function.comp_def,
           Sum.elim_inl, List.map_cons, List.map_nil, ContextFreeRule.mk.injEq, reduceCtorEq,
           false_and, or_self, recProd, liftWord, idxSym, baseProd, List.append_singleton_inj,
           Symbol.terminal.injEq, Sum.inr.injEq, exists_false, true_and, false_or, or_false,
           Sum.elim_inr, List.cons.injEq, Symbol.nonterminal.injEq, and_true, and_false, or_true]
       try exact ⟨i, by simp⟩)
  · rintro (((rfl | rfl) | ⟨i, rfl | rfl⟩) | ⟨i, rfl | rfl⟩)
    · exact ⟨_, Or.inl (Or.inl rfl), by simp [ruleOf, symOf]⟩
    · exact ⟨_, Or.inl (Or.inr rfl), by simp [ruleOf, symOf]⟩
    · exact ⟨_, Or.inr ⟨_, ⟨i, rfl⟩, Or.inl rfl⟩,
        by simp [ruleOf, symOf, recProd, liftWord, idxSym, Function.comp_def]⟩
    · exact ⟨_, Or.inr ⟨_, ⟨i, rfl⟩, Or.inr (Or.inl rfl)⟩,
        by simp [ruleOf, symOf, baseProd, liftWord, idxSym, Function.comp_def]⟩
    · exact ⟨_, Or.inr ⟨_, ⟨i, rfl⟩, Or.inr (Or.inr (Or.inl rfl))⟩,
        by simp [ruleOf, symOf, recProd, liftWord, idxSym, Function.comp_def]⟩
    · exact ⟨_, Or.inr ⟨_, ⟨i, rfl⟩, Or.inr (Or.inr (Or.inr rfl))⟩,
        by simp [ruleOf, symOf, baseProd, liftWord, idxSym, Function.comp_def]⟩

/-- `ambCode` witnesses the reduction from PCP to the ambiguity of grammar codes. -/
theorem pcp_reducesto_ambigCFGCode_spec [Nonempty α] :
    @PCP.DecisionProblem α ⪯_s[ambCode]
      fun c : CFGCode (α ⊕ ℕ) => AmbigCFG.DecisionProblem c.toCFG := by
  intro P
  beta_reduce
  rw [pcp_iff_ambigcfg, ← toCFG_ambPres_abs, ambCode_eq_map,
    decisionProblem_map_iff (Function.injective_id.sumMap Fin.val_injective) ntIdx_injective]

/-- PCP many-one reduces to the ambiguity of grammar codes, through `ambCode`. -/
def _root_.DiagonaLean.AmbigCFG.synthCodeFromPCP [Nonempty α] :
    @PCP.DecisionProblem α ⪯_s fun c : CFGCode (α ⊕ ℕ) => AmbigCFG.DecisionProblem c.toCFG :=
  ⟨ambCode, pcp_reducesto_ambigCFGCode_spec⟩

/-- The former name of `AmbigCFG.synthCodeFromPCP`. -/
@[deprecated DiagonaLean.AmbigCFG.synthCodeFromPCP (since := "2026-11-23")]
abbrev pcpReducesAmbigCFGCode := @DiagonaLean.AmbigCFG.synthCodeFromPCP

variable [Primcodable α]

omit [DecidableEq α] in
/-- **The code of a PCP instance is primitive recursive in it.** -/
@[fun_prop] theorem ambCode_prim : Primrec (ambCode (α := α)) := by
  unfold ambCode ambPres codeTs
  fun_prop

/-- **Whether a grammar code is ambiguous is not a computable predicate**, over the terminals
`α ⊕ ℕ`, for any alphabet `α` with two distinct letters. -/
theorem not_computablePred_ambigCFGCode [Nontrivial α] :
    ¬ ComputablePred fun c : CFGCode (α ⊕ ℕ) => AmbigCFG.DecisionProblem c.toCFG :=
  not_computablePred_of_reduces AmbigCFG.synthCodeFromPCP ambCode_prim.to_comp
    PCP.MachineLevel.not_computablePred_pcp

/-- **No Turing machine decides whether a grammar code is ambiguous**, under any computable
encoding of codes as bit strings. -/
theorem not_machineDecidable_ambigCFGCode [Nontrivial α] {enc : CFGCode (α ⊕ ℕ) → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc fun c => AmbigCFG.DecisionProblem c.toCFG :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_ambigCFGCode

end DiagonaLean.AmbigCFG.MachineLevel

namespace DiagonaLean.AmbigCFG

open DiagonaLean.AmbigCFG.MachineLevel DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Grammar

variable {α : Type} [DecidableEq α] [Primcodable α]

/-- **The reduction from PCP to ambiguity of grammar codes, proved computable** (`ambCode_prim`). -/
def codeFromPCP [Nonempty α] : @PCP.DecisionProblem α ⪯
    fun c : CFGCode (α ⊕ ℕ) => AmbigCFG.DecisionProblem c.toCFG :=
  .ofSynth AmbigCFG.synthCodeFromPCP ambCode_prim.to_comp

/-- **Ambiguity of grammar codes is halting-hard**, over the terminals `α ⊕ ℕ` for any alphabet `α`
with two distinct letters: `PCP.fromHaltOver`, then `codeFromPCP`. -/
def codeFromHaltOver (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction fun c : CFGCode (α ⊕ ℕ) => AmbigCFG.DecisionProblem c.toCFG := by
  haveI : Nonempty α := ⟨b0⟩
  reduce_from (PCP.fromHaltOver b0 b1 hne) via AmbigCFG.synthCodeFromPCP

end DiagonaLean.AmbigCFG
