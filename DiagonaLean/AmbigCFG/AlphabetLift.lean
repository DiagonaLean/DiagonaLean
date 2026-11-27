/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.AmbigCFG.Encode
import DiagonaLean.AmbigCFG.Reductions.PCP_to_AmbigCFGCode
import DiagonaLean.Foundations.Codes.Tactic

@[expose] public section

/-! # Ambiguity of grammar codes over every alphabet with two letters

Encoding the terminals of a grammar by a code keeps and reflects ambiguity
(`decisionProblem_grammarEncode_iff`), so on grammar codes ambiguity is a functor on codes
(`ambCodeFunctor`), and the lifting of `Foundations.Codes.Functor` moves the results over the
terminals `Bool ⊕ ℕ` (through `ambCode`) to grammar codes over any alphabet with two distinct
letters: the classical statement, with a finite terminal alphabet. The lifted results are
`AmbigCFG.synthCodeFromHaltOver` (`SynthHardness.lean`) and `AmbigCFG.codeFromHaltOver`
(`Undecidable.lean`).

## Main statements

* `ambCodeFunctor`, `codeProblemReduces`, `codeProblemReduces'`.
* `ambigCFGCode_manyOneEquiv`: many-one equivalent over any two such alphabets.
-/

namespace DiagonaLean.AmbigCFG.AlphabetLift

open DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Codes
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions

variable {T α : Type}

open Classical in
/-- Ambiguity of a grammar code, with classical decidable equality of terminals, so that it is
defined over every alphabet (the grammar does not depend on the instance, `codeProblem_iff`). -/
def CodeProblem (p : CFGCode T) : Prop := AmbigCFG.DecisionProblem p.toCFG

theorem codeProblem_iff [DecidableEq T] (p : CFGCode T) :
    CodeProblem p ↔ AmbigCFG.DecisionProblem p.toCFG := by
  unfold CodeProblem
  convert Iff.rfl

theorem codeProblem_eq [DecidableEq T] :
    @CodeProblem T = fun p => AmbigCFG.DecisionProblem p.toCFG :=
  funext fun p => propext (codeProblem_iff p)

/-- **Ambiguity of grammar codes, as a functor on codes.** -/
abbrev ambCodeFunctor : CodeFunctor IsCode where
  Inst T := CFGCode T
  map c p := presEncode c p
  Prob p := CodeProblem p
  map_unit p := presEncode_unit p
  map_kcomp c₁ c₂ p := presEncode_kcomp c₁ c₂ p
  natural {T β} c hc p := by
    classical
    rw [codeProblem_iff, codeProblem_iff, toCFG_presEncode hc]
    exact decisionProblem_grammarEncode_iff hc
  supp := presTerminals
  map_congr _ h := presEncode_congr h

/-- The two forms of the problem reduce to each other by the identity. -/
def codeProblemReduces [DecidableEq T] :
    (fun p : CFGCode T => AmbigCFG.DecisionProblem p.toCFG) ⪯_s @CodeProblem T :=
  ⟨id, fun p => (codeProblem_iff p).symm⟩

/-- The two forms of the problem reduce to each other by the identity. -/
def codeProblemReduces' [DecidableEq T] :
    @CodeProblem T ⪯_s fun p : CFGCode T => AmbigCFG.DecisionProblem p.toCFG :=
  ⟨id, fun p => codeProblem_iff p⟩

/-- **Alphabet invariance of ambiguity on grammar codes**: over any two nontrivial `Primcodable`
alphabets, ambiguity of grammar codes is many-one equivalent. -/
theorem ambigCFGCode_manyOneEquiv {β : Type} [Primcodable α] [Primcodable β] [Nontrivial α]
    [Nontrivial β] [DecidableEq α] [DecidableEq β] :
    ManyOneEquiv (fun c : CFGCode α => AmbigCFG.DecisionProblem c.toCFG)
      fun c : CFGCode β => AmbigCFG.DecisionProblem c.toCFG := by
  have h : ManyOneEquiv (@CodeProblem α) (@CodeProblem β) := by code_lift ambCodeFunctor
  rwa [codeProblem_eq, codeProblem_eq] at h

end DiagonaLean.AmbigCFG.AlphabetLift
